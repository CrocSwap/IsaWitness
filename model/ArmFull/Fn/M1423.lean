import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0850
import ArmFull.Fn.M1096
import ArmFull.Fn.M1097
import ArmFull.Fn.M1291
import ArmFull.Fn.M1292
import ArmFull.Fn.M1293
import ArmFull.Fn.M1335
import ArmFull.Fn.M1336

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
def __DecodeA64_SVE__seg28 (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__2281 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10000100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
             __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
    then
      (do
        let w__2280 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__2280 <b 2177) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2281 : Bool)
  then
    (do
      writeReg SEE 2177
      let msz := (BitVec.slice __opcode 23 2)
      let Rm := (BitVec.slice __opcode 16 5)
      let U := (BitVec.slice __opcode 13 1)
      let Pg := (BitVec.slice __opcode 10 3)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zt := (BitVec.slice __opcode 0 5)
      (decode_LDNT1SH_Z_P_AR_S_x32_unscaled msz Rm U Pg Zn Zt))
  else
    (do
      let w__2283 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
        then
          (do
            let w__2282 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2282 <b 2178) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2283 : Bool)
      then
        (do
          writeReg SEE 2178
          let msz := (BitVec.slice __opcode 23 2)
          let Rm := (BitVec.slice __opcode 16 5)
          let U := (BitVec.slice __opcode 14 1)
          let Pg := (BitVec.slice __opcode 10 3)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zt := (BitVec.slice __opcode 0 5)
          (decode_LDNT1B_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
      else
        (do
          let w__2285 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
            then
              (do
                let w__2284 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__2284 <b 2179) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__2285 : Bool)
          then
            (do
              writeReg SEE 2179
              let msz := (BitVec.slice __opcode 23 2)
              let Rm := (BitVec.slice __opcode 16 5)
              let U := (BitVec.slice __opcode 14 1)
              let Pg := (BitVec.slice __opcode 10 3)
              let Zn := (BitVec.slice __opcode 5 5)
              let Zt := (BitVec.slice __opcode 0 5)
              (decode_LDNT1H_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
          else
            (do
              let w__2287 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000101000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                then
                  (do
                    let w__2286 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__2286 <b 2180) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__2287 : Bool)
              then
                (do
                  writeReg SEE 2180
                  let msz := (BitVec.slice __opcode 23 2)
                  let Rm := (BitVec.slice __opcode 16 5)
                  let U := (BitVec.slice __opcode 14 1)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Zt := (BitVec.slice __opcode 0 5)
                  (decode_LDNT1W_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
              else
                (do
                  let w__2289 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000101100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                    then
                      (do
                        let w__2288 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__2288 <b 2181) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__2289 : Bool)
                  then
                    (do
                      writeReg SEE 2181
                      let msz := (BitVec.slice __opcode 23 2)
                      let Rm := (BitVec.slice __opcode 16 5)
                      let U := (BitVec.slice __opcode 14 1)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Zt := (BitVec.slice __opcode 0 5)
                      (decode_LDNT1D_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                  else
                    (do
                      let w__2291 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b11000100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                        then
                          (do
                            let w__2290 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__2290 <b 2182) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__2291 : Bool)
                      then
                        (do
                          writeReg SEE 2182
                          let msz := (BitVec.slice __opcode 23 2)
                          let Rm := (BitVec.slice __opcode 16 5)
                          let U := (BitVec.slice __opcode 14 1)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Zt := (BitVec.slice __opcode 0 5)
                          (decode_LDNT1SB_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                      else
                        (do
                          let w__2293 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode
                                     31 21)) == (0b11000100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                            then
                              (do
                                let w__2292 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__2292 <b 2183) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__2293 : Bool)
                          then
                            (do
                              writeReg SEE 2183
                              let msz := (BitVec.slice __opcode 23 2)
                              let Rm := (BitVec.slice __opcode 16 5)
                              let U := (BitVec.slice __opcode 14 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let Zt := (BitVec.slice __opcode 0 5)
                              (decode_LDNT1SH_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                          else
                            (do
                              let w__2295 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11000101000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__2294 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__2294 <b 2184) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__2295 : Bool)
                              then
                                (do
                                  writeReg SEE 2184
                                  let msz := (BitVec.slice __opcode 23 2)
                                  let Rm := (BitVec.slice __opcode 16 5)
                                  let U := (BitVec.slice __opcode 14 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let Zt := (BitVec.slice __opcode 0 5)
                                  (decode_LDNT1SW_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                              else
                                (do
                                  let w__2297 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b11100100010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__2296 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__2296 <b 2185) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__2297 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2185
                                      let msz := (BitVec.slice __opcode 23 2)
                                      let Rm := (BitVec.slice __opcode 16 5)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zt := (BitVec.slice __opcode 0 5)
                                      (decode_STNT1B_Z_P_AR_S_x32_unscaled msz Rm Pg Zn Zt))
                                  else
                                    (do
                                      let w__2299 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b11100100110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__2298 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__2298 <b 2186) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__2299 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2186
                                          let msz := (BitVec.slice __opcode 23 2)
                                          let Rm := (BitVec.slice __opcode 16 5)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zt := (BitVec.slice __opcode 0 5)
                                          (decode_STNT1H_Z_P_AR_S_x32_unscaled msz Rm Pg Zn Zt))
                                      else
                                        (do
                                          let w__2301 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b11100101010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__2300 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__2300 <b 2187) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__2301 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2187
                                              let msz := (BitVec.slice __opcode 23 2)
                                              let Rm := (BitVec.slice __opcode 16 5)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zt := (BitVec.slice __opcode 0 5)
                                              (decode_STNT1W_Z_P_AR_S_x32_unscaled msz Rm Pg Zn Zt))
                                          else
                                            (do
                                              let w__2303 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                         __opcode 31 21)) == (0b11100100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__2302 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__2302 <b 2188) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__2303 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2188
                                                  let msz := (BitVec.slice __opcode 23 2)
                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                  (decode_STNT1B_Z_P_AR_D_64_unscaled msz Rm Pg Zn
                                                    Zt))
                                              else
                                                (do
                                                  let w__2305 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b11100100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__2304 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__2304 <b 2189) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__2305 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2189
                                                      let msz := (BitVec.slice __opcode 23 2)
                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                      (decode_STNT1H_Z_P_AR_D_64_unscaled msz Rm Pg
                                                        Zn Zt))
                                                  else
                                                    (do
                                                      let w__2307 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b11100101000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__2306 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__2306 <b 2190) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__2307 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2190
                                                          let msz := (BitVec.slice __opcode 23 2)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                          (decode_STNT1W_Z_P_AR_D_64_unscaled msz Rm
                                                            Pg Zn Zt))
                                                      else
                                                        (do
                                                          let w__2309 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b11100101100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__2308 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__2308 <b 2191) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__2309 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2191
                                                              let msz :=
                                                                (BitVec.slice __opcode 23 2)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                              (decode_STNT1D_Z_P_AR_D_64_unscaled
                                                                msz Rm Pg Zn Zt))
                                                          else
                                                            (do
                                                              let w__2311 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b11000100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__2310 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__2310 <b 2192) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__2311 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2192
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_LD1Q_Z_P_AR_D_64_unscaled
                                                                    Rm Pg Zn Zt))
                                                              else
                                                                (do
                                                                  let w__2313 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                             __opcode 31 21)) == (0b11100100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                             __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__2312 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__2312 <b 2193) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__2313 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2193
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_ST1Q_Z_P_AR_D_64_unscaled
                                                                        Rm Pg Zn Zt))
                                                                  else
                                                                    (do
                                                                      let w__2315 ← (( do
                                                                        if ((((Sail.BitVec.castWidth (m := 21) (Sail.BitVec.extractLsb
                                                                               __opcode 31 11)) == (0b000001001011111101011#21 : (BitVec 21))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__2314 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__2314 <b 2727) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__2315 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2727
                                                                          let imm6 :=
                                                                            (BitVec.slice __opcode 5
                                                                              6)
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_RDSVL_R_I__ imm6
                                                                            Rd))
                                                                      else
                                                                        (do
                                                                          let w__2317 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b00000100011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 11)) == (0b01011#5 : (BitVec 5)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__2316 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__2316 <b 2728) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__2317 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2728
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let imm6 :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 6)
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_ADDSPL_R_RI__
                                                                                Rn imm6 Rd))
                                                                          else
                                                                            (do
                                                                              let w__2319 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b00000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         11)) == (0b01011#5 : (BitVec 5)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__2318 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__2318 <b 2729) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__2319 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2729
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let imm6 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 6)
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_ADDSVL_R_RI__
                                                                                    Rn imm6 Rd))
                                                                              else
                                                                                sailThrow ((Error_Undefined
                                                                                  ())))))))))))))))))))))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_LoadStore__seg0 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
               __opcode 29 23)) == (0b0010001#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                 __opcode 14 10)) == (0b11111#5 : (BitVec 5)))))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 113) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 113
      let Rt := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let o0 := (BitVec.slice __opcode 15 1)
      let Rs := (BitVec.slice __opcode 16 5)
      let L := (BitVec.slice __opcode 22 1)
      let size := (BitVec.slice __opcode 30 2)
      (decode_cas_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L size)
      (pure false))
  else
    (do
      let w__3 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b000010001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                   __opcode 14 10)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2 <b 114) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          writeReg SEE 114
          let Rt := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let o0 := (BitVec.slice __opcode 15 1)
          let Rs := (BitVec.slice __opcode 16 5)
          let L := (BitVec.slice __opcode 22 1)
          let size := (BitVec.slice __opcode 30 2)
          (decode_casb_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L size)
          (pure false))
      else
        (do
          let w__5 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b010010001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                       __opcode 14 10)) == (0b11111#5 : (BitVec 5))))) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__4 <b 115) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              writeReg SEE 115
              let Rt := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let o0 := (BitVec.slice __opcode 15 1)
              let Rs := (BitVec.slice __opcode 16 5)
              let L := (BitVec.slice __opcode 22 1)
              let size := (BitVec.slice __opcode 30 2)
              (decode_cash_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L size)
              (pure false))
          else
            (do
              let w__7 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                           __opcode 29 23)) == (0b0010000#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                             __opcode 14 10)) == (0b11111#5 : (BitVec 5)))))) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 116) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  writeReg SEE 116
                  let Rt := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Rt2 := (BitVec.slice __opcode 10 5)
                  let o0 := (BitVec.slice __opcode 15 1)
                  let Rs := (BitVec.slice __opcode 16 5)
                  let L := (BitVec.slice __opcode 22 1)
                  let sz := (BitVec.slice __opcode 30 1)
                  (decode_casp_aarch64_instrs_memory_atomicops_cas_pair Rt Rn Rt2 o0 Rs L sz)
                  (pure false))
              else
                (do
                  let w__9 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 15 10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 153) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      writeReg SEE 153
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let op2 := (BitVec.slice __opcode 12 4)
                      let Rs := (BitVec.slice __opcode 16 5)
                      let op1 := (BitVec.slice __opcode 22 2)
                      let sz := (BitVec.slice __opcode 30 2)
                      (decode_cpyp_aarch64_instrs_memory_mcpymset_cpy Rd Rn op2 Rs op1 sz)
                      (pure false))
                  else
                    (do
                      let w__11 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb __opcode 29
                                 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                   __opcode 15 10)) == (0b110001#6 : (BitVec 6))))) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__10 <b 154) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          writeReg SEE 154
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let op2 := (BitVec.slice __opcode 12 4)
                          let Rs := (BitVec.slice __opcode 16 5)
                          let op1 := (BitVec.slice __opcode 22 2)
                          let sz := (BitVec.slice __opcode 30 2)
                          (decode_cpypn_aarch64_instrs_memory_mcpymset_cpy Rd Rn op2 Rs op1 sz)
                          (pure false))
                      else
                        (do
                          let w__13 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb __opcode
                                     29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                       __opcode 15 10)) == (0b100001#6 : (BitVec 6))))) : Bool) : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__12 <b 155) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__13 : Bool)
                          then
                            (do
                              writeReg SEE 155
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let op2 := (BitVec.slice __opcode 12 4)
                              let Rs := (BitVec.slice __opcode 16 5)
                              let op1 := (BitVec.slice __opcode 22 2)
                              let sz := (BitVec.slice __opcode 30 2)
                              (decode_cpyprn_aarch64_instrs_memory_mcpymset_cpy Rd Rn op2 Rs op1 sz)
                              (pure false))
                          else
                            (do
                              let w__15 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                         __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                           __opcode 15 10)) == (0b001001#6 : (BitVec 6))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__14 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__14 <b 156) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__15 : Bool)
                              then
                                (do
                                  writeReg SEE 156
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let op2 := (BitVec.slice __opcode 12 4)
                                  let Rs := (BitVec.slice __opcode 16 5)
                                  let op1 := (BitVec.slice __opcode 22 2)
                                  let sz := (BitVec.slice __opcode 30 2)
                                  (decode_cpyprt_aarch64_instrs_memory_mcpymset_cpy Rd Rn op2 Rs op1
                                    sz)
                                  (pure false))
                              else
                                (do
                                  let w__17 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                             __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                               __opcode 15 10)) == (0b111001#6 : (BitVec 6))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__16 <b 157) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      writeReg SEE 157
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let op2 := (BitVec.slice __opcode 12 4)
                                      let Rs := (BitVec.slice __opcode 16 5)
                                      let op1 := (BitVec.slice __opcode 22 2)
                                      let sz := (BitVec.slice __opcode 30 2)
                                      (decode_cpyprtn_aarch64_instrs_memory_mcpymset_cpy Rd Rn op2
                                        Rs op1 sz)
                                      (pure false))
                                  else
                                    (do
                                      let w__19 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                 __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 15 10)) == (0b101001#6 : (BitVec 6))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__18 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__18 <b 158) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__19 : Bool)
                                      then
                                        (do
                                          writeReg SEE 158
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let op2 := (BitVec.slice __opcode 12 4)
                                          let Rs := (BitVec.slice __opcode 16 5)
                                          let op1 := (BitVec.slice __opcode 22 2)
                                          let sz := (BitVec.slice __opcode 30 2)
                                          (decode_cpyprtrn_aarch64_instrs_memory_mcpymset_cpy Rd Rn
                                            op2 Rs op1 sz)
                                          (pure false))
                                      else
                                        (do
                                          let w__21 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                     __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                       __opcode 15 10)) == (0b011001#6 : (BitVec 6))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__20 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__20 <b 159) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__21 : Bool)
                                          then
                                            (do
                                              writeReg SEE 159
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let op2 := (BitVec.slice __opcode 12 4)
                                              let Rs := (BitVec.slice __opcode 16 5)
                                              let op1 := (BitVec.slice __opcode 22 2)
                                              let sz := (BitVec.slice __opcode 30 2)
                                              (decode_cpyprtwn_aarch64_instrs_memory_mcpymset_cpy Rd
                                                Rn op2 Rs op1 sz)
                                              (pure false))
                                          else
                                            (do
                                              let w__23 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                         __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 15 10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__22 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__22 <b 160) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__23 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 160
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let op2 := (BitVec.slice __opcode 12 4)
                                                  let Rs := (BitVec.slice __opcode 16 5)
                                                  let op1 := (BitVec.slice __opcode 22 2)
                                                  let sz := (BitVec.slice __opcode 30 2)
                                                  (decode_cpypt_aarch64_instrs_memory_mcpymset_cpy
                                                    Rd Rn op2 Rs op1 sz)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__25 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                             __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b111101#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__24 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__24 <b 161) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__25 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 161
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let op2 := (BitVec.slice __opcode 12 4)
                                                      let Rs := (BitVec.slice __opcode 16 5)
                                                      let op1 := (BitVec.slice __opcode 22 2)
                                                      let sz := (BitVec.slice __opcode 30 2)
                                                      (decode_cpyptn_aarch64_instrs_memory_mcpymset_cpy
                                                        Rd Rn op2 Rs op1 sz)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__27 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                 __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b101101#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__26 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__26 <b 162) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__27 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 162
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let op2 := (BitVec.slice __opcode 12 4)
                                                          let Rs := (BitVec.slice __opcode 16 5)
                                                          let op1 := (BitVec.slice __opcode 22 2)
                                                          let sz := (BitVec.slice __opcode 30 2)
                                                          (decode_cpyptrn_aarch64_instrs_memory_mcpymset_cpy
                                                            Rd Rn op2 Rs op1 sz)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__29 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 15 10)) == (0b011101#6 : (BitVec 6))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__28 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__28 <b 163) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__29 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 163
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let op2 :=
                                                                (BitVec.slice __opcode 12 4)
                                                              let Rs := (BitVec.slice __opcode 16 5)
                                                              let op1 :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let sz := (BitVec.slice __opcode 30 2)
                                                              (decode_cpyptwn_aarch64_instrs_memory_mcpymset_cpy
                                                                Rd Rn op2 Rs op1 sz)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__31 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                         __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 15 10)) == (0b010001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__30 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__30 <b 164) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__31 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 164
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let op2 :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let Rs :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let op1 :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let sz :=
                                                                    (BitVec.slice __opcode 30 2)
                                                                  (decode_cpypwn_aarch64_instrs_memory_mcpymset_cpy
                                                                    Rd Rn op2 Rs op1 sz)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__33 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                               __opcode 15 10)) == (0b000101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__32 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__32 <b 165) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__33 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 165
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let op2 :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let Rs :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let op1 :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let sz :=
                                                                        (BitVec.slice __opcode 30 2)
                                                                      (decode_cpypwt_aarch64_instrs_memory_mcpymset_cpy
                                                                        Rd Rn op2 Rs op1 sz)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__35 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 10)) == (0b110101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__34 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__34 <b 166) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__35 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 166
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let op2 :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let Rs :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let op1 :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              30 2)
                                                                          (decode_cpypwtn_aarch64_instrs_memory_mcpymset_cpy
                                                                            Rd Rn op2 Rs op1 sz)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__37 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 29 24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       10)) == (0b100101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__36 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__36 <b 167) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__37 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 167
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let op2 :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let Rs :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let op1 :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let sz :=
                                                                                (BitVec.slice
                                                                                  __opcode 30 2)
                                                                              (decode_cpypwtrn_aarch64_instrs_memory_mcpymset_cpy
                                                                                Rd Rn op2 Rs op1 sz)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__39 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 29
                                                                                         24)) == (0b011101#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 10)) == (0b010101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__38 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__38 <b 168) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__39 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 168
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let op2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let Rs :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let op1 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let sz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 2)
                                                                                  (decode_cpypwtwn_aarch64_instrs_memory_mcpymset_cpy
                                                                                    Rd Rn op2 Rs op1
                                                                                    sz)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__41 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             29 24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__40 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__40 <b 169) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__41 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 169
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let op2 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let Rs :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let op1 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let sz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 2)
                                                                                      (decode_cpyfp_aarch64_instrs_memory_mcpymset_cpyf
                                                                                        Rd Rn op2 Rs
                                                                                        op1 sz)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__43 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 29
                                                                                                 24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   10)) == (0b110001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__42 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__42 <b 170) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__43 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 170
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let op2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let Rs :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let op1 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let sz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 2)
                                                                                          (decode_cpyfpn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                            Rd Rn
                                                                                            op2 Rs
                                                                                            op1 sz)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__45 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     29
                                                                                                     24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       10)) == (0b100001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__44 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__44 <b 171) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__45 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 171
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
                                                                                              let op2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let Rs :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let op1 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let sz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  30
                                                                                                  2)
                                                                                              (decode_cpyfprn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                Rd
                                                                                                Rn
                                                                                                op2
                                                                                                Rs
                                                                                                op1
                                                                                                sz)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__47 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         29
                                                                                                         24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           10)) == (0b001001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__46 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__46 <b 172) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__47 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 172
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
                                                                                                  let op2 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let Rs :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let op1 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
                                                                                                  let sz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      30
                                                                                                      2)
                                                                                                  (decode_cpyfprt_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    op2
                                                                                                    Rs
                                                                                                    op1
                                                                                                    sz)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__49 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             29
                                                                                                             24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               10)) == (0b111001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__48 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__48 <b 173) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__49 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 173
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
                                                                                                      let op2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let Rs :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let op1 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let sz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          30
                                                                                                          2)
                                                                                                      (decode_cpyfprtn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        op2
                                                                                                        Rs
                                                                                                        op1
                                                                                                        sz)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__51 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 29
                                                                                                                 24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   10)) == (0b101001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__50 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__50 <b 174) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__51 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 174
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
                                                                                                          let op2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let Rs :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let op1 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
                                                                                                          let sz :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              30
                                                                                                              2)
                                                                                                          (decode_cpyfprtrn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            op2
                                                                                                            Rs
                                                                                                            op1
                                                                                                            sz)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__53 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     29
                                                                                                                     24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       10)) == (0b011001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__52 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__52 <b 175) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__53 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 175
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
                                                                                                              let op2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let Rs :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let op1 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let sz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  30
                                                                                                                  2)
                                                                                                              (decode_cpyfprtwn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                op2
                                                                                                                Rs
                                                                                                                op1
                                                                                                                sz)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__55 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         29
                                                                                                                         24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           10)) == (0b001101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__54 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__54 <b 176) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__55 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 176
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
                                                                                                                  let op2 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let Rs :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let op1 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let sz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      30
                                                                                                                      2)
                                                                                                                  (decode_cpyfpt_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    op2
                                                                                                                    Rs
                                                                                                                    op1
                                                                                                                    sz)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__57 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             29
                                                                                                                             24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               10)) == (0b111101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__56 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__56 <b 177) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__57 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 177
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
                                                                                                                      let op2 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      let Rs :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let op1 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let sz :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          30
                                                                                                                          2)
                                                                                                                      (decode_cpyfptn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        op2
                                                                                                                        Rs
                                                                                                                        op1
                                                                                                                        sz)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__59 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 29
                                                                                                                                 24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   10)) == (0b101101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__58 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__58 <b 178) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__59 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 178
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
                                                                                                                          let op2 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let Rs :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let op1 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let sz :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              30
                                                                                                                              2)
                                                                                                                          (decode_cpyfptrn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            op2
                                                                                                                            Rs
                                                                                                                            op1
                                                                                                                            sz)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__61 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     29
                                                                                                                                     24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       10)) == (0b011101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__60 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__60 <b 179) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__61 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 179
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
                                                                                                                              let op2 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let Rs :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let op1 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let sz :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  30
                                                                                                                                  2)
                                                                                                                              (decode_cpyfptwn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                op2
                                                                                                                                Rs
                                                                                                                                op1
                                                                                                                                sz)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__63 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         29
                                                                                                                                         24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           10)) == (0b010001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__62 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__62 <b 180) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__63 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 180
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
                                                                                                                                  let op2 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      4)
                                                                                                                                  let Rs :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let op1 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let sz :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      30
                                                                                                                                      2)
                                                                                                                                  (decode_cpyfpwn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    op2
                                                                                                                                    Rs
                                                                                                                                    op1
                                                                                                                                    sz)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__65 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             29
                                                                                                                                             24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               10)) == (0b000101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__64 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__64 <b 181) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__65 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 181
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
                                                                                                                                      let op2 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          4)
                                                                                                                                      let Rs :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let op1 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let sz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          30
                                                                                                                                          2)
                                                                                                                                      (decode_cpyfpwt_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        op2
                                                                                                                                        Rs
                                                                                                                                        op1
                                                                                                                                        sz)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__67 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 29
                                                                                                                                                 24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   21
                                                                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   10)) == (0b110101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__66 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__66 <b 182) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__67 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 182
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
                                                                                                                                          let op2 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              12
                                                                                                                                              4)
                                                                                                                                          let Rs :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let op1 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let sz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              30
                                                                                                                                              2)
                                                                                                                                          (decode_cpyfpwtn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            op2
                                                                                                                                            Rs
                                                                                                                                            op1
                                                                                                                                            sz)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__69 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     29
                                                                                                                                                     24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       10)) == (0b100101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__68 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__68 <b 183) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__69 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 183
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
                                                                                                                                              let op2 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  12
                                                                                                                                                  4)
                                                                                                                                              let Rs :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
                                                                                                                                              let op1 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let sz :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  30
                                                                                                                                                  2)
                                                                                                                                              (decode_cpyfpwtrn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                op2
                                                                                                                                                Rs
                                                                                                                                                op1
                                                                                                                                                sz)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__71 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         29
                                                                                                                                                         24)) == (0b011001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           10)) == (0b010101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__70 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__70 <b 184) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__71 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 184
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
                                                                                                                                                  let op2 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      12
                                                                                                                                                      4)
                                                                                                                                                  let Rs :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let op1 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  let sz :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      30
                                                                                                                                                      2)
                                                                                                                                                  (decode_cpyfpwtwn_aarch64_instrs_memory_mcpymset_cpyf
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    op2
                                                                                                                                                    Rs
                                                                                                                                                    op1
                                                                                                                                                    sz)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
