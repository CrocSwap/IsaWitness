import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0232
import ArmFull.Fn.M0233
import ArmFull.Fn.M1283
import ArmFull.Fn.M1284
import ArmFull.Fn.M1468

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
def __DecodeT32__seg3 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__250 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 7 4)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
    then
      (do
        let w__249 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__249 <b 3133) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__250 : Bool)
  then
    (do
      writeReg SEE 3133
      let Rn := (BitVec.slice __opcode 16 4)
      let Rd := (BitVec.slice __opcode 8 4)
      let Rm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_SHADD8_T1enc_A_txt Rn Rd Rm)
      (pure false))
  else
    (do
      let w__252 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFAA#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 7 4)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
        then
          (do
            let w__251 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__251 <b 3135) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__252 : Bool)
      then
        (do
          writeReg SEE 3135
          let Rn := (BitVec.slice __opcode 16 4)
          let Rd := (BitVec.slice __opcode 8 4)
          let Rm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_SHASX_T1enc_A_txt Rn Rd Rm)
          (pure false))
      else
        (do
          let w__254 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFAE#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 7 4)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
            then
              (do
                let w__253 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__253 <b 3137) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__254 : Bool)
          then
            (do
              writeReg SEE 3137
              let Rn := (BitVec.slice __opcode 16 4)
              let Rd := (BitVec.slice __opcode 8 4)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_SHSAX_T1enc_A_txt Rn Rd Rm)
              (pure false))
          else
            (do
              let w__256 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFAD#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 7 4)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                then
                  (do
                    let w__255 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__255 <b 3139) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__256 : Bool)
              then
                (do
                  writeReg SEE 3139
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rd := (BitVec.slice __opcode 8 4)
                  let Rm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_SHSUB16_T1enc_A_txt Rn Rd Rm)
                  (pure false))
              else
                (do
                  let w__258 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFAC#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 7 4)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                    then
                      (do
                        let w__257 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__257 <b 3141) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__258 : Bool)
                  then
                    (do
                      writeReg SEE 3141
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Rd := (BitVec.slice __opcode 8 4)
                      let Rm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_SHSUB8_T1enc_A_txt Rn Rd Rm)
                      (pure false))
                  else
                    (do
                      let w__260 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0xFB1#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 __opcode 7 6)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                        then
                          (do
                            let w__259 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__259 <b 3143) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__260 : Bool)
                      then
                        (do
                          writeReg SEE 3143
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Ra := (BitVec.slice __opcode 12 4)
                          let Rd := (BitVec.slice __opcode 8 4)
                          let N := (BitVec.slice __opcode 5 1)
                          let M := (BitVec.slice __opcode 4 1)
                          let Rm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_SMLABB_T1enc_A_txt Rn Ra Rd N M Rm)
                          (pure false))
                      else
                        (do
                          let w__262 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xFB2#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 7 5)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                            then
                              (do
                                let w__261 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__261 <b 3145) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__262 : Bool)
                          then
                            (do
                              writeReg SEE 3145
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Ra := (BitVec.slice __opcode 12 4)
                              let Rd := (BitVec.slice __opcode 8 4)
                              let M := (BitVec.slice __opcode 4 1)
                              let Rm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_SMLAD_T1enc_A_txt Rn Ra Rd M Rm)
                              (pure false))
                          else
                            (do
                              let w__264 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 31 20)) == (0xFBC#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                         __opcode 7 4)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__263 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__263 <b 3147) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__264 : Bool)
                              then
                                (do
                                  writeReg SEE 3147
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let RdLo := (BitVec.slice __opcode 12 4)
                                  let RdHi := (BitVec.slice __opcode 8 4)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_SMLAL_T1enc_A_txt Rn RdLo RdHi Rm)
                                  (pure false))
                              else
                                (do
                                  let w__266 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0xFBC#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 7 6)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__265 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__265 <b 3149) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__266 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3149
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let RdLo := (BitVec.slice __opcode 12 4)
                                      let RdHi := (BitVec.slice __opcode 8 4)
                                      let N := (BitVec.slice __opcode 5 1)
                                      let M := (BitVec.slice __opcode 4 1)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_SMLALBB_T1enc_A_txt Rn RdLo RdHi N M Rm)
                                      (pure false))
                                  else
                                    (do
                                      let w__268 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0xFBC#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 7 5)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__267 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__267 <b 3151) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__268 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3151
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let RdLo := (BitVec.slice __opcode 12 4)
                                          let RdHi := (BitVec.slice __opcode 8 4)
                                          let M := (BitVec.slice __opcode 4 1)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_SMLALD_T1enc_A_txt Rn RdLo RdHi M
                                            Rm)
                                          (pure false))
                                      else
                                        (do
                                          let w__270 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0xFB3#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 7 5)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__269 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__269 <b 3153) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__270 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3153
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let Ra := (BitVec.slice __opcode 12 4)
                                              let Rd := (BitVec.slice __opcode 8 4)
                                              let M := (BitVec.slice __opcode 4 1)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_SMLAWB_T1enc_A_txt Rn Ra Rd M
                                                Rm)
                                              (pure false))
                                          else
                                            (do
                                              let w__272 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0xFB4#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 7 5)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__271 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__271 <b 3155) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__272 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3155
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let Ra := (BitVec.slice __opcode 12 4)
                                                  let Rd := (BitVec.slice __opcode 8 4)
                                                  let M := (BitVec.slice __opcode 4 1)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_SMLSD_T1enc_A_txt Rn Ra Rd
                                                    M Rm)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__274 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xFBD#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 7 5)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__273 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__273 <b 3157) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__274 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3157
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let RdLo := (BitVec.slice __opcode 12 4)
                                                      let RdHi := (BitVec.slice __opcode 8 4)
                                                      let M := (BitVec.slice __opcode 4 1)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_SMLSLD_T1enc_A_txt Rn
                                                        RdLo RdHi M Rm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__276 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xFB5#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 7 5)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__275 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__275 <b 3159) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__276 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3159
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Ra := (BitVec.slice __opcode 12 4)
                                                          let Rd := (BitVec.slice __opcode 8 4)
                                                          let R := (BitVec.slice __opcode 4 1)
                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_SMMLA_T1enc_A_txt
                                                            Rn Ra Rd R Rm)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__278 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xFB6#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 7 5)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__277 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__277 <b 3161) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__278 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3161
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Ra := (BitVec.slice __opcode 12 4)
                                                              let Rd := (BitVec.slice __opcode 8 4)
                                                              let R := (BitVec.slice __opcode 4 1)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_SMMLS_T1enc_A_txt
                                                                Rn Ra Rd R Rm)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__280 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0xFB5#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                           __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 7 5)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__279 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__279 <b 3163) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__280 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3163
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 8 4)
                                                                  let R :=
                                                                    (BitVec.slice __opcode 4 1)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_SMMUL_T1enc_A_txt
                                                                    Rn Rd R Rm)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__282 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xFB2#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                               __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 7 5)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__281 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__281 <b 3165) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__282 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3165
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 8 4)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 4 1)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_SMUAD_T1enc_A_txt
                                                                        Rn Rd M Rm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__284 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xFB1#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 7 6)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__283 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__283 <b 3167) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__284 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3167
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 8
                                                                              4)
                                                                          let N :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          let M :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_SMULBB_T1enc_A_txt
                                                                            Rn Rd N M Rm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__286 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xFB8#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 7 4)) == (0x0#4 : (BitVec 4)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__285 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__285 <b 3169) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__286 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3169
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let RdLo :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let RdHi :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 4)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_SMULL_T1enc_A_txt
                                                                                Rn RdLo RdHi Rm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__288 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xFB3#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           7 5)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__287 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__287 <b 3171) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__288 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3171
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 4)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 1)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_SMULWB_T1enc_A_txt
                                                                                    Rn Rd M Rm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__290 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xFB4#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               7 5)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__289 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__289 <b 3173) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__290 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3173
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 8
                                                                                          4)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          1)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_SMUSD_T1enc_A_txt
                                                                                        Rn Rd M Rm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__292 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xF32#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   12)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   7
                                                                                                   4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__291 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__291 <b 3175) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__292 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3175
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 4)
                                                                                          let sat_imm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       26)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       4)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     5)])) != 0#1)) : Bool)
                                                                                          then
                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                              ()))
                                                                                          else
                                                                                            (do
                                                                                              (decode_aarch32_instrs_SSAT16_T1enc_A_txt
                                                                                                Rn
                                                                                                Rd
                                                                                                sat_imm))
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__294 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     22)) == (0b1111001100#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       20
                                                                                                       20)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         5
                                                                                                         5)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__293 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__293 <b 3177) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__294 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3177
                                                                                              let sh :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  21
                                                                                                  1)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let imm3 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  3)
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  4)
                                                                                              let imm2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  6
                                                                                                  2)
                                                                                              let sat_imm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         26)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         5)])) != 0#1)) : Bool)
                                                                                              then
                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                  ()))
                                                                                              else
                                                                                                (do
                                                                                                  (decode_aarch32_instrs_SSAT_T1enc_A_txt
                                                                                                    sh
                                                                                                    Rn
                                                                                                    imm3
                                                                                                    Rd
                                                                                                    imm2
                                                                                                    sat_imm))
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__296 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xFAE#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           7
                                                                                                           4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__295 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__295 <b 3179) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__296 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3179
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Rd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      4)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_SSAX_T1enc_A_txt
                                                                                                    Rn
                                                                                                    Rd
                                                                                                    Rm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__298 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xFAD#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               7
                                                                                                               4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__297 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__297 <b 3181) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__298 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3181
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Rd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          8
                                                                                                          4)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_SSUB16_T1enc_A_txt
                                                                                                        Rn
                                                                                                        Rd
                                                                                                        Rm)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__300 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xFAC#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   7
                                                                                                                   4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__299 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__299 <b 3183) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__300 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3183
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Rd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              4)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_SSUB8_T1enc_A_txt
                                                                                                            Rn
                                                                                                            Rd
                                                                                                            Rm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__302 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     25)) == (0b1110110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       22
                                                                                                                       22)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         20
                                                                                                                         20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         8)) == (0x5E#8 : (BitVec 8)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__301 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__301 <b 3185) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__302 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3185
                                                                                                              let P :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  24
                                                                                                                  1)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  23
                                                                                                                  1)
                                                                                                              let W :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  21
                                                                                                                  1)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let imm8 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  8)
                                                                                                              (decode_aarch32_instrs_STC_T1enc_A_txt
                                                                                                                P
                                                                                                                U
                                                                                                                W
                                                                                                                Rn
                                                                                                                imm8)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__304 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         22)) == (0b1110100010#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         20
                                                                                                                         20)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__303 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__303 <b 3188) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__304 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3188
                                                                                                                  let W :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      21
                                                                                                                      1)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let P :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      15
                                                                                                                      1)
                                                                                                                  let M :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      14
                                                                                                                      1)
                                                                                                                  let register_list :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      14)
                                                                                                                  (decode_aarch32_instrs_STM_T2enc_A_txt
                                                                                                                    W
                                                                                                                    Rn
                                                                                                                    P
                                                                                                                    M
                                                                                                                    register_list)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__306 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             22)) == (0b1110100100#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             20
                                                                                                                             20)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__305 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__305 <b 3191) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__306 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3191
                                                                                                                      let W :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          21
                                                                                                                          1)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let P :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          15
                                                                                                                          1)
                                                                                                                      let M :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          14
                                                                                                                          1)
                                                                                                                      let register_list :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          14)
                                                                                                                      (decode_aarch32_instrs_STMDB_T1enc_A_txt
                                                                                                                        W
                                                                                                                        Rn
                                                                                                                        P
                                                                                                                        M
                                                                                                                        register_list)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__308 ← (( do
                                                                                                                        if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               31
                                                                                                                               20)) == (0xF88#12 : (BitVec 12))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__307 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__307 <b 3195) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__308 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3195
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Rt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let imm12 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              12)
                                                                                                                          (decode_aarch32_instrs_STRB_i_T2enc_A_txt
                                                                                                                            Rn
                                                                                                                            Rt
                                                                                                                            imm12)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__310 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xF80#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     11
                                                                                                                                     11)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__309 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__309 <b 3196) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__310 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3196
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let Rt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let P :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  1)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  9
                                                                                                                                  1)
                                                                                                                              let W :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  8
                                                                                                                                  1)
                                                                                                                              let imm8 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  8)
                                                                                                                              (decode_aarch32_instrs_STRB_i_T3enc_A_txt
                                                                                                                                Rn
                                                                                                                                Rt
                                                                                                                                P
                                                                                                                                U
                                                                                                                                W
                                                                                                                                imm8)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__312 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         20)) == (0xF80#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         11
                                                                                                                                         6)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__311 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__311 <b 3199) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__312 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3199
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let Rt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      4)
                                                                                                                                  let imm2 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      4
                                                                                                                                      2)
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  (decode_aarch32_instrs_STRB_r_T2enc_A_txt
                                                                                                                                    Rn
                                                                                                                                    Rt
                                                                                                                                    imm2
                                                                                                                                    Rm)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__314 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             20)) == (0xF80#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             11
                                                                                                                                             8)) == (0xE#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__313 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__313 <b 3202) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__314 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3202
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let Rt :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          4)
                                                                                                                                      let imm8 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          8)
                                                                                                                                      (decode_aarch32_instrs_STRBT_T1enc_A_txt
                                                                                                                                        Rn
                                                                                                                                        Rt
                                                                                                                                        imm8)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__316 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 25)) == (0b1110100#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   22
                                                                                                                                                   22)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   20
                                                                                                                                                   20)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__315 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__315 <b 3204) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__316 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 3204
                                                                                                                                          let P :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              24
                                                                                                                                              1)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              23
                                                                                                                                              1)
                                                                                                                                          let W :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              21
                                                                                                                                              1)
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let Rt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              12
                                                                                                                                              4)
                                                                                                                                          let Rt2 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              8
                                                                                                                                              4)
                                                                                                                                          let imm8 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              8)
                                                                                                                                          (decode_aarch32_instrs_STRD_i_T1enc_A_txt
                                                                                                                                            P
                                                                                                                                            U
                                                                                                                                            W
                                                                                                                                            Rn
                                                                                                                                            Rt
                                                                                                                                            Rt2
                                                                                                                                            imm8)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__318 ← (( do
                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   31
                                                                                                                                                   20)) == (0xE84#12 : (BitVec 12))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__317 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__317 <b 3207) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__318 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 3207
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let Rt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  12
                                                                                                                                                  4)
                                                                                                                                              let Rd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  8
                                                                                                                                                  4)
                                                                                                                                              let imm8 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  8)
                                                                                                                                              (decode_aarch32_instrs_STREX_T1enc_A_txt
                                                                                                                                                Rn
                                                                                                                                                Rt
                                                                                                                                                Rd
                                                                                                                                                imm8)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__320 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         11
                                                                                                                                                         4)) == (0xF4#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__319 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__319 <b 3209) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__320 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 3209
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      4)
                                                                                                                                                  let Rt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      12
                                                                                                                                                      4)
                                                                                                                                                  let Rd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      4)
                                                                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                 __opcode
                                                                                                                                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                 __opcode
                                                                                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                               __opcode
                                                                                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                             __opcode
                                                                                                                                                             11)])) != 1#1)) : Bool)
                                                                                                                                                  then
                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                      ()))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      (decode_aarch32_instrs_STREXB_T1enc_A_txt
                                                                                                                                                        Rn
                                                                                                                                                        Rt
                                                                                                                                                        Rd))
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__322 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             7
                                                                                                                                                             4)) == (0x7#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__321 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__321 <b 3211) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__322 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 3211
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          4)
                                                                                                                                                      let Rt :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          12
                                                                                                                                                          4)
                                                                                                                                                      let Rt2 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          8
                                                                                                                                                          4)
                                                                                                                                                      let Rd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          4)
                                                                                                                                                      (decode_aarch32_instrs_STREXD_T1enc_A_txt
                                                                                                                                                        Rn
                                                                                                                                                        Rt
                                                                                                                                                        Rt2
                                                                                                                                                        Rd)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__324 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 20)) == (0xE8C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 11
                                                                                                                                                                 4)) == (0xF5#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__323 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__323 <b 3213) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__324 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 3213
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              4)
                                                                                                                                                          let Rt :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              12
                                                                                                                                                              4)
                                                                                                                                                          let Rd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              4)
                                                                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                         __opcode
                                                                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                         __opcode
                                                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                       __opcode
                                                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                     __opcode
                                                                                                                                                                     11)])) != 1#1)) : Bool)
                                                                                                                                                          then
                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                              ()))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              (decode_aarch32_instrs_STREXH_T1enc_A_txt
                                                                                                                                                                Rn
                                                                                                                                                                Rt
                                                                                                                                                                Rd))
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__326 ← (( do
                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   31
                                                                                                                                                                   20)) == (0xF8A#12 : (BitVec 12))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__325 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__325 <b 3216) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__326 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 3216
                                                                                                                                                              let Rn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  4)
                                                                                                                                                              let Rt :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  12
                                                                                                                                                                  4)
                                                                                                                                                              let imm12 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  12)
                                                                                                                                                              (decode_aarch32_instrs_STRH_i_T2enc_A_txt
                                                                                                                                                                Rn
                                                                                                                                                                Rt
                                                                                                                                                                imm12)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__328 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         20)) == (0xF82#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         11
                                                                                                                                                                         11)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__327 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__327 <b 3217) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__328 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 3217
                                                                                                                                                                  let Rn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      4)
                                                                                                                                                                  let Rt :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      12
                                                                                                                                                                      4)
                                                                                                                                                                  let P :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      1)
                                                                                                                                                                  let U :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      9
                                                                                                                                                                      1)
                                                                                                                                                                  let W :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      8
                                                                                                                                                                      1)
                                                                                                                                                                  let imm8 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      8)
                                                                                                                                                                  (decode_aarch32_instrs_STRH_i_T3enc_A_txt
                                                                                                                                                                    Rn
                                                                                                                                                                    Rt
                                                                                                                                                                    P
                                                                                                                                                                    U
                                                                                                                                                                    W
                                                                                                                                                                    imm8)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__330 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             20)) == (0xF82#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             11
                                                                                                                                                                             6)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__329 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__329 <b 3220) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__330 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 3220
                                                                                                                                                                      let Rn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          4)
                                                                                                                                                                      let Rt :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          12
                                                                                                                                                                          4)
                                                                                                                                                                      let imm2 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          4
                                                                                                                                                                          2)
                                                                                                                                                                      let Rm :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          4)
                                                                                                                                                                      (decode_aarch32_instrs_STRH_r_T2enc_A_txt
                                                                                                                                                                        Rn
                                                                                                                                                                        Rt
                                                                                                                                                                        imm2
                                                                                                                                                                        Rm)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__332 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 20)) == (0xF82#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 11
                                                                                                                                                                                 8)) == (0xE#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__331 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__331 <b 3223) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__332 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 3223
                                                                                                                                                                          let Rn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              4)
                                                                                                                                                                          let Rt :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              12
                                                                                                                                                                              4)
                                                                                                                                                                          let imm8 :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              8)
                                                                                                                                                                          (decode_aarch32_instrs_STRHT_T1enc_A_txt
                                                                                                                                                                            Rn
                                                                                                                                                                            Rt
                                                                                                                                                                            imm8)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__334 ← (( do
                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   31
                                                                                                                                                                                   20)) == (0xF8C#12 : (BitVec 12))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__333 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__333 <b 3227) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__334 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 3227
                                                                                                                                                                              let Rn :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  16
                                                                                                                                                                                  4)
                                                                                                                                                                              let Rt :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  12
                                                                                                                                                                                  4)
                                                                                                                                                                              let imm12 :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  12)
                                                                                                                                                                              (decode_aarch32_instrs_STR_i_T3enc_A_txt
                                                                                                                                                                                Rn
                                                                                                                                                                                Rt
                                                                                                                                                                                imm12)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__336 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         20)) == (0xF84#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         11
                                                                                                                                                                                         11)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__335 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__335 <b 3228) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__336 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 3228
                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      16
                                                                                                                                                                                      4)
                                                                                                                                                                                  let Rt :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      12
                                                                                                                                                                                      4)
                                                                                                                                                                                  let P :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      10
                                                                                                                                                                                      1)
                                                                                                                                                                                  let U :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      9
                                                                                                                                                                                      1)
                                                                                                                                                                                  let W :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      8
                                                                                                                                                                                      1)
                                                                                                                                                                                  let imm8 :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      8)
                                                                                                                                                                                  (decode_aarch32_instrs_STR_i_T4enc_A_txt
                                                                                                                                                                                    Rn
                                                                                                                                                                                    Rt
                                                                                                                                                                                    P
                                                                                                                                                                                    U
                                                                                                                                                                                    W
                                                                                                                                                                                    imm8)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__338 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             31
                                                                                                                                                                                             20)) == (0xF84#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             11
                                                                                                                                                                                             6)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__337 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__337 <b 3231) : Bool))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false)
                                                                                                                                                                                    )
                                                                                                                                                                                    :
                                                                                                                                                                                    SailM
                                                                                                                                                                                    Bool
                                                                                                                                                                                    )
                                                                                                                                                                                  if (w__338 : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 3231
                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          16
                                                                                                                                                                                          4)
                                                                                                                                                                                      let Rt :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          12
                                                                                                                                                                                          4)
                                                                                                                                                                                      let imm2 :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          4
                                                                                                                                                                                          2)
                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          0
                                                                                                                                                                                          4)
                                                                                                                                                                                      (decode_aarch32_instrs_STR_r_T2enc_A_txt
                                                                                                                                                                                        Rn
                                                                                                                                                                                        Rt
                                                                                                                                                                                        imm2
                                                                                                                                                                                        Rm)
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                  else
                                                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
