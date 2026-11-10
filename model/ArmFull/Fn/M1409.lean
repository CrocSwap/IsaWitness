import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0985
import ArmFull.Fn.M0986
import ArmFull.Fn.M0987
import ArmFull.Fn.M1161
import ArmFull.Fn.M1340
import ArmFull.Fn.M1341

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
def __DecodeA64_SME__seg2 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__149 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100001100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
             __opcode 4 2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
    then
      (do
        let w__148 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__148 <b 2268) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__149 : Bool)
  then
    (do
      writeReg SEE 2268
      let u0 := (BitVec.slice __opcode 24 1)
      let u1 := (BitVec.slice __opcode 21 1)
      let Zm := (BitVec.slice __opcode 16 5)
      let Pm := (BitVec.slice __opcode 13 3)
      let Pn := (BitVec.slice __opcode 10 3)
      let Zn := (BitVec.slice __opcode 5 5)
      let S := (BitVec.slice __opcode 4 1)
      let ZAda := (BitVec.slice __opcode 0 2)
      (decode_USMOPA_ZA_PP_ZZ_32 u0 u1 Zm Pm Pn Zn S ZAda)
      (pure false))
  else
    (do
      let w__151 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100001101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 4 2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
        then
          (do
            let w__150 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__150 <b 2269) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__151 : Bool)
      then
        (do
          writeReg SEE 2269
          let u0 := (BitVec.slice __opcode 24 1)
          let u1 := (BitVec.slice __opcode 21 1)
          let Zm := (BitVec.slice __opcode 16 5)
          let Pm := (BitVec.slice __opcode 13 3)
          let Pn := (BitVec.slice __opcode 10 3)
          let Zn := (BitVec.slice __opcode 5 5)
          let S := (BitVec.slice __opcode 4 1)
          let ZAda := (BitVec.slice __opcode 0 2)
          (decode_UMOPA_ZA_PP_ZZ_32 u0 u1 Zm Pm Pn Zn S ZAda)
          (pure false))
      else
        (do
          let w__153 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 4 2)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
            then
              (do
                let w__152 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__152 <b 2270) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__153 : Bool)
          then
            (do
              writeReg SEE 2270
              let u0 := (BitVec.slice __opcode 24 1)
              let u1 := (BitVec.slice __opcode 21 1)
              let Zm := (BitVec.slice __opcode 16 5)
              let Pm := (BitVec.slice __opcode 13 3)
              let Pn := (BitVec.slice __opcode 10 3)
              let Zn := (BitVec.slice __opcode 5 5)
              let S := (BitVec.slice __opcode 4 1)
              let ZAda := (BitVec.slice __opcode 0 2)
              (decode_SMOPS_ZA_PP_ZZ_32 u0 u1 Zm Pm Pn Zn S ZAda)
              (pure false))
          else
            (do
              let w__155 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100000101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 4 2)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                then
                  (do
                    let w__154 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__154 <b 2271) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__155 : Bool)
              then
                (do
                  writeReg SEE 2271
                  let u0 := (BitVec.slice __opcode 24 1)
                  let u1 := (BitVec.slice __opcode 21 1)
                  let Zm := (BitVec.slice __opcode 16 5)
                  let Pm := (BitVec.slice __opcode 13 3)
                  let Pn := (BitVec.slice __opcode 10 3)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let S := (BitVec.slice __opcode 4 1)
                  let ZAda := (BitVec.slice __opcode 0 2)
                  (decode_SUMOPS_ZA_PP_ZZ_32 u0 u1 Zm Pm Pn Zn S ZAda)
                  (pure false))
              else
                (do
                  let w__157 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100001100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 4 2)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                    then
                      (do
                        let w__156 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__156 <b 2272) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__157 : Bool)
                  then
                    (do
                      writeReg SEE 2272
                      let u0 := (BitVec.slice __opcode 24 1)
                      let u1 := (BitVec.slice __opcode 21 1)
                      let Zm := (BitVec.slice __opcode 16 5)
                      let Pm := (BitVec.slice __opcode 13 3)
                      let Pn := (BitVec.slice __opcode 10 3)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let S := (BitVec.slice __opcode 4 1)
                      let ZAda := (BitVec.slice __opcode 0 2)
                      (decode_USMOPS_ZA_PP_ZZ_32 u0 u1 Zm Pm Pn Zn S ZAda)
                      (pure false))
                  else
                    (do
                      let w__159 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b10100001101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 4 2)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                        then
                          (do
                            let w__158 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__158 <b 2273) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__159 : Bool)
                      then
                        (do
                          writeReg SEE 2273
                          let u0 := (BitVec.slice __opcode 24 1)
                          let u1 := (BitVec.slice __opcode 21 1)
                          let Zm := (BitVec.slice __opcode 16 5)
                          let Pm := (BitVec.slice __opcode 13 3)
                          let Pn := (BitVec.slice __opcode 10 3)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let S := (BitVec.slice __opcode 4 1)
                          let ZAda := (BitVec.slice __opcode 0 2)
                          (decode_UMOPS_ZA_PP_ZZ_32 u0 u1 Zm Pm Pn Zn S ZAda)
                          (pure false))
                      else
                        (do
                          let w__161 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode
                                     31 21)) == (0b10100000110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 4 3)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                            then
                              (do
                                let w__160 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__160 <b 2274) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__161 : Bool)
                          then
                            (do
                              writeReg SEE 2274
                              let u0 := (BitVec.slice __opcode 24 1)
                              let u1 := (BitVec.slice __opcode 21 1)
                              let Zm := (BitVec.slice __opcode 16 5)
                              let Pm := (BitVec.slice __opcode 13 3)
                              let Pn := (BitVec.slice __opcode 10 3)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let S := (BitVec.slice __opcode 4 1)
                              let ZAda := (BitVec.slice __opcode 0 3)
                              (decode_SMOPA_ZA_PP_ZZ_64 u0 u1 Zm Pm Pn Zn S ZAda)
                              (pure false))
                          else
                            (do
                              let w__163 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b10100000111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         __opcode 4 3)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__162 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__162 <b 2275) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__163 : Bool)
                              then
                                (do
                                  writeReg SEE 2275
                                  let u0 := (BitVec.slice __opcode 24 1)
                                  let u1 := (BitVec.slice __opcode 21 1)
                                  let Zm := (BitVec.slice __opcode 16 5)
                                  let Pm := (BitVec.slice __opcode 13 3)
                                  let Pn := (BitVec.slice __opcode 10 3)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let S := (BitVec.slice __opcode 4 1)
                                  let ZAda := (BitVec.slice __opcode 0 3)
                                  (decode_SUMOPA_ZA_PP_ZZ_64 u0 u1 Zm Pm Pn Zn S ZAda)
                                  (pure false))
                              else
                                (do
                                  let w__165 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b10100001110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 4 3)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__164 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__164 <b 2276) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__165 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2276
                                      let u0 := (BitVec.slice __opcode 24 1)
                                      let u1 := (BitVec.slice __opcode 21 1)
                                      let Zm := (BitVec.slice __opcode 16 5)
                                      let Pm := (BitVec.slice __opcode 13 3)
                                      let Pn := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let S := (BitVec.slice __opcode 4 1)
                                      let ZAda := (BitVec.slice __opcode 0 3)
                                      (decode_USMOPA_ZA_PP_ZZ_64 u0 u1 Zm Pm Pn Zn S ZAda)
                                      (pure false))
                                  else
                                    (do
                                      let w__167 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b10100001111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 4 3)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__166 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__166 <b 2277) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__167 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2277
                                          let u0 := (BitVec.slice __opcode 24 1)
                                          let u1 := (BitVec.slice __opcode 21 1)
                                          let Zm := (BitVec.slice __opcode 16 5)
                                          let Pm := (BitVec.slice __opcode 13 3)
                                          let Pn := (BitVec.slice __opcode 10 3)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let S := (BitVec.slice __opcode 4 1)
                                          let ZAda := (BitVec.slice __opcode 0 3)
                                          (decode_UMOPA_ZA_PP_ZZ_64 u0 u1 Zm Pm Pn Zn S ZAda)
                                          (pure false))
                                      else
                                        (do
                                          let w__169 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b10100000110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                     __opcode 4 3)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__168 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__168 <b 2278) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__169 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2278
                                              let u0 := (BitVec.slice __opcode 24 1)
                                              let u1 := (BitVec.slice __opcode 21 1)
                                              let Zm := (BitVec.slice __opcode 16 5)
                                              let Pm := (BitVec.slice __opcode 13 3)
                                              let Pn := (BitVec.slice __opcode 10 3)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let S := (BitVec.slice __opcode 4 1)
                                              let ZAda := (BitVec.slice __opcode 0 3)
                                              (decode_SMOPS_ZA_PP_ZZ_64 u0 u1 Zm Pm Pn Zn S ZAda)
                                              (pure false))
                                          else
                                            (do
                                              let w__171 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                         __opcode 31 21)) == (0b10100000111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 4 3)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__170 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__170 <b 2279) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__171 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2279
                                                  let u0 := (BitVec.slice __opcode 24 1)
                                                  let u1 := (BitVec.slice __opcode 21 1)
                                                  let Zm := (BitVec.slice __opcode 16 5)
                                                  let Pm := (BitVec.slice __opcode 13 3)
                                                  let Pn := (BitVec.slice __opcode 10 3)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let S := (BitVec.slice __opcode 4 1)
                                                  let ZAda := (BitVec.slice __opcode 0 3)
                                                  (decode_SUMOPS_ZA_PP_ZZ_64 u0 u1 Zm Pm Pn Zn S
                                                    ZAda)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__173 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b10100001110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                             __opcode 4 3)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__172 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__172 <b 2280) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__173 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2280
                                                      let u0 := (BitVec.slice __opcode 24 1)
                                                      let u1 := (BitVec.slice __opcode 21 1)
                                                      let Zm := (BitVec.slice __opcode 16 5)
                                                      let Pm := (BitVec.slice __opcode 13 3)
                                                      let Pn := (BitVec.slice __opcode 10 3)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let S := (BitVec.slice __opcode 4 1)
                                                      let ZAda := (BitVec.slice __opcode 0 3)
                                                      (decode_USMOPS_ZA_PP_ZZ_64 u0 u1 Zm Pm Pn Zn S
                                                        ZAda)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__175 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b10100001111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                 __opcode 4 3)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__174 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__174 <b 2281) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__175 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2281
                                                          let u0 := (BitVec.slice __opcode 24 1)
                                                          let u1 := (BitVec.slice __opcode 21 1)
                                                          let Zm := (BitVec.slice __opcode 16 5)
                                                          let Pm := (BitVec.slice __opcode 13 3)
                                                          let Pn := (BitVec.slice __opcode 10 3)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let S := (BitVec.slice __opcode 4 1)
                                                          let ZAda := (BitVec.slice __opcode 0 3)
                                                          (decode_UMOPS_ZA_PP_ZZ_64 u0 u1 Zm Pm Pn
                                                            Zn S ZAda)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__177 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                     __opcode 31 16)) == (0xC000#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__176 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__176 <b 2282) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__177 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2282
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Q := (BitVec.slice __opcode 16 1)
                                                              let V := (BitVec.slice __opcode 15 1)
                                                              let Rs := (BitVec.slice __opcode 13 2)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let off4 :=
                                                                (BitVec.slice __opcode 0 4)
                                                              (decode_MOVA_ZA_P_RZ_B size Q V Rs Pg
                                                                Zn off4)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__179 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                         __opcode 31 16)) == (0xC040#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__178 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__178 <b 2283) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__179 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2283
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 16 1)
                                                                  let V :=
                                                                    (BitVec.slice __opcode 15 1)
                                                                  let Rs :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let ZAd :=
                                                                    (BitVec.slice __opcode 3 1)
                                                                  let off3 :=
                                                                    (BitVec.slice __opcode 0 3)
                                                                  (decode_MOVA_ZA_P_RZ_H size Q V Rs
                                                                    Pg Zn ZAd off3)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__181 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                             __opcode 31 16)) == (0xC080#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__180 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__180 <b 2284) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__181 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2284
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 16 1)
                                                                      let V :=
                                                                        (BitVec.slice __opcode 15 1)
                                                                      let Rs :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let ZAd :=
                                                                        (BitVec.slice __opcode 2 2)
                                                                      let off2 :=
                                                                        (BitVec.slice __opcode 0 2)
                                                                      (decode_MOVA_ZA_P_RZ_W size Q
                                                                        V Rs Pg Zn ZAd off2)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__183 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 16)) == (0xC0C0#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__182 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__182 <b 2285) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__183 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2285
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Q :=
                                                                            (BitVec.slice __opcode
                                                                              16 1)
                                                                          let V :=
                                                                            (BitVec.slice __opcode
                                                                              15 1)
                                                                          let Rs :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let ZAd :=
                                                                            (BitVec.slice __opcode 1
                                                                              3)
                                                                          let o1 :=
                                                                            (BitVec.slice __opcode 0
                                                                              1)
                                                                          (decode_MOVA_ZA_P_RZ_D
                                                                            size Q V Rs Pg Zn ZAd o1)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__185 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 16)) == (0xC0C1#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__184 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__184 <b 2286) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__185 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2286
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let Q :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 1)
                                                                              let V :=
                                                                                (BitVec.slice
                                                                                  __opcode 15 1)
                                                                              let Rs :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let ZAd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_MOVA_ZA_P_RZ_Q
                                                                                size Q V Rs Pg Zn
                                                                                ZAd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__187 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         16)) == (0xC002#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 9
                                                                                         9)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__186 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__186 <b 2287) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__187 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2287
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 1)
                                                                                  let V :=
                                                                                    (BitVec.slice
                                                                                      __opcode 15 1)
                                                                                  let Rs :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let off4 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 4)
                                                                                  let Zd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_MOVA_Z_P_RZA_B
                                                                                    size Q V Rs Pg
                                                                                    off4 Zd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__189 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 16)) == (0xC042#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             9 9)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__188 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__188 <b 2288) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__189 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2288
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 1)
                                                                                      let V :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          15 1)
                                                                                      let Rs :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let ZAn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 8
                                                                                          1)
                                                                                      let off3 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          3)
                                                                                      let Zd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_MOVA_Z_P_RZA_H
                                                                                        size Q V Rs
                                                                                        Pg ZAn off3
                                                                                        Zd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__191 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 16)) == (0xC082#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 9 9)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__190 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__190 <b 2289) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__191 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2289
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 1)
                                                                                          let V :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              15 1)
                                                                                          let Rs :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let ZAn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              7 2)
                                                                                          let off2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 2)
                                                                                          let Zd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_MOVA_Z_P_RZA_W
                                                                                            size Q V
                                                                                            Rs Pg
                                                                                            ZAn off2
                                                                                            Zd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__193 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     16)) == (0xC0C2#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     9
                                                                                                     9)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__192 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__192 <b 2290) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__193 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2290
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let Q :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  1)
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
                                                                                              let Pg :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  3)
                                                                                              let ZAn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  6
                                                                                                  3)
                                                                                              let o1 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  1)
                                                                                              let Zd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_MOVA_Z_P_RZA_D
                                                                                                size
                                                                                                Q V
                                                                                                Rs
                                                                                                Pg
                                                                                                ZAn
                                                                                                o1
                                                                                                Zd)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__195 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         16)) == (0xC0C3#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         9
                                                                                                         9)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__194 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__194 <b 2291) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__195 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2291
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
                                                                                                  let Q :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      1)
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
                                                                                                  let Pg :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      3)
                                                                                                  let ZAn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      4)
                                                                                                  let Zd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_MOVA_Z_P_RZA_Q
                                                                                                    size
                                                                                                    Q
                                                                                                    V
                                                                                                    Rs
                                                                                                    Pg
                                                                                                    ZAn
                                                                                                    Zd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__197 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             15)) == (0b11100001000000000#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               12
                                                                                                               10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               4
                                                                                                               4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__196 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__196 <b 2292) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__197 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2292
                                                                                                      let Rv :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          2)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let off4 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_LDR_ZA_RI__
                                                                                                        Rv
                                                                                                        Rn
                                                                                                        off4)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__199 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 15)) == (0b11100001001000000#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   12
                                                                                                                   10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   4
                                                                                                                   4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__198 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__198 <b 2293) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__199 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2293
                                                                                                          let Rv :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              2)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let off4 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_STR_ZA_RI__
                                                                                                            Rv
                                                                                                            Rn
                                                                                                            off4)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__201 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b11100000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     4
                                                                                                                     4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__200 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__200 <b 2294) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__201 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2294
                                                                                                              let msz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
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
                                                                                                              let off4 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_LD1B_ZA_P_RRR__
                                                                                                                msz
                                                                                                                Rm
                                                                                                                V
                                                                                                                Rs
                                                                                                                Pg
                                                                                                                Rn
                                                                                                                off4)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__203 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b11100000010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__202 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__202 <b 2295) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__203 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2295
                                                                                                                  let msz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
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
                                                                                                                  let ZAt :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      3
                                                                                                                      1)
                                                                                                                  let off3 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      3)
                                                                                                                  (decode_LD1H_ZA_P_RRR__
                                                                                                                    msz
                                                                                                                    Rm
                                                                                                                    V
                                                                                                                    Rs
                                                                                                                    Pg
                                                                                                                    Rn
                                                                                                                    ZAt
                                                                                                                    off3)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__205 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b11100000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             4
                                                                                                                             4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__204 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__204 <b 2296) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__205 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2296
                                                                                                                      let msz :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
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
                                                                                                                      let ZAt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          2
                                                                                                                          2)
                                                                                                                      let off2 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          2)
                                                                                                                      (decode_LD1W_ZA_P_RRR__
                                                                                                                        msz
                                                                                                                        Rm
                                                                                                                        V
                                                                                                                        Rs
                                                                                                                        Pg
                                                                                                                        Rn
                                                                                                                        ZAt
                                                                                                                        off2)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__207 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b11100000110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__206 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__206 <b 2297) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__207 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2297
                                                                                                                          let msz :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
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
                                                                                                                          let ZAt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              1
                                                                                                                              3)
                                                                                                                          let o1 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              1)
                                                                                                                          (decode_LD1D_ZA_P_RRR__
                                                                                                                            msz
                                                                                                                            Rm
                                                                                                                            V
                                                                                                                            Rs
                                                                                                                            Pg
                                                                                                                            Rn
                                                                                                                            ZAt
                                                                                                                            o1)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__209 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b11100001110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     4
                                                                                                                                     4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__208 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__208 <b 2298) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__209 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2298
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
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
                                                                                                                              let ZAt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_LD1Q_ZA_P_RRR__
                                                                                                                                Rm
                                                                                                                                V
                                                                                                                                Rs
                                                                                                                                Pg
                                                                                                                                Rn
                                                                                                                                ZAt)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__211 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b11100000001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         4
                                                                                                                                         4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__210 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__210 <b 2299) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__211 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2299
                                                                                                                                  let msz :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
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
                                                                                                                                  let off4 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  (decode_ST1B_ZA_P_RRR__
                                                                                                                                    msz
                                                                                                                                    Rm
                                                                                                                                    V
                                                                                                                                    Rs
                                                                                                                                    Pg
                                                                                                                                    Rn
                                                                                                                                    off4)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__213 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b11100000011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             4
                                                                                                                                             4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__212 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__212 <b 2300) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__213 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2300
                                                                                                                                      let msz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let Rm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
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
                                                                                                                                      let ZAt :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          3
                                                                                                                                          1)
                                                                                                                                      let off3 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          3)
                                                                                                                                      (decode_ST1H_ZA_P_RRR__
                                                                                                                                        msz
                                                                                                                                        Rm
                                                                                                                                        V
                                                                                                                                        Rs
                                                                                                                                        Pg
                                                                                                                                        Rn
                                                                                                                                        ZAt
                                                                                                                                        off3)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__215 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b11100000101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 4
                                                                                                                                                 4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__214 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__214 <b 2301) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__215 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2301
                                                                                                                                          let msz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let Rm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
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
                                                                                                                                          let ZAt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              2
                                                                                                                                              2)
                                                                                                                                          let off2 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              2)
                                                                                                                                          (decode_ST1W_ZA_P_RRR__
                                                                                                                                            msz
                                                                                                                                            Rm
                                                                                                                                            V
                                                                                                                                            Rs
                                                                                                                                            Pg
                                                                                                                                            Rn
                                                                                                                                            ZAt
                                                                                                                                            off2)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__217 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b11100000111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     4
                                                                                                                                                     4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__216 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__216 <b 2302) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__217 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2302
                                                                                                                                              let msz :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let Rm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
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
                                                                                                                                              let ZAt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  1
                                                                                                                                                  3)
                                                                                                                                              let o1 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  1)
                                                                                                                                              (decode_ST1D_ZA_P_RRR__
                                                                                                                                                msz
                                                                                                                                                Rm
                                                                                                                                                V
                                                                                                                                                Rs
                                                                                                                                                Pg
                                                                                                                                                Rn
                                                                                                                                                ZAt
                                                                                                                                                o1)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__219 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         21)) == (0b11100001111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         4
                                                                                                                                                         4)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__218 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__218 <b 2303) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__219 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2303
                                                                                                                                                  let Rm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
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
                                                                                                                                                  let ZAt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      4)
                                                                                                                                                  (decode_ST1Q_ZA_P_RRR__
                                                                                                                                                    Rm
                                                                                                                                                    V
                                                                                                                                                    Rs
                                                                                                                                                    Pg
                                                                                                                                                    Rn
                                                                                                                                                    ZAt)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
