import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1026
import ArmFull.Fn.M1027
import ArmFull.Fn.M1325
import ArmFull.Fn.M1326

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
def __DecodeA64_SVE__seg24 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1965 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA52#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
             __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
    then
      (do
        let w__1964 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1964 <b 2019) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1965 : Bool)
  then
    (do
      writeReg SEE 2019
      let msz := (BitVec.slice __opcode 23 2)
      let ssz := (BitVec.slice __opcode 21 2)
      let imm4 := (BitVec.slice __opcode 16 4)
      let Pg := (BitVec.slice __opcode 10 3)
      let Rn := (BitVec.slice __opcode 5 5)
      let Zt := (BitVec.slice __opcode 0 5)
      (decode_LD1ROW_Z_P_BI_U32 msz ssz imm4 Pg Rn Zt)
      (pure false))
  else
    (do
      let w__1967 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA5A#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 15 13)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
        then
          (do
            let w__1966 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1966 <b 2020) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1967 : Bool)
      then
        (do
          writeReg SEE 2020
          let msz := (BitVec.slice __opcode 23 2)
          let ssz := (BitVec.slice __opcode 21 2)
          let imm4 := (BitVec.slice __opcode 16 4)
          let Pg := (BitVec.slice __opcode 10 3)
          let Rn := (BitVec.slice __opcode 5 5)
          let Zt := (BitVec.slice __opcode 0 5)
          (decode_LD1ROD_Z_P_BI_U64 msz ssz imm4 Pg Rn Zt)
          (pure false))
      else
        (do
          let w__1969 ← (( do
            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b110001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                       __opcode 15 13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
            then
              (do
                let w__1968 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1968 <b 2021) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1969 : Bool)
          then
            (do
              writeReg SEE 2021
              let msz := (BitVec.slice __opcode 23 2)
              let xs := (BitVec.slice __opcode 22 1)
              let Zm := (BitVec.slice __opcode 16 5)
              let U := (BitVec.slice __opcode 14 1)
              let ff := (BitVec.slice __opcode 13 1)
              let Pg := (BitVec.slice __opcode 10 3)
              let Rn := (BitVec.slice __opcode 5 5)
              let Zt := (BitVec.slice __opcode 0 5)
              (decode_LD1B_Z_P_BZ_D_x32_unscaled msz xs Zm U ff Pg Rn Zt)
              (pure false))
          else
            (do
              let w__1971 ← (( do
                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b110001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                           __opcode 15 13)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                then
                  (do
                    let w__1970 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1970 <b 2022) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1971 : Bool)
              then
                (do
                  writeReg SEE 2022
                  let msz := (BitVec.slice __opcode 23 2)
                  let xs := (BitVec.slice __opcode 22 1)
                  let Zm := (BitVec.slice __opcode 16 5)
                  let U := (BitVec.slice __opcode 14 1)
                  let ff := (BitVec.slice __opcode 13 1)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Zt := (BitVec.slice __opcode 0 5)
                  (decode_LD1SB_Z_P_BZ_D_x32_unscaled msz xs Zm U ff Pg Rn Zt)
                  (pure false))
              else
                (do
                  let w__1973 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b110001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                               __opcode 15 13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                    then
                      (do
                        let w__1972 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1972 <b 2023) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1973 : Bool)
                  then
                    (do
                      writeReg SEE 2023
                      let msz := (BitVec.slice __opcode 23 2)
                      let xs := (BitVec.slice __opcode 22 1)
                      let Zm := (BitVec.slice __opcode 16 5)
                      let U := (BitVec.slice __opcode 14 1)
                      let ff := (BitVec.slice __opcode 13 1)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Zt := (BitVec.slice __opcode 0 5)
                      (decode_LDFF1B_Z_P_BZ_D_x32_unscaled msz xs Zm U ff Pg Rn Zt)
                      (pure false))
                  else
                    (do
                      let w__1975 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31
                                 23)) == (0b110001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   __opcode 15 13)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                        then
                          (do
                            let w__1974 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1974 <b 2024) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1975 : Bool)
                      then
                        (do
                          writeReg SEE 2024
                          let msz := (BitVec.slice __opcode 23 2)
                          let xs := (BitVec.slice __opcode 22 1)
                          let Zm := (BitVec.slice __opcode 16 5)
                          let U := (BitVec.slice __opcode 14 1)
                          let ff := (BitVec.slice __opcode 13 1)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let Zt := (BitVec.slice __opcode 0 5)
                          (decode_LDFF1SB_Z_P_BZ_D_x32_unscaled msz xs Zm U ff Pg Rn Zt)
                          (pure false))
                      else
                        (do
                          let w__1977 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode
                                     31 23)) == (0b110001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                       __opcode 15 13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                            then
                              (do
                                let w__1976 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1976 <b 2025) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1977 : Bool)
                          then
                            (do
                              writeReg SEE 2025
                              let msz := (BitVec.slice __opcode 23 2)
                              let xs := (BitVec.slice __opcode 22 1)
                              let Zm := (BitVec.slice __opcode 16 5)
                              let U := (BitVec.slice __opcode 14 1)
                              let ff := (BitVec.slice __opcode 13 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let Zt := (BitVec.slice __opcode 0 5)
                              (decode_LD1H_Z_P_BZ_D_x32_unscaled msz xs Zm U ff Pg Rn Zt)
                              (pure false))
                          else
                            (do
                              let w__1979 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b110001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 15 13)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1978 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1978 <b 2026) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1979 : Bool)
                              then
                                (do
                                  writeReg SEE 2026
                                  let msz := (BitVec.slice __opcode 23 2)
                                  let xs := (BitVec.slice __opcode 22 1)
                                  let Zm := (BitVec.slice __opcode 16 5)
                                  let U := (BitVec.slice __opcode 14 1)
                                  let ff := (BitVec.slice __opcode 13 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let Zt := (BitVec.slice __opcode 0 5)
                                  (decode_LD1SH_Z_P_BZ_D_x32_unscaled msz xs Zm U ff Pg Rn Zt)
                                  (pure false))
                              else
                                (do
                                  let w__1981 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b110001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 15 13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1980 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1980 <b 2027) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1981 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2027
                                      let msz := (BitVec.slice __opcode 23 2)
                                      let xs := (BitVec.slice __opcode 22 1)
                                      let Zm := (BitVec.slice __opcode 16 5)
                                      let U := (BitVec.slice __opcode 14 1)
                                      let ff := (BitVec.slice __opcode 13 1)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let Zt := (BitVec.slice __opcode 0 5)
                                      (decode_LDFF1H_Z_P_BZ_D_x32_unscaled msz xs Zm U ff Pg Rn Zt)
                                      (pure false))
                                  else
                                    (do
                                      let w__1983 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b110001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 15 13)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1982 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1982 <b 2028) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1983 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2028
                                          let msz := (BitVec.slice __opcode 23 2)
                                          let xs := (BitVec.slice __opcode 22 1)
                                          let Zm := (BitVec.slice __opcode 16 5)
                                          let U := (BitVec.slice __opcode 14 1)
                                          let ff := (BitVec.slice __opcode 13 1)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let Zt := (BitVec.slice __opcode 0 5)
                                          (decode_LDFF1SH_Z_P_BZ_D_x32_unscaled msz xs Zm U ff Pg Rn
                                            Zt)
                                          (pure false))
                                      else
                                        (do
                                          let w__1985 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 31 23)) == (0b110001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 15 13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1984 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1984 <b 2029) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1985 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2029
                                              let msz := (BitVec.slice __opcode 23 2)
                                              let xs := (BitVec.slice __opcode 22 1)
                                              let Zm := (BitVec.slice __opcode 16 5)
                                              let U := (BitVec.slice __opcode 14 1)
                                              let ff := (BitVec.slice __opcode 13 1)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let Zt := (BitVec.slice __opcode 0 5)
                                              (decode_LD1W_Z_P_BZ_D_x32_unscaled msz xs Zm U ff Pg
                                                Rn Zt)
                                              (pure false))
                                          else
                                            (do
                                              let w__1987 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b110001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                           __opcode 15 13)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1986 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1986 <b 2030) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1987 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2030
                                                  let msz := (BitVec.slice __opcode 23 2)
                                                  let xs := (BitVec.slice __opcode 22 1)
                                                  let Zm := (BitVec.slice __opcode 16 5)
                                                  let U := (BitVec.slice __opcode 14 1)
                                                  let ff := (BitVec.slice __opcode 13 1)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                  (decode_LD1SW_Z_P_BZ_D_x32_unscaled msz xs Zm U ff
                                                    Pg Rn Zt)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1989 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b110001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 15 13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1988 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1988 <b 2031) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1989 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2031
                                                      let msz := (BitVec.slice __opcode 23 2)
                                                      let xs := (BitVec.slice __opcode 22 1)
                                                      let Zm := (BitVec.slice __opcode 16 5)
                                                      let U := (BitVec.slice __opcode 14 1)
                                                      let ff := (BitVec.slice __opcode 13 1)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                      (decode_LDFF1W_Z_P_BZ_D_x32_unscaled msz xs Zm
                                                        U ff Pg Rn Zt)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1991 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b110001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                   __opcode 15 13)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1990 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1990 <b 2032) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1991 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2032
                                                          let msz := (BitVec.slice __opcode 23 2)
                                                          let xs := (BitVec.slice __opcode 22 1)
                                                          let Zm := (BitVec.slice __opcode 16 5)
                                                          let U := (BitVec.slice __opcode 14 1)
                                                          let ff := (BitVec.slice __opcode 13 1)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                          (decode_LDFF1SW_Z_P_BZ_D_x32_unscaled msz
                                                            xs Zm U ff Pg Rn Zt)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1993 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b110001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 15 13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1992 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1992 <b 2033) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1993 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2033
                                                              let msz :=
                                                                (BitVec.slice __opcode 23 2)
                                                              let xs := (BitVec.slice __opcode 22 1)
                                                              let Zm := (BitVec.slice __opcode 16 5)
                                                              let U := (BitVec.slice __opcode 14 1)
                                                              let ff := (BitVec.slice __opcode 13 1)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                              (decode_LD1D_Z_P_BZ_D_x32_unscaled msz
                                                                xs Zm U ff Pg Rn Zt)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1995 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b110001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 15 13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1994 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1994 <b 2034) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1995 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2034
                                                                  let msz :=
                                                                    (BitVec.slice __opcode 23 2)
                                                                  let xs :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 14 1)
                                                                  let ff :=
                                                                    (BitVec.slice __opcode 13 1)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_LDFF1D_Z_P_BZ_D_x32_unscaled
                                                                    msz xs Zm U ff Pg Rn Zt)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1997 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b110001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1996 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1996 <b 2035) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1997 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2035
                                                                      let xs :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let msz :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let prfop :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_PRFB_I_P_BZ_D_x32_scaled
                                                                        xs Zm msz Pg Rn prfop)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1999 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b110001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1998 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1998 <b 2036) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1999 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2036
                                                                          let xs :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let msz :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let prfop :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_PRFH_I_P_BZ_D_x32_scaled
                                                                            xs Zm msz Pg Rn prfop)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__2001 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b110001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__2000 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__2000 <b 2037) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__2001 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2037
                                                                              let xs :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let msz :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let prfop :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_PRFW_I_P_BZ_D_x32_scaled
                                                                                xs Zm msz Pg Rn
                                                                                prfop)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__2003 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b110001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__2002 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__2002 <b 2038) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__2003 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2038
                                                                                  let xs :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let msz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let prfop :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_PRFD_I_P_BZ_D_x32_scaled
                                                                                    xs Zm msz Pg Rn
                                                                                    prfop)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__2005 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b110001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__2004 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__2004 <b 2039) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__2005 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2039
                                                                                      let xs :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          14 1)
                                                                                      let ff :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 1)
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
                                                                                      (decode_LD1H_Z_P_BZ_D_x32_scaled
                                                                                        xs Zm U ff
                                                                                        Pg Rn Zt)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__2007 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b110001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   13)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__2006 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__2006 <b 2040) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__2007 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2040
                                                                                          let xs :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              14 1)
                                                                                          let ff :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 1)
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
                                                                                          (decode_LD1SH_Z_P_BZ_D_x32_scaled
                                                                                            xs Zm U
                                                                                            ff Pg Rn
                                                                                            Zt)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__2009 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b110001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__2008 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__2008 <b 2041) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__2009 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2041
                                                                                              let xs :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  14
                                                                                                  1)
                                                                                              let ff :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  1)
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
                                                                                              (decode_LDFF1H_Z_P_BZ_D_x32_scaled
                                                                                                xs
                                                                                                Zm U
                                                                                                ff
                                                                                                Pg
                                                                                                Rn
                                                                                                Zt)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__2011 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b110001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           13)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__2010 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__2010 <b 2042) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__2011 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2042
                                                                                                  let xs :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      14
                                                                                                      1)
                                                                                                  let ff :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      1)
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
                                                                                                  (decode_LDFF1SH_Z_P_BZ_D_x32_scaled
                                                                                                    xs
                                                                                                    Zm
                                                                                                    U
                                                                                                    ff
                                                                                                    Pg
                                                                                                    Rn
                                                                                                    Zt)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__2013 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b110001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__2012 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__2012 <b 2043) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__2013 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2043
                                                                                                      let xs :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          14
                                                                                                          1)
                                                                                                      let ff :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          1)
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
                                                                                                      (decode_LD1W_Z_P_BZ_D_x32_scaled
                                                                                                        xs
                                                                                                        Zm
                                                                                                        U
                                                                                                        ff
                                                                                                        Pg
                                                                                                        Rn
                                                                                                        Zt)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__2015 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b110001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   13)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__2014 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__2014 <b 2044) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__2015 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2044
                                                                                                          let xs :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              14
                                                                                                              1)
                                                                                                          let ff :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              1)
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
                                                                                                          (decode_LD1SW_Z_P_BZ_D_x32_scaled
                                                                                                            xs
                                                                                                            Zm
                                                                                                            U
                                                                                                            ff
                                                                                                            Pg
                                                                                                            Rn
                                                                                                            Zt)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__2017 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b110001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__2016 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__2016 <b 2045) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__2017 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2045
                                                                                                              let xs :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  14
                                                                                                                  1)
                                                                                                              let ff :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  1)
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
                                                                                                              (decode_LDFF1W_Z_P_BZ_D_x32_scaled
                                                                                                                xs
                                                                                                                Zm
                                                                                                                U
                                                                                                                ff
                                                                                                                Pg
                                                                                                                Rn
                                                                                                                Zt)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__2019 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b110001010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           13)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__2018 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__2018 <b 2046) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__2019 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2046
                                                                                                                  let xs :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      14
                                                                                                                      1)
                                                                                                                  let ff :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      1)
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
                                                                                                                  (decode_LDFF1SW_Z_P_BZ_D_x32_scaled
                                                                                                                    xs
                                                                                                                    Zm
                                                                                                                    U
                                                                                                                    ff
                                                                                                                    Pg
                                                                                                                    Rn
                                                                                                                    Zt)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__2021 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             23)) == (0b110001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__2020 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__2020 <b 2047) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__2021 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2047
                                                                                                                      let xs :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let Zm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          14
                                                                                                                          1)
                                                                                                                      let ff :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          1)
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
                                                                                                                      (decode_LD1D_Z_P_BZ_D_x32_scaled
                                                                                                                        xs
                                                                                                                        Zm
                                                                                                                        U
                                                                                                                        ff
                                                                                                                        Pg
                                                                                                                        Rn
                                                                                                                        Zt)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__2023 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 23)) == (0b110001011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__2022 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__2022 <b 2048) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__2023 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2048
                                                                                                                          let xs :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              14
                                                                                                                              1)
                                                                                                                          let ff :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              1)
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
                                                                                                                          (decode_LDFF1D_Z_P_BZ_D_x32_scaled
                                                                                                                            xs
                                                                                                                            Zm
                                                                                                                            U
                                                                                                                            ff
                                                                                                                            Pg
                                                                                                                            Rn
                                                                                                                            Zt)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__2025 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b11000100000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       4
                                                                                                                                       4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__2024 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__2024 <b 2049) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__2025 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2049
                                                                                                                              let msz :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  23
                                                                                                                                  2)
                                                                                                                              let imm5 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
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
                                                                                                                              let prfop :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_PRFB_I_P_AI_D
                                                                                                                                msz
                                                                                                                                imm5
                                                                                                                                Pg
                                                                                                                                Zn
                                                                                                                                prfop)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__2027 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b11000100100#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           4
                                                                                                                                           4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__2026 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__2026 <b 2050) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__2027 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2050
                                                                                                                                  let msz :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      23
                                                                                                                                      2)
                                                                                                                                  let imm5 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
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
                                                                                                                                  let prfop :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  (decode_PRFH_I_P_AI_D
                                                                                                                                    msz
                                                                                                                                    imm5
                                                                                                                                    Pg
                                                                                                                                    Zn
                                                                                                                                    prfop)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__2029 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b11000101000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               4
                                                                                                                                               4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__2028 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__2028 <b 2051) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__2029 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2051
                                                                                                                                      let msz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          23
                                                                                                                                          2)
                                                                                                                                      let imm5 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
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
                                                                                                                                      let prfop :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      (decode_PRFW_I_P_AI_D
                                                                                                                                        msz
                                                                                                                                        imm5
                                                                                                                                        Pg
                                                                                                                                        Zn
                                                                                                                                        prfop)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))


end ArmFull.Functions
