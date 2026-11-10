import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0021
import ArmFull.Fn.M0049
import ArmFull.Fn.M0092
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0854

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

def decode_sev_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp (← occLabel 4021) ()) ) : SailM SystemHintOp )
  let op ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0000000 => (pure (SystemHintOp_NOP))
    | 0b0000001 => (pure (SystemHintOp_YIELD))
    | 0b0000010 => (pure (SystemHintOp_WFE))
    | 0b0000011 => (pure (SystemHintOp_WFI))
    | 0b0000100 => (pure (SystemHintOp_SEV))
    | 0b0000101 => (pure (SystemHintOp_SEVL))
    | 0b0000110 =>
      (do
        let w__0 ← (( do (HaveDGHExt ()) ) : SailM Bool )
        if ((! w__0) : Bool)
        then
          (do
            (EndOfInstruction ()))
        else (pure (()))
        (pure (SystemHintOp_DGH)))
    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (do
            match op2 with
            | 0b000 => sailThrow ((Error_See "PACIA1716"))
            | 0b010 => sailThrow ((Error_See "PACIB1716"))
            | 0b100 => sailThrow ((Error_See "AUTIA1716"))
            | 0b110 => sailThrow ((Error_See "AUTIB1716"))
            | _ =>
              (do
                (EndOfInstruction ()))
            (pure (op)))
        else
          (do
            match b__0 with
            | 0b0010000 =>
              (do
                let w__1 ← (( do (HaveRASExt ()) ) : SailM Bool )
                if ((! w__1) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_ESB)))
            | 0b0010001 =>
              (do
                let w__2 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
                if ((! w__2) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_PSB)))
            | 0b0010010 =>
              (do
                let w__3 ← (( do (HaveSelfHostedTrace ()) ) : SailM Bool )
                if ((! w__3) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_TSB)))
            | 0b0010011 =>
              (do
                let w__4 ← (( do (IsFeatureImplemented FEAT_GCS) ) : SailM Bool )
                if ((! w__4) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_GCSB)))
            | 0b0010100 => (pure (SystemHintOp_CSDB))
            | 0b0010110 =>
              (do
                let w__5 ← (( do (HaveFeatCLRBHB ()) ) : SailM Bool )
                if ((! w__5) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_CLRBHB)))
            | b__0 =>
              (do
                if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x3#4 : (BitVec 4))) : Bool)
                then
                  (do
                    match op2 with
                    | 0b000 => sailThrow ((Error_See "PACIAZ"))
                    | 0b001 => sailThrow ((Error_See "PACIASP"))
                    | 0b010 => sailThrow ((Error_See "PACIBZ"))
                    | 0b011 => sailThrow ((Error_See "PACIBSP"))
                    | 0b100 => sailThrow ((Error_See "AUTIAZ"))
                    | 0b101 => sailThrow ((Error_See "AUTIASP"))
                    | 0b110 => sailThrow ((Error_See "AUTIBZ"))
                    | _ => sailThrow ((Error_See "AUTIBSP"))
                    (pure (op)))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                    then
                      (do
                        let op : SystemHintOp := SystemHintOp_BTI
                        let w__6 ← (( do (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1)) )
                          : SailM Bool )
                        (SetBTypeCompatible w__6)
                        (pure (op)))
                    else
                      (do
                        match b__0 with
                        | 0b0101000 =>
                          (do
                            let w__7 ← (( do (IsFeatureImplemented FEAT_CHK) ) : SailM Bool )
                            if ((! w__7) : Bool)
                            then
                              (do
                                (EndOfInstruction ()))
                            else (pure (()))
                            (pure (SystemHintOp_CHKFEAT)))
                        | _ =>
                          (do
                            (EndOfInstruction ())
                            (pure (op)))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)


def decode_sevl_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp (← occLabel 4022) ()) ) : SailM SystemHintOp )
  let op ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0000000 => (pure (SystemHintOp_NOP))
    | 0b0000001 => (pure (SystemHintOp_YIELD))
    | 0b0000010 => (pure (SystemHintOp_WFE))
    | 0b0000011 => (pure (SystemHintOp_WFI))
    | 0b0000100 => (pure (SystemHintOp_SEV))
    | 0b0000101 => (pure (SystemHintOp_SEVL))
    | 0b0000110 =>
      (do
        let w__0 ← (( do (HaveDGHExt ()) ) : SailM Bool )
        if ((! w__0) : Bool)
        then
          (do
            (EndOfInstruction ()))
        else (pure (()))
        (pure (SystemHintOp_DGH)))
    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (do
            match op2 with
            | 0b000 => sailThrow ((Error_See "PACIA1716"))
            | 0b010 => sailThrow ((Error_See "PACIB1716"))
            | 0b100 => sailThrow ((Error_See "AUTIA1716"))
            | 0b110 => sailThrow ((Error_See "AUTIB1716"))
            | _ =>
              (do
                (EndOfInstruction ()))
            (pure (op)))
        else
          (do
            match b__0 with
            | 0b0010000 =>
              (do
                let w__1 ← (( do (HaveRASExt ()) ) : SailM Bool )
                if ((! w__1) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_ESB)))
            | 0b0010001 =>
              (do
                let w__2 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
                if ((! w__2) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_PSB)))
            | 0b0010010 =>
              (do
                let w__3 ← (( do (HaveSelfHostedTrace ()) ) : SailM Bool )
                if ((! w__3) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_TSB)))
            | 0b0010011 =>
              (do
                let w__4 ← (( do (IsFeatureImplemented FEAT_GCS) ) : SailM Bool )
                if ((! w__4) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_GCSB)))
            | 0b0010100 => (pure (SystemHintOp_CSDB))
            | 0b0010110 =>
              (do
                let w__5 ← (( do (HaveFeatCLRBHB ()) ) : SailM Bool )
                if ((! w__5) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_CLRBHB)))
            | b__0 =>
              (do
                if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x3#4 : (BitVec 4))) : Bool)
                then
                  (do
                    match op2 with
                    | 0b000 => sailThrow ((Error_See "PACIAZ"))
                    | 0b001 => sailThrow ((Error_See "PACIASP"))
                    | 0b010 => sailThrow ((Error_See "PACIBZ"))
                    | 0b011 => sailThrow ((Error_See "PACIBSP"))
                    | 0b100 => sailThrow ((Error_See "AUTIAZ"))
                    | 0b101 => sailThrow ((Error_See "AUTIASP"))
                    | 0b110 => sailThrow ((Error_See "AUTIBZ"))
                    | _ => sailThrow ((Error_See "AUTIBSP"))
                    (pure (op)))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                    then
                      (do
                        let op : SystemHintOp := SystemHintOp_BTI
                        let w__6 ← (( do (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1)) )
                          : SailM Bool )
                        (SetBTypeCompatible w__6)
                        (pure (op)))
                    else
                      (do
                        match b__0 with
                        | 0b0101000 =>
                          (do
                            let w__7 ← (( do (IsFeatureImplemented FEAT_CHK) ) : SailM Bool )
                            if ((! w__7) : Bool)
                            then
                              (do
                                (EndOfInstruction ()))
                            else (pure (()))
                            (pure (SystemHintOp_CHKFEAT)))
                        | _ =>
                          (do
                            (EndOfInstruction ())
                            (pure (op)))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)


def decode_tsb_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp (← occLabel 4023) ()) ) : SailM SystemHintOp )
  let op ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0000000 => (pure (SystemHintOp_NOP))
    | 0b0000001 => (pure (SystemHintOp_YIELD))
    | 0b0000010 => (pure (SystemHintOp_WFE))
    | 0b0000011 => (pure (SystemHintOp_WFI))
    | 0b0000100 => (pure (SystemHintOp_SEV))
    | 0b0000101 => (pure (SystemHintOp_SEVL))
    | 0b0000110 =>
      (do
        let w__0 ← (( do (HaveDGHExt ()) ) : SailM Bool )
        if ((! w__0) : Bool)
        then
          (do
            (EndOfInstruction ()))
        else (pure (()))
        (pure (SystemHintOp_DGH)))
    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (do
            match op2 with
            | 0b000 => sailThrow ((Error_See "PACIA1716"))
            | 0b010 => sailThrow ((Error_See "PACIB1716"))
            | 0b100 => sailThrow ((Error_See "AUTIA1716"))
            | 0b110 => sailThrow ((Error_See "AUTIB1716"))
            | _ =>
              (do
                (EndOfInstruction ()))
            (pure (op)))
        else
          (do
            match b__0 with
            | 0b0010000 =>
              (do
                let w__1 ← (( do (HaveRASExt ()) ) : SailM Bool )
                if ((! w__1) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_ESB)))
            | 0b0010001 =>
              (do
                let w__2 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
                if ((! w__2) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_PSB)))
            | 0b0010010 =>
              (do
                let w__3 ← (( do (HaveSelfHostedTrace ()) ) : SailM Bool )
                if ((! w__3) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_TSB)))
            | 0b0010011 =>
              (do
                let w__4 ← (( do (IsFeatureImplemented FEAT_GCS) ) : SailM Bool )
                if ((! w__4) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_GCSB)))
            | 0b0010100 => (pure (SystemHintOp_CSDB))
            | 0b0010110 =>
              (do
                let w__5 ← (( do (HaveFeatCLRBHB ()) ) : SailM Bool )
                if ((! w__5) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_CLRBHB)))
            | b__0 =>
              (do
                if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x3#4 : (BitVec 4))) : Bool)
                then
                  (do
                    match op2 with
                    | 0b000 => sailThrow ((Error_See "PACIAZ"))
                    | 0b001 => sailThrow ((Error_See "PACIASP"))
                    | 0b010 => sailThrow ((Error_See "PACIBZ"))
                    | 0b011 => sailThrow ((Error_See "PACIBSP"))
                    | 0b100 => sailThrow ((Error_See "AUTIAZ"))
                    | 0b101 => sailThrow ((Error_See "AUTIASP"))
                    | 0b110 => sailThrow ((Error_See "AUTIBZ"))
                    | _ => sailThrow ((Error_See "AUTIBSP"))
                    (pure (op)))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                    then
                      (do
                        let op : SystemHintOp := SystemHintOp_BTI
                        let w__6 ← (( do (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1)) )
                          : SailM Bool )
                        (SetBTypeCompatible w__6)
                        (pure (op)))
                    else
                      (do
                        match b__0 with
                        | 0b0101000 =>
                          (do
                            let w__7 ← (( do (IsFeatureImplemented FEAT_CHK) ) : SailM Bool )
                            if ((! w__7) : Bool)
                            then
                              (do
                                (EndOfInstruction ()))
                            else (pure (()))
                            (pure (SystemHintOp_CHKFEAT)))
                        | _ =>
                          (do
                            (EndOfInstruction ())
                            (pure (op)))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)


def decode_wfe_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp (← occLabel 4024) ()) ) : SailM SystemHintOp )
  let op ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0000000 => (pure (SystemHintOp_NOP))
    | 0b0000001 => (pure (SystemHintOp_YIELD))
    | 0b0000010 => (pure (SystemHintOp_WFE))
    | 0b0000011 => (pure (SystemHintOp_WFI))
    | 0b0000100 => (pure (SystemHintOp_SEV))
    | 0b0000101 => (pure (SystemHintOp_SEVL))
    | 0b0000110 =>
      (do
        let w__0 ← (( do (HaveDGHExt ()) ) : SailM Bool )
        if ((! w__0) : Bool)
        then
          (do
            (EndOfInstruction ()))
        else (pure (()))
        (pure (SystemHintOp_DGH)))
    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (do
            match op2 with
            | 0b000 => sailThrow ((Error_See "PACIA1716"))
            | 0b010 => sailThrow ((Error_See "PACIB1716"))
            | 0b100 => sailThrow ((Error_See "AUTIA1716"))
            | 0b110 => sailThrow ((Error_See "AUTIB1716"))
            | _ =>
              (do
                (EndOfInstruction ()))
            (pure (op)))
        else
          (do
            match b__0 with
            | 0b0010000 =>
              (do
                let w__1 ← (( do (HaveRASExt ()) ) : SailM Bool )
                if ((! w__1) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_ESB)))
            | 0b0010001 =>
              (do
                let w__2 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
                if ((! w__2) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_PSB)))
            | 0b0010010 =>
              (do
                let w__3 ← (( do (HaveSelfHostedTrace ()) ) : SailM Bool )
                if ((! w__3) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_TSB)))
            | 0b0010011 =>
              (do
                let w__4 ← (( do (IsFeatureImplemented FEAT_GCS) ) : SailM Bool )
                if ((! w__4) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_GCSB)))
            | 0b0010100 => (pure (SystemHintOp_CSDB))
            | 0b0010110 =>
              (do
                let w__5 ← (( do (HaveFeatCLRBHB ()) ) : SailM Bool )
                if ((! w__5) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_CLRBHB)))
            | b__0 =>
              (do
                if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x3#4 : (BitVec 4))) : Bool)
                then
                  (do
                    match op2 with
                    | 0b000 => sailThrow ((Error_See "PACIAZ"))
                    | 0b001 => sailThrow ((Error_See "PACIASP"))
                    | 0b010 => sailThrow ((Error_See "PACIBZ"))
                    | 0b011 => sailThrow ((Error_See "PACIBSP"))
                    | 0b100 => sailThrow ((Error_See "AUTIAZ"))
                    | 0b101 => sailThrow ((Error_See "AUTIASP"))
                    | 0b110 => sailThrow ((Error_See "AUTIBZ"))
                    | _ => sailThrow ((Error_See "AUTIBSP"))
                    (pure (op)))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                    then
                      (do
                        let op : SystemHintOp := SystemHintOp_BTI
                        let w__6 ← (( do (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1)) )
                          : SailM Bool )
                        (SetBTypeCompatible w__6)
                        (pure (op)))
                    else
                      (do
                        match b__0 with
                        | 0b0101000 =>
                          (do
                            let w__7 ← (( do (IsFeatureImplemented FEAT_CHK) ) : SailM Bool )
                            if ((! w__7) : Bool)
                            then
                              (do
                                (EndOfInstruction ()))
                            else (pure (()))
                            (pure (SystemHintOp_CHKFEAT)))
                        | _ =>
                          (do
                            (EndOfInstruction ())
                            (pure (op)))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)


def decode_wfi_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp (← occLabel 4025) ()) ) : SailM SystemHintOp )
  let op ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0000000 => (pure (SystemHintOp_NOP))
    | 0b0000001 => (pure (SystemHintOp_YIELD))
    | 0b0000010 => (pure (SystemHintOp_WFE))
    | 0b0000011 => (pure (SystemHintOp_WFI))
    | 0b0000100 => (pure (SystemHintOp_SEV))
    | 0b0000101 => (pure (SystemHintOp_SEVL))
    | 0b0000110 =>
      (do
        let w__0 ← (( do (HaveDGHExt ()) ) : SailM Bool )
        if ((! w__0) : Bool)
        then
          (do
            (EndOfInstruction ()))
        else (pure (()))
        (pure (SystemHintOp_DGH)))
    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x1#4 : (BitVec 4))) : Bool)
        then
          (do
            match op2 with
            | 0b000 => sailThrow ((Error_See "PACIA1716"))
            | 0b010 => sailThrow ((Error_See "PACIB1716"))
            | 0b100 => sailThrow ((Error_See "AUTIA1716"))
            | 0b110 => sailThrow ((Error_See "AUTIB1716"))
            | _ =>
              (do
                (EndOfInstruction ()))
            (pure (op)))
        else
          (do
            match b__0 with
            | 0b0010000 =>
              (do
                let w__1 ← (( do (HaveRASExt ()) ) : SailM Bool )
                if ((! w__1) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_ESB)))
            | 0b0010001 =>
              (do
                let w__2 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
                if ((! w__2) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_PSB)))
            | 0b0010010 =>
              (do
                let w__3 ← (( do (HaveSelfHostedTrace ()) ) : SailM Bool )
                if ((! w__3) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_TSB)))
            | 0b0010011 =>
              (do
                let w__4 ← (( do (IsFeatureImplemented FEAT_GCS) ) : SailM Bool )
                if ((! w__4) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_GCSB)))
            | 0b0010100 => (pure (SystemHintOp_CSDB))
            | 0b0010110 =>
              (do
                let w__5 ← (( do (HaveFeatCLRBHB ()) ) : SailM Bool )
                if ((! w__5) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                (pure (SystemHintOp_CLRBHB)))
            | b__0 =>
              (do
                if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x3#4 : (BitVec 4))) : Bool)
                then
                  (do
                    match op2 with
                    | 0b000 => sailThrow ((Error_See "PACIAZ"))
                    | 0b001 => sailThrow ((Error_See "PACIASP"))
                    | 0b010 => sailThrow ((Error_See "PACIBZ"))
                    | 0b011 => sailThrow ((Error_See "PACIBSP"))
                    | 0b100 => sailThrow ((Error_See "AUTIAZ"))
                    | 0b101 => sailThrow ((Error_See "AUTIASP"))
                    | 0b110 => sailThrow ((Error_See "AUTIBZ"))
                    | _ => sailThrow ((Error_See "AUTIBSP"))
                    (pure (op)))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 6 3)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                    then
                      (do
                        let op : SystemHintOp := SystemHintOp_BTI
                        let w__6 ← (( do (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1)) )
                          : SailM Bool )
                        (SetBTypeCompatible w__6)
                        (pure (op)))
                    else
                      (do
                        match b__0 with
                        | 0b0101000 =>
                          (do
                            let w__7 ← (( do (IsFeatureImplemented FEAT_CHK) ) : SailM Bool )
                            if ((! w__7) : Bool)
                            then
                              (do
                                (EndOfInstruction ()))
                            else (pure (()))
                            (pure (SystemHintOp_CHKFEAT)))
                        | _ =>
                          (do
                            (EndOfInstruction ())
                            (pure (op)))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)


end ArmFull.Functions
