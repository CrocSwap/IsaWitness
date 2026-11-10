import ObsGen.Clauses
import ObsGen.Architectural
/-! GENERATED provisional architectural mapping equations; no constant-time guarantee follows from these equations. -/
namespace ObsGen.ArchClauses
open Sail ArmFull ArmFull.Functions ObsGen
set_option linter.unusedVariables false
set_option maxHeartbeats 200000

def obs_abs_aarch64_instrs_integer_arithmetic_unary_abs (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_abs_aarch64_instrs_integer_arithmetic_unary_abs Rd Rn sf) s
theorem obs_abs_aarch64_instrs_integer_arithmetic_unary_abs_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_abs_aarch64_instrs_integer_arithmetic_unary_abs real Rd Rn sf s =
      Arch.project .clause s (stateOf ((decode_abs_aarch64_instrs_integer_arithmetic_unary_abs Rd Rn sf) s)) (Clauses.obs_abs_aarch64_instrs_integer_arithmetic_unary_abs real Rd Rn sf s) := rfl

def obs_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd Rd Rn size U Q) s
theorem obs_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd Rd Rn size U Q) s)) (Clauses.obs_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd real Rd Rn size U Q s) := rfl

def obs_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd Rd Rn size U) s
theorem obs_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd real Rd Rn size U s =
      Arch.project .clause s (stateOf ((decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd Rd Rn size U) s)) (Clauses.obs_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd real Rd Rn size U s) := rfl

def obs_adc_aarch64_instrs_integer_arithmetic_add_sub_carry (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf) s
theorem obs_adc_aarch64_instrs_integer_arithmetic_add_sub_carry_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_adc_aarch64_instrs_integer_arithmetic_add_sub_carry real Rd Rn Rm S op sf s =
      Arch.project .clause s (stateOf ((decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf) s)) (Clauses.obs_adc_aarch64_instrs_integer_arithmetic_add_sub_carry real Rd Rn Rm S op sf s) := rfl

def obs_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf) s
theorem obs_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry real Rd Rn Rm S op sf s =
      Arch.project .clause s (stateOf ((decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf) s)) (Clauses.obs_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry real Rd Rn Rm S op sf s) := rfl

def obs_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf) s
theorem obs_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg real Rd Rn imm3 option_name Rm S op sf s =
      Arch.project .clause s (stateOf ((decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf) s)) (Clauses.obs_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg real Rd Rn imm3 option_name Rm S op sf s) := rfl

def obs_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf) s
theorem obs_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate real Rd Rn imm12 sh S op sf s =
      Arch.project .clause s (stateOf ((decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf) s)) (Clauses.obs_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate real Rd Rn imm12 sh S op sf s) := rfl

def obs_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf) s
theorem obs_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg real Rd Rn imm6 Rm shift S op sf s =
      Arch.project .clause s (stateOf ((decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf) s)) (Clauses.obs_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg real Rd Rn imm6 Rm shift S op sf s) := rfl

def obs_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd Rd Rn Rm size U Q) s
theorem obs_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd Rd Rn Rm size U Q) s)) (Clauses.obs_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd real Rd Rn Rm size U Q s) := rfl

def obs_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd Rd Rn Rm size U) s
theorem obs_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd Rd Rn Rm size U) s)) (Clauses.obs_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd real Rd Rn Rm size U s) := rfl

def obs_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm size U Q) s
theorem obs_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm size U Q) s)) (Clauses.obs_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow real Rd Rn o1 Rm size U Q s) := rfl

def obs_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd Rd Rn size) s
theorem obs_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd real Rd Rn size s =
      Arch.project .clause s (stateOf ((decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd Rd Rn size) s)) (Clauses.obs_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd real Rd Rn size s) := rfl

def obs_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair Rd Rn Rm size Q) s
theorem obs_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair real Rd Rn Rm size Q s =
      Arch.project .clause s (stateOf ((decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair Rd Rn Rm size Q) s)) (Clauses.obs_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair real Rd Rn Rm size Q s) := rfl

def obs_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf) s
theorem obs_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg real Rd Rn imm3 option_name Rm S op sf s =
      Arch.project .clause s (stateOf ((decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf) s)) (Clauses.obs_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg real Rd Rn imm3 option_name Rm S op sf s) := rfl

def obs_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf) s
theorem obs_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate real Rd Rn imm12 sh S op sf s =
      Arch.project .clause s (stateOf ((decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf) s)) (Clauses.obs_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate real Rd Rn imm12 sh S op sf s) := rfl

def obs_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf) s
theorem obs_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg real Rd Rn imm6 Rm shift S op sf s =
      Arch.project .clause s (stateOf ((decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf) s)) (Clauses.obs_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg real Rd Rn imm6 Rm shift S op sf s) := rfl

def obs_addv_advsimd_aarch64_instrs_vector_reduce_add_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd Rd Rn size Q) s
theorem obs_addv_advsimd_aarch64_instrs_vector_reduce_add_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_addv_advsimd_aarch64_instrs_vector_reduce_add_simd real Rd Rn size Q s =
      Arch.project .clause s (stateOf ((decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd Rd Rn size Q) s)) (Clauses.obs_addv_advsimd_aarch64_instrs_vector_reduce_add_simd real Rd Rn size Q s) := rfl

def obs_adr_aarch64_instrs_integer_arithmetic_address_pc_rel (real : Type) [SailReal real] (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi immlo op) s
theorem obs_adr_aarch64_instrs_integer_arithmetic_address_pc_rel_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) (s : State) :
    obs_adr_aarch64_instrs_integer_arithmetic_address_pc_rel real Rd immhi immlo op s =
      Arch.project .clause s (stateOf ((decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi immlo op) s)) (Clauses.obs_adr_aarch64_instrs_integer_arithmetic_address_pc_rel real Rd immhi immlo op s) := rfl

def obs_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel (real : Type) [SailReal real] (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi immlo op) s
theorem obs_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) (s : State) :
    obs_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel real Rd immhi immlo op s =
      Arch.project .clause s (stateOf ((decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi immlo op) s)) (Clauses.obs_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel real Rd immhi immlo op s) := rfl

def obs_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round Rd Rn D) s
theorem obs_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) :
    obs_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round real Rd Rn D s =
      Arch.project .clause s (stateOf ((decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round Rd Rn D) s)) (Clauses.obs_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round real Rd Rn D s) := rfl

def obs_aese_advsimd_aarch64_instrs_vector_crypto_aes_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round Rd Rn D) s
theorem obs_aese_advsimd_aarch64_instrs_vector_crypto_aes_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) :
    obs_aese_advsimd_aarch64_instrs_vector_crypto_aes_round real Rd Rn D s =
      Arch.project .clause s (stateOf ((decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round Rd Rn D) s)) (Clauses.obs_aese_advsimd_aarch64_instrs_vector_crypto_aes_round real Rd Rn D s) := rfl

def obs_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix Rd Rn D) s
theorem obs_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) :
    obs_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix real Rd Rn D s =
      Arch.project .clause s (stateOf ((decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix Rd Rn D) s)) (Clauses.obs_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix real Rd Rn D s) := rfl

def obs_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix Rd Rn D) s
theorem obs_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) :
    obs_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix real Rd Rn D s =
      Arch.project .clause s (stateOf ((decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix Rd Rn D) s)) (Clauses.obs_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix real Rd Rn D s) := rfl

def obs_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size Q) s
theorem obs_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr real Rd Rn Rm size Q s =
      Arch.project .clause s (stateOf ((decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size Q) s)) (Clauses.obs_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr real Rd Rn Rm size Q s) := rfl

def obs_and_log_imm_aarch64_instrs_integer_logical_immediate (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf) s
theorem obs_and_log_imm_aarch64_instrs_integer_logical_immediate_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_and_log_imm_aarch64_instrs_integer_logical_immediate real Rd Rn imms immr N opc sf s =
      Arch.project .clause s (stateOf ((decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf) s)) (Clauses.obs_and_log_imm_aarch64_instrs_integer_logical_immediate real Rd Rn imms immr N opc sf s) := rfl

def obs_and_log_shift_aarch64_instrs_integer_logical_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s
theorem obs_and_log_shift_aarch64_instrs_integer_logical_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_and_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s =
      Arch.project .clause s (stateOf ((decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s)) (Clauses.obs_and_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s) := rfl

def obs_ands_log_imm_aarch64_instrs_integer_logical_immediate (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf) s
theorem obs_ands_log_imm_aarch64_instrs_integer_logical_immediate_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_ands_log_imm_aarch64_instrs_integer_logical_immediate real Rd Rn imms immr N opc sf s =
      Arch.project .clause s (stateOf ((decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf) s)) (Clauses.obs_ands_log_imm_aarch64_instrs_integer_logical_immediate real Rd Rn imms immr N opc sf s) := rfl

def obs_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s
theorem obs_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s =
      Arch.project .clause s (stateOf ((decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s)) (Clauses.obs_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s) := rfl

def obs_asrv_aarch64_instrs_integer_shift_variable (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_asrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf) s
theorem obs_asrv_aarch64_instrs_integer_shift_variable_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_asrv_aarch64_instrs_integer_shift_variable real Rd Rn op2 Rm sf s =
      Arch.project .clause s (stateOf ((decode_asrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf) s)) (Clauses.obs_asrv_aarch64_instrs_integer_shift_variable real Rd Rn op2 Rm sf s) := rfl

def obs_autda_aarch64_instrs_integer_pac_autda_dp_1src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_autda_aarch64_instrs_integer_pac_autda_dp_1src Rd Rn Z) s
theorem obs_autda_aarch64_instrs_integer_pac_autda_dp_1src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) :
    obs_autda_aarch64_instrs_integer_pac_autda_dp_1src real Rd Rn Z s =
      Arch.project .clause s (stateOf ((decode_autda_aarch64_instrs_integer_pac_autda_dp_1src Rd Rn Z) s)) (Clauses.obs_autda_aarch64_instrs_integer_pac_autda_dp_1src real Rd Rn Z s) := rfl

def obs_autdb_aarch64_instrs_integer_pac_autdb_dp_1src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_autdb_aarch64_instrs_integer_pac_autdb_dp_1src Rd Rn Z) s
theorem obs_autdb_aarch64_instrs_integer_pac_autdb_dp_1src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) :
    obs_autdb_aarch64_instrs_integer_pac_autdb_dp_1src real Rd Rn Z s =
      Arch.project .clause s (stateOf ((decode_autdb_aarch64_instrs_integer_pac_autdb_dp_1src Rd Rn Z) s)) (Clauses.obs_autdb_aarch64_instrs_integer_pac_autdb_dp_1src real Rd Rn Z s) := rfl

def obs_autia_aarch64_instrs_integer_pac_autia_dp_1src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_autia_aarch64_instrs_integer_pac_autia_dp_1src Rd Rn Z) s
theorem obs_autia_aarch64_instrs_integer_pac_autia_dp_1src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) :
    obs_autia_aarch64_instrs_integer_pac_autia_dp_1src real Rd Rn Z s =
      Arch.project .clause s (stateOf ((decode_autia_aarch64_instrs_integer_pac_autia_dp_1src Rd Rn Z) s)) (Clauses.obs_autia_aarch64_instrs_integer_pac_autia_dp_1src real Rd Rn Z s) := rfl

def obs_autia_aarch64_instrs_integer_pac_autia_hint (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_autia_aarch64_instrs_integer_pac_autia_hint op2 CRm) s
theorem obs_autia_aarch64_instrs_integer_pac_autia_hint_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_autia_aarch64_instrs_integer_pac_autia_hint real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_autia_aarch64_instrs_integer_pac_autia_hint op2 CRm) s)) (Clauses.obs_autia_aarch64_instrs_integer_pac_autia_hint real op2 CRm s) := rfl

def obs_autib_aarch64_instrs_integer_pac_autib_dp_1src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_autib_aarch64_instrs_integer_pac_autib_dp_1src Rd Rn Z) s
theorem obs_autib_aarch64_instrs_integer_pac_autib_dp_1src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) :
    obs_autib_aarch64_instrs_integer_pac_autib_dp_1src real Rd Rn Z s =
      Arch.project .clause s (stateOf ((decode_autib_aarch64_instrs_integer_pac_autib_dp_1src Rd Rn Z) s)) (Clauses.obs_autib_aarch64_instrs_integer_pac_autib_dp_1src real Rd Rn Z s) := rfl

def obs_autib_aarch64_instrs_integer_pac_autib_hint (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_autib_aarch64_instrs_integer_pac_autib_hint op2 CRm) s
theorem obs_autib_aarch64_instrs_integer_pac_autib_hint_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_autib_aarch64_instrs_integer_pac_autib_hint real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_autib_aarch64_instrs_integer_pac_autib_hint op2 CRm) s)) (Clauses.obs_autib_aarch64_instrs_integer_pac_autib_hint real op2 CRm s) := rfl

def obs_axflag_aarch64_instrs_integer_flags_axflag (real : Type) [SailReal real] (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_axflag_aarch64_instrs_integer_flags_axflag CRm) s
theorem obs_axflag_aarch64_instrs_integer_flags_axflag_mapping (real : Type) [SailReal real] (CRm : (BitVec 4)) (s : State) :
    obs_axflag_aarch64_instrs_integer_flags_axflag real CRm s =
      Arch.project .clause s (stateOf ((decode_axflag_aarch64_instrs_integer_flags_axflag CRm) s)) (Clauses.obs_axflag_aarch64_instrs_integer_flags_axflag real CRm s) := rfl

def obs_b_cond_aarch64_instrs_branch_conditional_cond (real : Type) [SailReal real] (cond : (BitVec 4)) (imm19 : (BitVec 19)) (s : State) : Arch.Observation :=
  Arch.observe (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19) s
theorem obs_b_cond_aarch64_instrs_branch_conditional_cond_mapping (real : Type) [SailReal real] (cond : (BitVec 4)) (imm19 : (BitVec 19)) (s : State) :
    obs_b_cond_aarch64_instrs_branch_conditional_cond real cond imm19 s =
      Arch.project .clause s (stateOf ((decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19) s)) (Clauses.obs_b_cond_aarch64_instrs_branch_conditional_cond real cond imm19 s) := rfl

def obs_b_uncond_aarch64_instrs_branch_unconditional_immediate (real : Type) [SailReal real] (imm26 : (BitVec 26)) (op : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 op) s
theorem obs_b_uncond_aarch64_instrs_branch_unconditional_immediate_mapping (real : Type) [SailReal real] (imm26 : (BitVec 26)) (op : (BitVec 1)) (s : State) :
    obs_b_uncond_aarch64_instrs_branch_unconditional_immediate real imm26 op s =
      Arch.project .clause s (stateOf ((decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 op) s)) (Clauses.obs_b_uncond_aarch64_instrs_branch_unconditional_immediate real imm26 op s) := rfl

def obs_bc_cond_aarch64_instrs_branch_conditional_hinted (real : Type) [SailReal real] (cond : (BitVec 4)) (imm19 : (BitVec 19)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bc_cond_aarch64_instrs_branch_conditional_hinted cond imm19) s
theorem obs_bc_cond_aarch64_instrs_branch_conditional_hinted_mapping (real : Type) [SailReal real] (cond : (BitVec 4)) (imm19 : (BitVec 19)) (s : State) :
    obs_bc_cond_aarch64_instrs_branch_conditional_hinted real cond imm19 s =
      Arch.project .clause s (stateOf ((decode_bc_cond_aarch64_instrs_branch_conditional_hinted cond imm19) s)) (Clauses.obs_bc_cond_aarch64_instrs_branch_conditional_hinted real cond imm19 s) := rfl

def obs_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax Rd Rn Ra Rm) s
theorem obs_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax real Rd Rn Ra Rm s =
      Arch.project .clause s (stateOf ((decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax Rd Rn Ra Rm) s)) (Clauses.obs_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax real Rd Rn Ra Rm s) := rfl

def obs_bfm_aarch64_instrs_integer_bitfield (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc sf) s
theorem obs_bfm_aarch64_instrs_integer_bitfield_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_bfm_aarch64_instrs_integer_bitfield real Rd Rn imms immr N opc sf s =
      Arch.project .clause s (stateOf ((decode_bfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc sf) s)) (Clauses.obs_bfm_aarch64_instrs_integer_bitfield real Rd Rn imms immr N opc sf s) := rfl

def obs_bic_advsimd_imm_aarch64_instrs_vector_logical (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bic_advsimd_imm_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s
theorem obs_bic_advsimd_imm_aarch64_instrs_vector_logical_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_bic_advsimd_imm_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s =
      Arch.project .clause s (stateOf ((decode_bic_advsimd_imm_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s)) (Clauses.obs_bic_advsimd_imm_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s) := rfl

def obs_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size Q) s
theorem obs_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr real Rd Rn Rm size Q s =
      Arch.project .clause s (stateOf ((decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size Q) s)) (Clauses.obs_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr real Rd Rn Rm size Q s) := rfl

def obs_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s
theorem obs_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s =
      Arch.project .clause s (stateOf ((decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s)) (Clauses.obs_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s) := rfl

def obs_bics_aarch64_instrs_integer_logical_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bics_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s
theorem obs_bics_aarch64_instrs_integer_logical_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_bics_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s =
      Arch.project .clause s (stateOf ((decode_bics_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s)) (Clauses.obs_bics_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s) := rfl

def obs_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 Q) s
theorem obs_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor real Rd Rn Rm opc2 Q s =
      Arch.project .clause s (stateOf ((decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 Q) s)) (Clauses.obs_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor real Rd Rn Rm opc2 Q s) := rfl

def obs_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 Q) s
theorem obs_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor real Rd Rn Rm opc2 Q s =
      Arch.project .clause s (stateOf ((decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 Q) s)) (Clauses.obs_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor real Rd Rn Rm opc2 Q s) := rfl

def obs_bl_aarch64_instrs_branch_unconditional_immediate (real : Type) [SailReal real] (imm26 : (BitVec 26)) (op : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 op) s
theorem obs_bl_aarch64_instrs_branch_unconditional_immediate_mapping (real : Type) [SailReal real] (imm26 : (BitVec 26)) (op : (BitVec 1)) (s : State) :
    obs_bl_aarch64_instrs_branch_unconditional_immediate real imm26 op s =
      Arch.project .clause s (stateOf ((decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 op) s)) (Clauses.obs_bl_aarch64_instrs_branch_unconditional_immediate real imm26 op s) := rfl

def obs_blr_aarch64_instrs_branch_unconditional_register (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_blr_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s
theorem obs_blr_aarch64_instrs_branch_unconditional_register_mapping (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) :
    obs_blr_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s =
      Arch.project .clause s (stateOf ((decode_blr_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s)) (Clauses.obs_blr_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s) := rfl

def obs_blra_aarch64_instrs_branch_unconditional_register (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_blra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s
theorem obs_blra_aarch64_instrs_branch_unconditional_register_mapping (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) :
    obs_blra_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s =
      Arch.project .clause s (stateOf ((decode_blra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s)) (Clauses.obs_blra_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s) := rfl

def obs_br_aarch64_instrs_branch_unconditional_register (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_br_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s
theorem obs_br_aarch64_instrs_branch_unconditional_register_mapping (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) :
    obs_br_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s =
      Arch.project .clause s (stateOf ((decode_br_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s)) (Clauses.obs_br_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s) := rfl

def obs_bra_aarch64_instrs_branch_unconditional_register (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s
theorem obs_bra_aarch64_instrs_branch_unconditional_register_mapping (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) :
    obs_bra_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s =
      Arch.project .clause s (stateOf ((decode_bra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s)) (Clauses.obs_bra_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s) := rfl

def obs_brk_aarch64_instrs_system_exceptions_debug_breakpoint (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) : Arch.Observation :=
  Arch.observe (decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint imm16) s
theorem obs_brk_aarch64_instrs_system_exceptions_debug_breakpoint_mapping (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) :
    obs_brk_aarch64_instrs_system_exceptions_debug_breakpoint real imm16 s =
      Arch.project .clause s (stateOf ((decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint imm16) s)) (Clauses.obs_brk_aarch64_instrs_system_exceptions_debug_breakpoint real imm16 s) := rfl

def obs_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 Q) s
theorem obs_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor real Rd Rn Rm opc2 Q s =
      Arch.project .clause s (stateOf ((decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 Q) s)) (Clauses.obs_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor real Rd Rn Rm opc2 Q s) := rfl

def obs_bti_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_bti_aarch64_instrs_system_hints op2 CRm) s
theorem obs_bti_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_bti_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_bti_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_bti_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_cas_aarch64_instrs_memory_atomicops_cas_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cas_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L size) s
theorem obs_cas_aarch64_instrs_memory_atomicops_cas_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_cas_aarch64_instrs_memory_atomicops_cas_single real Rt Rn o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_cas_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L size) s)) (Clauses.obs_cas_aarch64_instrs_memory_atomicops_cas_single real Rt Rn o0 Rs L size s) := rfl

def obs_casb_aarch64_instrs_memory_atomicops_cas_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_casb_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L size) s
theorem obs_casb_aarch64_instrs_memory_atomicops_cas_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_casb_aarch64_instrs_memory_atomicops_cas_single real Rt Rn o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_casb_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L size) s)) (Clauses.obs_casb_aarch64_instrs_memory_atomicops_cas_single real Rt Rn o0 Rs L size s) := rfl

def obs_cash_aarch64_instrs_memory_atomicops_cas_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cash_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L size) s
theorem obs_cash_aarch64_instrs_memory_atomicops_cas_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_cash_aarch64_instrs_memory_atomicops_cas_single real Rt Rn o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_cash_aarch64_instrs_memory_atomicops_cas_single Rt Rn o0 Rs L size) s)) (Clauses.obs_cash_aarch64_instrs_memory_atomicops_cas_single real Rt Rn o0 Rs L size s) := rfl

def obs_cbnz_aarch64_instrs_branch_conditional_compare (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf) s
theorem obs_cbnz_aarch64_instrs_branch_conditional_compare_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_cbnz_aarch64_instrs_branch_conditional_compare real Rt imm19 op sf s =
      Arch.project .clause s (stateOf ((decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf) s)) (Clauses.obs_cbnz_aarch64_instrs_branch_conditional_compare real Rt imm19 op sf s) := rfl

def obs_cbz_aarch64_instrs_branch_conditional_compare (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf) s
theorem obs_cbz_aarch64_instrs_branch_conditional_compare_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_cbz_aarch64_instrs_branch_conditional_compare real Rt imm19 op sf s =
      Arch.project .clause s (stateOf ((decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf) s)) (Clauses.obs_cbz_aarch64_instrs_branch_conditional_compare real Rt imm19 op sf s) := rfl

def obs_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate (real : Type) [SailReal real] (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op sf) s
theorem obs_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate_mapping (real : Type) [SailReal real] (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate real nzcv Rn cond imm5 op sf s =
      Arch.project .clause s (stateOf ((decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op sf) s)) (Clauses.obs_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate real nzcv Rn cond imm5 op sf s) := rfl

def obs_ccmn_reg_aarch64_instrs_integer_conditional_compare_register (real : Type) [SailReal real] (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op sf) s
theorem obs_ccmn_reg_aarch64_instrs_integer_conditional_compare_register_mapping (real : Type) [SailReal real] (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_ccmn_reg_aarch64_instrs_integer_conditional_compare_register real nzcv Rn cond Rm op sf s =
      Arch.project .clause s (stateOf ((decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op sf) s)) (Clauses.obs_ccmn_reg_aarch64_instrs_integer_conditional_compare_register real nzcv Rn cond Rm op sf s) := rfl

def obs_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate (real : Type) [SailReal real] (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op sf) s
theorem obs_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate_mapping (real : Type) [SailReal real] (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate real nzcv Rn cond imm5 op sf s =
      Arch.project .clause s (stateOf ((decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op sf) s)) (Clauses.obs_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate real nzcv Rn cond imm5 op sf s) := rfl

def obs_ccmp_reg_aarch64_instrs_integer_conditional_compare_register (real : Type) [SailReal real] (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op sf) s
theorem obs_ccmp_reg_aarch64_instrs_integer_conditional_compare_register_mapping (real : Type) [SailReal real] (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_ccmp_reg_aarch64_instrs_integer_conditional_compare_register real nzcv Rn cond Rm op sf s =
      Arch.project .clause s (stateOf ((decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op sf) s)) (Clauses.obs_ccmp_reg_aarch64_instrs_integer_conditional_compare_register real nzcv Rn cond Rm op sf s) := rfl

def obs_cfinv_aarch64_instrs_integer_flags_cfinv (real : Type) [SailReal real] (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cfinv_aarch64_instrs_integer_flags_cfinv CRm) s
theorem obs_cfinv_aarch64_instrs_integer_flags_cfinv_mapping (real : Type) [SailReal real] (CRm : (BitVec 4)) (s : State) :
    obs_cfinv_aarch64_instrs_integer_flags_cfinv real CRm s =
      Arch.project .clause s (stateOf ((decode_cfinv_aarch64_instrs_integer_flags_cfinv CRm) s)) (Clauses.obs_cfinv_aarch64_instrs_integer_flags_cfinv real CRm s) := rfl

def obs_chkfeat_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_chkfeat_aarch64_instrs_system_hints op2 CRm) s
theorem obs_chkfeat_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_chkfeat_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_chkfeat_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_chkfeat_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_clrbhb_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_clrbhb_aarch64_instrs_system_hints op2 CRm) s
theorem obs_clrbhb_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_clrbhb_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_clrbhb_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_clrbhb_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn size U Q) s
theorem obs_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn size U Q) s)) (Clauses.obs_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz real Rd Rn size U Q s) := rfl

def obs_cls_int_aarch64_instrs_integer_arithmetic_cnt (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cls_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op sf) s
theorem obs_cls_int_aarch64_instrs_integer_arithmetic_cnt_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_cls_int_aarch64_instrs_integer_arithmetic_cnt real Rd Rn op sf s =
      Arch.project .clause s (stateOf ((decode_cls_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op sf) s)) (Clauses.obs_cls_int_aarch64_instrs_integer_arithmetic_cnt real Rd Rn op sf s) := rfl

def obs_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn size U Q) s
theorem obs_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz Rd Rn size U Q) s)) (Clauses.obs_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz real Rd Rn size U Q s) := rfl

def obs_clz_int_aarch64_instrs_integer_arithmetic_cnt (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_clz_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op sf) s
theorem obs_clz_int_aarch64_instrs_integer_arithmetic_cnt_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_clz_int_aarch64_instrs_integer_arithmetic_cnt real Rd Rn op sf s =
      Arch.project .clause s (stateOf ((decode_clz_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op sf) s)) (Clauses.obs_clz_int_aarch64_instrs_integer_arithmetic_cnt real Rd Rn op sf s) := rfl

def obs_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd Rd Rn Rm size U Q) s
theorem obs_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd Rd Rn Rm size U Q) s)) (Clauses.obs_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd real Rd Rn Rm size U Q s) := rfl

def obs_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd Rd Rn Rm size U) s
theorem obs_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd Rd Rn Rm size U) s)) (Clauses.obs_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd real Rd Rn Rm size U s) := rfl

def obs_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op size U Q) s
theorem obs_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op size U Q) s)) (Clauses.obs_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd real Rd Rn op size U Q s) := rfl

def obs_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op size U) s
theorem obs_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd real Rd Rn op size U s =
      Arch.project .clause s (stateOf ((decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op size U) s)) (Clauses.obs_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd real Rd Rn op size U s) := rfl

def obs_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm size U Q) s
theorem obs_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd real Rd Rn eq Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm size U Q) s)) (Clauses.obs_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd real Rd Rn eq Rm size U Q s) := rfl

def obs_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm size U) s
theorem obs_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd real Rd Rn eq Rm size U s =
      Arch.project .clause s (stateOf ((decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm size U) s)) (Clauses.obs_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd real Rd Rn eq Rm size U s) := rfl

def obs_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op size U Q) s
theorem obs_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op size U Q) s)) (Clauses.obs_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd real Rd Rn op size U Q s) := rfl

def obs_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op size U) s
theorem obs_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd real Rd Rn op size U s =
      Arch.project .clause s (stateOf ((decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op size U) s)) (Clauses.obs_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd real Rd Rn op size U s) := rfl

def obs_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm size U Q) s
theorem obs_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd real Rd Rn eq Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm size U Q) s)) (Clauses.obs_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd real Rd Rn eq Rm size U Q s) := rfl

def obs_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm size U) s
theorem obs_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd real Rd Rn eq Rm size U s =
      Arch.project .clause s (stateOf ((decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm size U) s)) (Clauses.obs_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd real Rd Rn eq Rm size U s) := rfl

def obs_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op size U Q) s
theorem obs_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op size U Q) s)) (Clauses.obs_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd real Rd Rn op size U Q s) := rfl

def obs_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op size U) s
theorem obs_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd real Rd Rn op size U s =
      Arch.project .clause s (stateOf ((decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op size U) s)) (Clauses.obs_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd real Rd Rn op size U s) := rfl

def obs_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm size U Q) s
theorem obs_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd real Rd Rn eq Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm size U Q) s)) (Clauses.obs_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd real Rd Rn eq Rm size U Q s) := rfl

def obs_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm size U) s
theorem obs_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd real Rd Rn eq Rm size U s =
      Arch.project .clause s (stateOf ((decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm size U) s)) (Clauses.obs_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd real Rd Rn eq Rm size U s) := rfl

def obs_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm size U Q) s
theorem obs_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd real Rd Rn eq Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd Rd Rn eq Rm size U Q) s)) (Clauses.obs_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd real Rd Rn eq Rm size U Q s) := rfl

def obs_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm size U) s
theorem obs_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd real Rd Rn eq Rm size U s =
      Arch.project .clause s (stateOf ((decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd Rd Rn eq Rm size U) s)) (Clauses.obs_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd real Rd Rn eq Rm size U s) := rfl

def obs_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op size U Q) s
theorem obs_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd Rd Rn op size U Q) s)) (Clauses.obs_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd real Rd Rn op size U Q s) := rfl

def obs_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op size U) s
theorem obs_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd real Rd Rn op size U s =
      Arch.project .clause s (stateOf ((decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd Rd Rn op size U) s)) (Clauses.obs_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd real Rd Rn op size U s) := rfl

def obs_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd Rd Rn size Q) s
theorem obs_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd real Rd Rn size Q s =
      Arch.project .clause s (stateOf ((decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd Rd Rn size Q) s)) (Clauses.obs_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd real Rd Rn size Q s) := rfl

def obs_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd Rd Rn size) s
theorem obs_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd real Rd Rn size s =
      Arch.project .clause s (stateOf ((decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd Rd Rn size) s)) (Clauses.obs_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd real Rd Rn size s) := rfl

def obs_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd Rd Rn Rm size U Q) s
theorem obs_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd Rd Rn Rm size U Q) s)) (Clauses.obs_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd real Rd Rn Rm size U Q s) := rfl

def obs_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd Rd Rn Rm size U) s
theorem obs_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd Rd Rn Rm size U) s)) (Clauses.obs_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd real Rd Rn Rm size U s) := rfl

def obs_cnt_aarch64_instrs_integer_arithmetic_unary_cnt (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cnt_aarch64_instrs_integer_arithmetic_unary_cnt Rd Rn sf) s
theorem obs_cnt_aarch64_instrs_integer_arithmetic_unary_cnt_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_cnt_aarch64_instrs_integer_arithmetic_unary_cnt real Rd Rn sf s =
      Arch.project .clause s (stateOf ((decode_cnt_aarch64_instrs_integer_arithmetic_unary_cnt Rd Rn sf) s)) (Clauses.obs_cnt_aarch64_instrs_integer_arithmetic_unary_cnt real Rd Rn sf s) := rfl

def obs_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt Rd Rn size Q) s
theorem obs_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt real Rd Rn size Q s =
      Arch.project .clause s (stateOf ((decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt Rd Rn size Q) s)) (Clauses.obs_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt real Rd Rn size Q s) := rfl

def obs_crc32_aarch64_instrs_integer_crc (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_crc32_aarch64_instrs_integer_crc Rd Rn sz C Rm sf) s
theorem obs_crc32_aarch64_instrs_integer_crc_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_crc32_aarch64_instrs_integer_crc real Rd Rn sz C Rm sf s =
      Arch.project .clause s (stateOf ((decode_crc32_aarch64_instrs_integer_crc Rd Rn sz C Rm sf) s)) (Clauses.obs_crc32_aarch64_instrs_integer_crc real Rd Rn sz C Rm sf s) := rfl

def obs_crc32c_aarch64_instrs_integer_crc (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_crc32c_aarch64_instrs_integer_crc Rd Rn sz C Rm sf) s
theorem obs_crc32c_aarch64_instrs_integer_crc_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_crc32c_aarch64_instrs_integer_crc real Rd Rn sz C Rm sf s =
      Arch.project .clause s (stateOf ((decode_crc32c_aarch64_instrs_integer_crc Rd Rn sz C Rm sf) s)) (Clauses.obs_crc32c_aarch64_instrs_integer_crc real Rd Rn sz C Rm sf s) := rfl

def obs_csdb_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_csdb_aarch64_instrs_system_hints op2 CRm) s
theorem obs_csdb_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_csdb_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_csdb_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_csdb_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_csel_aarch64_instrs_integer_conditional_select (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf) s
theorem obs_csel_aarch64_instrs_integer_conditional_select_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_csel_aarch64_instrs_integer_conditional_select real Rd Rn o2 cond Rm op sf s =
      Arch.project .clause s (stateOf ((decode_csel_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf) s)) (Clauses.obs_csel_aarch64_instrs_integer_conditional_select real Rd Rn o2 cond Rm op sf s) := rfl

def obs_csinc_aarch64_instrs_integer_conditional_select (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf) s
theorem obs_csinc_aarch64_instrs_integer_conditional_select_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_csinc_aarch64_instrs_integer_conditional_select real Rd Rn o2 cond Rm op sf s =
      Arch.project .clause s (stateOf ((decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf) s)) (Clauses.obs_csinc_aarch64_instrs_integer_conditional_select real Rd Rn o2 cond Rm op sf s) := rfl

def obs_csinv_aarch64_instrs_integer_conditional_select (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf) s
theorem obs_csinv_aarch64_instrs_integer_conditional_select_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_csinv_aarch64_instrs_integer_conditional_select real Rd Rn o2 cond Rm op sf s =
      Arch.project .clause s (stateOf ((decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf) s)) (Clauses.obs_csinv_aarch64_instrs_integer_conditional_select real Rd Rn o2 cond Rm op sf s) := rfl

def obs_csneg_aarch64_instrs_integer_conditional_select (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_csneg_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf) s
theorem obs_csneg_aarch64_instrs_integer_conditional_select_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_csneg_aarch64_instrs_integer_conditional_select real Rd Rn o2 cond Rm op sf s =
      Arch.project .clause s (stateOf ((decode_csneg_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf) s)) (Clauses.obs_csneg_aarch64_instrs_integer_conditional_select real Rd Rn o2 cond Rm op sf s) := rfl

def obs_ctz_aarch64_instrs_integer_arithmetic_unary_ctz (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ctz_aarch64_instrs_integer_arithmetic_unary_ctz Rd Rn sf) s
theorem obs_ctz_aarch64_instrs_integer_arithmetic_unary_ctz_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_ctz_aarch64_instrs_integer_arithmetic_unary_ctz real Rd Rn sf s =
      Arch.project .clause s (stateOf ((decode_ctz_aarch64_instrs_integer_arithmetic_unary_ctz Rd Rn sf) s)) (Clauses.obs_ctz_aarch64_instrs_integer_arithmetic_unary_ctz real Rd Rn sf s) := rfl

def obs_dcps1_aarch64_instrs_system_exceptions_debug_exception (real : Type) [SailReal real] (LL : (BitVec 2)) (imm16 : (BitVec 16)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dcps1_aarch64_instrs_system_exceptions_debug_exception LL imm16) s
theorem obs_dcps1_aarch64_instrs_system_exceptions_debug_exception_mapping (real : Type) [SailReal real] (LL : (BitVec 2)) (imm16 : (BitVec 16)) (s : State) :
    obs_dcps1_aarch64_instrs_system_exceptions_debug_exception real LL imm16 s =
      Arch.project .clause s (stateOf ((decode_dcps1_aarch64_instrs_system_exceptions_debug_exception LL imm16) s)) (Clauses.obs_dcps1_aarch64_instrs_system_exceptions_debug_exception real LL imm16 s) := rfl

def obs_dcps2_aarch64_instrs_system_exceptions_debug_exception (real : Type) [SailReal real] (LL : (BitVec 2)) (imm16 : (BitVec 16)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dcps2_aarch64_instrs_system_exceptions_debug_exception LL imm16) s
theorem obs_dcps2_aarch64_instrs_system_exceptions_debug_exception_mapping (real : Type) [SailReal real] (LL : (BitVec 2)) (imm16 : (BitVec 16)) (s : State) :
    obs_dcps2_aarch64_instrs_system_exceptions_debug_exception real LL imm16 s =
      Arch.project .clause s (stateOf ((decode_dcps2_aarch64_instrs_system_exceptions_debug_exception LL imm16) s)) (Clauses.obs_dcps2_aarch64_instrs_system_exceptions_debug_exception real LL imm16 s) := rfl

def obs_dcps3_aarch64_instrs_system_exceptions_debug_exception (real : Type) [SailReal real] (LL : (BitVec 2)) (imm16 : (BitVec 16)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dcps3_aarch64_instrs_system_exceptions_debug_exception LL imm16) s
theorem obs_dcps3_aarch64_instrs_system_exceptions_debug_exception_mapping (real : Type) [SailReal real] (LL : (BitVec 2)) (imm16 : (BitVec 16)) (s : State) :
    obs_dcps3_aarch64_instrs_system_exceptions_debug_exception real LL imm16 s =
      Arch.project .clause s (stateOf ((decode_dcps3_aarch64_instrs_system_exceptions_debug_exception LL imm16) s)) (Clauses.obs_dcps3_aarch64_instrs_system_exceptions_debug_exception real LL imm16 s) := rfl

def obs_dgh_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dgh_aarch64_instrs_system_hints op2 CRm) s
theorem obs_dgh_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_dgh_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_dgh_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_dgh_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_dmb_aarch64_instrs_system_barriers_dmb (real : Type) [SailReal real] (opc : (BitVec 2)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dmb_aarch64_instrs_system_barriers_dmb opc CRm) s
theorem obs_dmb_aarch64_instrs_system_barriers_dmb_mapping (real : Type) [SailReal real] (opc : (BitVec 2)) (CRm : (BitVec 4)) (s : State) :
    obs_dmb_aarch64_instrs_system_barriers_dmb real opc CRm s =
      Arch.project .clause s (stateOf ((decode_dmb_aarch64_instrs_system_barriers_dmb opc CRm) s)) (Clauses.obs_dmb_aarch64_instrs_system_barriers_dmb real opc CRm s) := rfl

def obs_drps_aarch64_instrs_branch_unconditional_dret (real : Type) [SailReal real] (obs_unit : Unit) (s : State) : Arch.Observation :=
  Arch.observe (decode_drps_aarch64_instrs_branch_unconditional_dret obs_unit) s
theorem obs_drps_aarch64_instrs_branch_unconditional_dret_mapping (real : Type) [SailReal real] (obs_unit : Unit) (s : State) :
    obs_drps_aarch64_instrs_branch_unconditional_dret real obs_unit s =
      Arch.project .clause s (stateOf ((decode_drps_aarch64_instrs_branch_unconditional_dret obs_unit) s)) (Clauses.obs_drps_aarch64_instrs_branch_unconditional_dret real obs_unit s) := rfl

def obs_dsb_aarch64_instrs_system_barriers_dsb (real : Type) [SailReal real] (opc : (BitVec 2)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dsb_aarch64_instrs_system_barriers_dsb opc CRm) s
theorem obs_dsb_aarch64_instrs_system_barriers_dsb_mapping (real : Type) [SailReal real] (opc : (BitVec 2)) (CRm : (BitVec 4)) (s : State) :
    obs_dsb_aarch64_instrs_system_barriers_dsb real opc CRm s =
      Arch.project .clause s (stateOf ((decode_dsb_aarch64_instrs_system_barriers_dsb opc CRm) s)) (Clauses.obs_dsb_aarch64_instrs_system_barriers_dsb real opc CRm s) := rfl

def obs_dsb_aarch64_instrs_system_barriers_dsb_nxs (real : Type) [SailReal real] (imm2 : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dsb_aarch64_instrs_system_barriers_dsb_nxs imm2) s
theorem obs_dsb_aarch64_instrs_system_barriers_dsb_nxs_mapping (real : Type) [SailReal real] (imm2 : (BitVec 2)) (s : State) :
    obs_dsb_aarch64_instrs_system_barriers_dsb_nxs real imm2 s =
      Arch.project .clause s (stateOf ((decode_dsb_aarch64_instrs_system_barriers_dsb_nxs imm2) s)) (Clauses.obs_dsb_aarch64_instrs_system_barriers_dsb_nxs real imm2 s) := rfl

def obs_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd Rd Rn imm5 Q) s
theorem obs_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd real Rd Rn imm5 Q s =
      Arch.project .clause s (stateOf ((decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd Rd Rn imm5 Q) s)) (Clauses.obs_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd real Rd Rn imm5 Q s) := rfl

def obs_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd Rd Rn imm5) s
theorem obs_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (s : State) :
    obs_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd real Rd Rn imm5 s =
      Arch.project .clause s (stateOf ((decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd Rd Rn imm5) s)) (Clauses.obs_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd real Rd Rn imm5 s) := rfl

def obs_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup Rd Rn imm5 Q) s
theorem obs_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup real Rd Rn imm5 Q s =
      Arch.project .clause s (stateOf ((decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup Rd Rn imm5 Q) s)) (Clauses.obs_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup real Rd Rn imm5 Q s) := rfl

def obs_eon_aarch64_instrs_integer_logical_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_eon_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s
theorem obs_eon_aarch64_instrs_integer_logical_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_eon_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s =
      Arch.project .clause s (stateOf ((decode_eon_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s)) (Clauses.obs_eon_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s) := rfl

def obs_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3 Rd Rn Ra Rm) s
theorem obs_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3 real Rd Rn Ra Rm s =
      Arch.project .clause s (stateOf ((decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3 Rd Rn Ra Rm) s)) (Clauses.obs_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3 real Rd Rn Ra Rm s) := rfl

def obs_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 Q) s
theorem obs_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor real Rd Rn Rm opc2 Q s =
      Arch.project .clause s (stateOf ((decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor Rd Rn Rm opc2 Q) s)) (Clauses.obs_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor real Rd Rn Rm opc2 Q s) := rfl

def obs_eor_log_imm_aarch64_instrs_integer_logical_immediate (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_eor_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf) s
theorem obs_eor_log_imm_aarch64_instrs_integer_logical_immediate_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_eor_log_imm_aarch64_instrs_integer_logical_immediate real Rd Rn imms immr N opc sf s =
      Arch.project .clause s (stateOf ((decode_eor_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf) s)) (Clauses.obs_eor_log_imm_aarch64_instrs_integer_logical_immediate real Rd Rn imms immr N opc sf s) := rfl

def obs_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s
theorem obs_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s =
      Arch.project .clause s (stateOf ((decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s)) (Clauses.obs_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s) := rfl

def obs_eret_aarch64_instrs_branch_unconditional_eret (real : Type) [SailReal real] (op4 : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_eret_aarch64_instrs_branch_unconditional_eret op4 Rn M A) s
theorem obs_eret_aarch64_instrs_branch_unconditional_eret_mapping (real : Type) [SailReal real] (op4 : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (s : State) :
    obs_eret_aarch64_instrs_branch_unconditional_eret real op4 Rn M A s =
      Arch.project .clause s (stateOf ((decode_eret_aarch64_instrs_branch_unconditional_eret op4 Rn M A) s)) (Clauses.obs_eret_aarch64_instrs_branch_unconditional_eret real op4 Rn M A s) := rfl

def obs_ereta_aarch64_instrs_branch_unconditional_eret (real : Type) [SailReal real] (op4 : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ereta_aarch64_instrs_branch_unconditional_eret op4 Rn M A) s
theorem obs_ereta_aarch64_instrs_branch_unconditional_eret_mapping (real : Type) [SailReal real] (op4 : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (s : State) :
    obs_ereta_aarch64_instrs_branch_unconditional_eret real op4 Rn M A s =
      Arch.project .clause s (stateOf ((decode_ereta_aarch64_instrs_branch_unconditional_eret op4 Rn M A) s)) (Clauses.obs_ereta_aarch64_instrs_branch_unconditional_eret real op4 Rn M A s) := rfl

def obs_esb_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_esb_aarch64_instrs_system_hints op2 CRm) s
theorem obs_esb_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_esb_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_esb_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_esb_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (Rm : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract Rd Rn imm4 Rm Q) s
theorem obs_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (Rm : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract real Rd Rn imm4 Rm Q s =
      Arch.project .clause s (stateOf ((decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract Rd Rn imm4 Rm Q) s)) (Clauses.obs_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract real Rd Rn imm4 Rm Q s) := rfl

def obs_extr_aarch64_instrs_integer_ins_ext_extract_immediate (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate Rd Rn imms Rm N sf) s
theorem obs_extr_aarch64_instrs_integer_ins_ext_extract_immediate_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_extr_aarch64_instrs_integer_ins_ext_extract_immediate real Rd Rn imms Rm N sf s =
      Arch.project .clause s (stateOf ((decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate Rd Rn imms Rm N sf) s)) (Clauses.obs_extr_aarch64_instrs_integer_ins_ext_extract_immediate real Rd Rn imms Rm N sf s) := rfl

def obs_fabs_float_aarch64_instrs_float_arithmetic_unary (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fabs_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc ftype) s
theorem obs_fabs_float_aarch64_instrs_float_arithmetic_unary_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) (s : State) :
    obs_fabs_float_aarch64_instrs_float_arithmetic_unary real Rd Rn opc ftype s =
      Arch.project .clause s (stateOf ((decode_fabs_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc ftype) s)) (Clauses.obs_fabs_float_aarch64_instrs_float_arithmetic_unary real Rd Rn opc ftype s) := rfl

def obs_fccmp_float_aarch64_instrs_float_compare_cond (real : Type) [SailReal real] (nzcv : (BitVec 4)) (op : (BitVec 1)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fccmp_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm ftype) s
theorem obs_fccmp_float_aarch64_instrs_float_compare_cond_mapping (real : Type) [SailReal real] (nzcv : (BitVec 4)) (op : (BitVec 1)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) :
    obs_fccmp_float_aarch64_instrs_float_compare_cond real nzcv op Rn cond Rm ftype s =
      Arch.project .clause s (stateOf ((decode_fccmp_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm ftype) s)) (Clauses.obs_fccmp_float_aarch64_instrs_float_compare_cond real nzcv op Rn cond Rm ftype s) := rfl

def obs_fccmpe_float_aarch64_instrs_float_compare_cond (real : Type) [SailReal real] (nzcv : (BitVec 4)) (op : (BitVec 1)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fccmpe_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm ftype) s
theorem obs_fccmpe_float_aarch64_instrs_float_compare_cond_mapping (real : Type) [SailReal real] (nzcv : (BitVec 4)) (op : (BitVec 1)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) :
    obs_fccmpe_float_aarch64_instrs_float_compare_cond real nzcv op Rn cond Rm ftype s =
      Arch.project .clause s (stateOf ((decode_fccmpe_float_aarch64_instrs_float_compare_cond nzcv op Rn cond Rm ftype) s)) (Clauses.obs_fccmpe_float_aarch64_instrs_float_compare_cond real nzcv op Rn cond Rm ftype s) := rfl

def obs_fcmp_float_aarch64_instrs_float_compare_uncond (real : Type) [SailReal real] (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcmp_float_aarch64_instrs_float_compare_uncond opc Rn Rm ftype) s
theorem obs_fcmp_float_aarch64_instrs_float_compare_uncond_mapping (real : Type) [SailReal real] (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) :
    obs_fcmp_float_aarch64_instrs_float_compare_uncond real opc Rn Rm ftype s =
      Arch.project .clause s (stateOf ((decode_fcmp_float_aarch64_instrs_float_compare_uncond opc Rn Rm ftype) s)) (Clauses.obs_fcmp_float_aarch64_instrs_float_compare_uncond real opc Rn Rm ftype s) := rfl

def obs_fcmpe_float_aarch64_instrs_float_compare_uncond (real : Type) [SailReal real] (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcmpe_float_aarch64_instrs_float_compare_uncond opc Rn Rm ftype) s
theorem obs_fcmpe_float_aarch64_instrs_float_compare_uncond_mapping (real : Type) [SailReal real] (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) :
    obs_fcmpe_float_aarch64_instrs_float_compare_uncond real opc Rn Rm ftype s =
      Arch.project .clause s (stateOf ((decode_fcmpe_float_aarch64_instrs_float_compare_uncond opc Rn Rm ftype) s)) (Clauses.obs_fcmpe_float_aarch64_instrs_float_compare_uncond real opc Rn Rm ftype s) := rfl

def obs_fcsel_float_aarch64_instrs_float_move_fp_select (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcsel_float_aarch64_instrs_float_move_fp_select Rd Rn cond Rm ftype) s
theorem obs_fcsel_float_aarch64_instrs_float_move_fp_select_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) (s : State) :
    obs_fcsel_float_aarch64_instrs_float_move_fp_select real Rd Rn cond Rm ftype s =
      Arch.project .clause s (stateOf ((decode_fcsel_float_aarch64_instrs_float_move_fp_select Rd Rn cond Rm ftype) s)) (Clauses.obs_fcsel_float_aarch64_instrs_float_move_fp_select real Rd Rn cond Rm ftype s) := rfl

def obs_fcvt_float_aarch64_instrs_float_convert_fp (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvt_float_aarch64_instrs_float_convert_fp Rd Rn opc ftype) s
theorem obs_fcvt_float_aarch64_instrs_float_convert_fp_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) (s : State) :
    obs_fcvt_float_aarch64_instrs_float_convert_fp real Rd Rn opc ftype s =
      Arch.project .clause s (stateOf ((decode_fcvt_float_aarch64_instrs_float_convert_fp Rd Rn opc ftype) s)) (Clauses.obs_fcvt_float_aarch64_instrs_float_convert_fp real Rd Rn opc ftype s) := rfl

def obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd Rd Rn sz U Q) s
theorem obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd real Rd Rn sz U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd Rd Rn sz U Q) s)) (Clauses.obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd real Rd Rn sz U Q s) := rfl

def obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd Rd Rn sz U) s
theorem obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd real Rd Rn sz U s =
      Arch.project .clause s (stateOf ((decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd Rd Rn sz U) s)) (Clauses.obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd real Rd Rn sz U s) := rfl

def obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd Rd Rn U Q) s
theorem obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd real Rd Rn U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd Rd Rn U Q) s)) (Clauses.obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd real Rd Rn U Q s) := rfl

def obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd Rd Rn U) s
theorem obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd real Rd Rn U s =
      Arch.project .clause s (stateOf ((decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd Rd Rn U) s)) (Clauses.obs_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd real Rd Rn U s) := rfl

def obs_fcvtas_float_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtas_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtas_float_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtas_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtas_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtas_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd Rd Rn sz U Q) s
theorem obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd real Rd Rn sz U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd Rd Rn sz U Q) s)) (Clauses.obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd real Rd Rn sz U Q s) := rfl

def obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd Rd Rn sz U) s
theorem obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd real Rd Rn sz U s =
      Arch.project .clause s (stateOf ((decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd Rd Rn sz U) s)) (Clauses.obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd real Rd Rn sz U s) := rfl

def obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd Rd Rn U Q) s
theorem obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd real Rd Rn U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd Rd Rn U Q) s)) (Clauses.obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd real Rd Rn U Q s) := rfl

def obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd Rd Rn U) s
theorem obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd real Rd Rn U s =
      Arch.project .clause s (stateOf ((decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd Rd Rn U) s)) (Clauses.obs_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd real Rd Rn U s) := rfl

def obs_fcvtau_float_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtau_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtau_float_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtau_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtau_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtau_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen Rd Rn sz Q) s
theorem obs_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen real Rd Rn sz Q s =
      Arch.project .clause s (stateOf ((decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen Rd Rn sz Q) s)) (Clauses.obs_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen real Rd Rn sz Q s) := rfl

def obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s
theorem obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s) := rfl

def obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s
theorem obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s)) (Clauses.obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s) := rfl

def obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s
theorem obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s)) (Clauses.obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s) := rfl

def obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s
theorem obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s)) (Clauses.obs_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s) := rfl

def obs_fcvtms_float_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtms_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtms_float_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtms_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtms_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtms_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s
theorem obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s) := rfl

def obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s
theorem obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s)) (Clauses.obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s) := rfl

def obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s
theorem obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s)) (Clauses.obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s) := rfl

def obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s
theorem obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s)) (Clauses.obs_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s) := rfl

def obs_fcvtmu_float_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtmu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtmu_float_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtmu_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtmu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtmu_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow Rd Rn sz Q) s
theorem obs_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow real Rd Rn sz Q s =
      Arch.project .clause s (stateOf ((decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow Rd Rn sz Q) s)) (Clauses.obs_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow real Rd Rn sz Q s) := rfl

def obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s
theorem obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s) := rfl

def obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s
theorem obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s)) (Clauses.obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s) := rfl

def obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s
theorem obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s)) (Clauses.obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s) := rfl

def obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s
theorem obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s)) (Clauses.obs_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s) := rfl

def obs_fcvtns_float_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtns_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtns_float_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtns_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtns_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtns_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s
theorem obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s) := rfl

def obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s
theorem obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s)) (Clauses.obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s) := rfl

def obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s
theorem obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s)) (Clauses.obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s) := rfl

def obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s
theorem obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s)) (Clauses.obs_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s) := rfl

def obs_fcvtnu_float_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtnu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtnu_float_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtnu_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtnu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtnu_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s
theorem obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s) := rfl

def obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s
theorem obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s)) (Clauses.obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s) := rfl

def obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s
theorem obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s)) (Clauses.obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s) := rfl

def obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s
theorem obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s)) (Clauses.obs_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s) := rfl

def obs_fcvtps_float_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtps_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtps_float_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtps_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtps_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtps_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s
theorem obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s) := rfl

def obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s
theorem obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s)) (Clauses.obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s) := rfl

def obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s
theorem obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s)) (Clauses.obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s) := rfl

def obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s
theorem obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s)) (Clauses.obs_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s) := rfl

def obs_fcvtpu_float_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtpu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtpu_float_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtpu_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtpu_float_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtpu_float_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd Rd Rn sz Q) s
theorem obs_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd real Rd Rn sz Q s =
      Arch.project .clause s (stateOf ((decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd Rd Rn sz Q) s)) (Clauses.obs_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd real Rd Rn sz Q s) := rfl

def obs_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd Rd Rn sz) s
theorem obs_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (s : State) :
    obs_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd real Rd Rn sz s =
      Arch.project .clause s (stateOf ((decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd Rd Rn sz) s)) (Clauses.obs_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd real Rd Rn sz s) := rfl

def obs_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd Rd Rn immb immh U Q) s
theorem obs_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd real Rd Rn immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd Rd Rn immb immh U Q) s)) (Clauses.obs_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd real Rd Rn immb immh U Q s) := rfl

def obs_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd Rd Rn immb immh U) s
theorem obs_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd real Rd Rn immb immh U s =
      Arch.project .clause s (stateOf ((decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd Rd Rn immb immh U) s)) (Clauses.obs_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd real Rd Rn immb immh U s) := rfl

def obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s
theorem obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s) := rfl

def obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s
theorem obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s)) (Clauses.obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s) := rfl

def obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s
theorem obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s)) (Clauses.obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s) := rfl

def obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s
theorem obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s)) (Clauses.obs_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s) := rfl

def obs_fcvtzs_float_fix_aarch64_instrs_float_convert_fix (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode ftype sf) s
theorem obs_fcvtzs_float_fix_aarch64_instrs_float_convert_fix_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtzs_float_fix_aarch64_instrs_float_convert_fix real Rd Rn scale opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode ftype sf) s)) (Clauses.obs_fcvtzs_float_fix_aarch64_instrs_float_convert_fix real Rd Rn scale opcode rmode ftype sf s) := rfl

def obs_fcvtzs_float_int_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzs_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtzs_float_int_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtzs_float_int_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtzs_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtzs_float_int_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd Rd Rn immb immh U Q) s
theorem obs_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd real Rd Rn immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd Rd Rn immb immh U Q) s)) (Clauses.obs_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd real Rd Rn immb immh U Q s) := rfl

def obs_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd Rd Rn immb immh U) s
theorem obs_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd real Rd Rn immb immh U s =
      Arch.project .clause s (stateOf ((decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd Rd Rn immb immh U) s)) (Clauses.obs_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd real Rd Rn immb immh U s) := rfl

def obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s
theorem obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd real Rd Rn o1 sz o2 U Q s) := rfl

def obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s
theorem obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd Rd Rn o1 sz o2 U) s)) (Clauses.obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd real Rd Rn o1 sz o2 U s) := rfl

def obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s
theorem obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd Rd Rn o1 o2 U Q) s)) (Clauses.obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd real Rd Rn o1 o2 U Q s) := rfl

def obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s
theorem obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s =
      Arch.project .clause s (stateOf ((decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd Rd Rn o1 o2 U) s)) (Clauses.obs_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd real Rd Rn o1 o2 U s) := rfl

def obs_fcvtzu_float_fix_aarch64_instrs_float_convert_fix (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode ftype sf) s
theorem obs_fcvtzu_float_fix_aarch64_instrs_float_convert_fix_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtzu_float_fix_aarch64_instrs_float_convert_fix real Rd Rn scale opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode ftype sf) s)) (Clauses.obs_fcvtzu_float_fix_aarch64_instrs_float_convert_fix real Rd Rn scale opcode rmode ftype sf s) := rfl

def obs_fcvtzu_float_int_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fcvtzu_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fcvtzu_float_int_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fcvtzu_float_int_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fcvtzu_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fcvtzu_float_int_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fjcvtzs_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fjcvtzs_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fjcvtzs_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fjcvtzs_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fjcvtzs_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fjcvtzs_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fmov_advsimd_aarch64_instrs_vector_fp16_movi (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi Rd h g f e d c b a Q) s
theorem obs_fmov_advsimd_aarch64_instrs_vector_fp16_movi_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fmov_advsimd_aarch64_instrs_vector_fp16_movi real Rd h g f e d c b a Q s =
      Arch.project .clause s (stateOf ((decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi Rd h g f e d c b a Q) s)) (Clauses.obs_fmov_advsimd_aarch64_instrs_vector_fp16_movi real Rd h g f e d c b a Q s) := rfl

def obs_fmov_advsimd_aarch64_instrs_vector_logical (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fmov_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s
theorem obs_fmov_advsimd_aarch64_instrs_vector_logical_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_fmov_advsimd_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s =
      Arch.project .clause s (stateOf ((decode_fmov_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s)) (Clauses.obs_fmov_advsimd_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s) := rfl

def obs_fmov_float_aarch64_instrs_float_arithmetic_unary (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fmov_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc ftype) s
theorem obs_fmov_float_aarch64_instrs_float_arithmetic_unary_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) (s : State) :
    obs_fmov_float_aarch64_instrs_float_arithmetic_unary real Rd Rn opc ftype s =
      Arch.project .clause s (stateOf ((decode_fmov_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc ftype) s)) (Clauses.obs_fmov_float_aarch64_instrs_float_arithmetic_unary real Rd Rn opc ftype s) := rfl

def obs_fmov_float_gen_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fmov_float_gen_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_fmov_float_gen_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_fmov_float_gen_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_fmov_float_gen_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_fmov_float_gen_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_fmov_float_imm_aarch64_instrs_float_move_fp_imm (real : Type) [SailReal real] (Rd : (BitVec 5)) (imm8 : (BitVec 8)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm Rd imm8 ftype) s
theorem obs_fmov_float_imm_aarch64_instrs_float_move_fp_imm_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (imm8 : (BitVec 8)) (ftype : (BitVec 2)) (s : State) :
    obs_fmov_float_imm_aarch64_instrs_float_move_fp_imm real Rd imm8 ftype s =
      Arch.project .clause s (stateOf ((decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm Rd imm8 ftype) s)) (Clauses.obs_fmov_float_imm_aarch64_instrs_float_move_fp_imm real Rd imm8 ftype s) := rfl

def obs_fneg_float_aarch64_instrs_float_arithmetic_unary (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_fneg_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc ftype) s
theorem obs_fneg_float_aarch64_instrs_float_arithmetic_unary_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) (s : State) :
    obs_fneg_float_aarch64_instrs_float_arithmetic_unary real Rd Rn opc ftype s =
      Arch.project .clause s (stateOf ((decode_fneg_float_aarch64_instrs_float_arithmetic_unary Rd Rn opc ftype) s)) (Clauses.obs_fneg_float_aarch64_instrs_float_arithmetic_unary real Rd Rn opc ftype s) := rfl

def obs_frint32x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frint32x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 Rd Rn op sz U Q) s
theorem obs_frint32x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frint32x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 real Rd Rn op sz U Q s =
      Arch.project .clause s (stateOf ((decode_frint32x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 Rd Rn op sz U Q) s)) (Clauses.obs_frint32x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 real Rd Rn op sz U Q s) := rfl

def obs_frint32x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frint32x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 Rd Rn op ftype) s
theorem obs_frint32x_float_aarch64_instrs_float_arithmetic_round_frint_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) (s : State) :
    obs_frint32x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 real Rd Rn op ftype s =
      Arch.project .clause s (stateOf ((decode_frint32x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 Rd Rn op ftype) s)) (Clauses.obs_frint32x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 real Rd Rn op ftype s) := rfl

def obs_frint32z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frint32z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 Rd Rn op sz U Q) s
theorem obs_frint32z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frint32z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 real Rd Rn op sz U Q s =
      Arch.project .clause s (stateOf ((decode_frint32z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 Rd Rn op sz U Q) s)) (Clauses.obs_frint32z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 real Rd Rn op sz U Q s) := rfl

def obs_frint32z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frint32z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 Rd Rn op ftype) s
theorem obs_frint32z_float_aarch64_instrs_float_arithmetic_round_frint_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) (s : State) :
    obs_frint32z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 real Rd Rn op ftype s =
      Arch.project .clause s (stateOf ((decode_frint32z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 Rd Rn op ftype) s)) (Clauses.obs_frint32z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 real Rd Rn op ftype s) := rfl

def obs_frint64x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frint64x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 Rd Rn op sz U Q) s
theorem obs_frint64x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frint64x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 real Rd Rn op sz U Q s =
      Arch.project .clause s (stateOf ((decode_frint64x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 Rd Rn op sz U Q) s)) (Clauses.obs_frint64x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 real Rd Rn op sz U Q s) := rfl

def obs_frint64x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frint64x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 Rd Rn op ftype) s
theorem obs_frint64x_float_aarch64_instrs_float_arithmetic_round_frint_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) (s : State) :
    obs_frint64x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 real Rd Rn op ftype s =
      Arch.project .clause s (stateOf ((decode_frint64x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 Rd Rn op ftype) s)) (Clauses.obs_frint64x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 real Rd Rn op ftype s) := rfl

def obs_frint64z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frint64z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 Rd Rn op sz U Q) s
theorem obs_frint64z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frint64z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 real Rd Rn op sz U Q s =
      Arch.project .clause s (stateOf ((decode_frint64z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 Rd Rn op sz U Q) s)) (Clauses.obs_frint64z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 real Rd Rn op sz U Q s) := rfl

def obs_frint64z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frint64z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 Rd Rn op ftype) s
theorem obs_frint64z_float_aarch64_instrs_float_arithmetic_round_frint_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) (s : State) :
    obs_frint64z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 real Rd Rn op ftype s =
      Arch.project .clause s (stateOf ((decode_frint64z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 Rd Rn op ftype) s)) (Clauses.obs_frint64z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 real Rd Rn op ftype s) := rfl

def obs_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s
theorem obs_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s) := rfl

def obs_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s
theorem obs_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s)) (Clauses.obs_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s) := rfl

def obs_frinta_float_aarch64_instrs_float_arithmetic_round_frint (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s
theorem obs_frinta_float_aarch64_instrs_float_arithmetic_round_frint_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) :
    obs_frinta_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s =
      Arch.project .clause s (stateOf ((decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s)) (Clauses.obs_frinta_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s) := rfl

def obs_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s
theorem obs_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s) := rfl

def obs_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s
theorem obs_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s)) (Clauses.obs_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s) := rfl

def obs_frinti_float_aarch64_instrs_float_arithmetic_round_frint (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s
theorem obs_frinti_float_aarch64_instrs_float_arithmetic_round_frint_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) :
    obs_frinti_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s =
      Arch.project .clause s (stateOf ((decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s)) (Clauses.obs_frinti_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s) := rfl

def obs_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s
theorem obs_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s) := rfl

def obs_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s
theorem obs_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s)) (Clauses.obs_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s) := rfl

def obs_frintm_float_aarch64_instrs_float_arithmetic_round_frint (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s
theorem obs_frintm_float_aarch64_instrs_float_arithmetic_round_frint_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) :
    obs_frintm_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s =
      Arch.project .clause s (stateOf ((decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s)) (Clauses.obs_frintm_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s) := rfl

def obs_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s
theorem obs_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s) := rfl

def obs_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s
theorem obs_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s)) (Clauses.obs_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s) := rfl

def obs_frintn_float_aarch64_instrs_float_arithmetic_round_frint (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s
theorem obs_frintn_float_aarch64_instrs_float_arithmetic_round_frint_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) :
    obs_frintn_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s =
      Arch.project .clause s (stateOf ((decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s)) (Clauses.obs_frintn_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s) := rfl

def obs_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s
theorem obs_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s) := rfl

def obs_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s
theorem obs_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s)) (Clauses.obs_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s) := rfl

def obs_frintp_float_aarch64_instrs_float_arithmetic_round_frint (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s
theorem obs_frintp_float_aarch64_instrs_float_arithmetic_round_frint_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) :
    obs_frintp_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s =
      Arch.project .clause s (stateOf ((decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s)) (Clauses.obs_frintp_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s) := rfl

def obs_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s
theorem obs_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s) := rfl

def obs_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s
theorem obs_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s)) (Clauses.obs_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s) := rfl

def obs_frintx_float_aarch64_instrs_float_arithmetic_round_frint (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s
theorem obs_frintx_float_aarch64_instrs_float_arithmetic_round_frint_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) :
    obs_frintx_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s =
      Arch.project .clause s (stateOf ((decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s)) (Clauses.obs_frintx_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s) := rfl

def obs_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s
theorem obs_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U Q) s)) (Clauses.obs_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round real Rd Rn o1 sz o2 U Q s) := rfl

def obs_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s
theorem obs_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s =
      Arch.project .clause s (stateOf ((decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q) s)) (Clauses.obs_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round real Rd Rn o1 o2 U Q s) := rfl

def obs_frintz_float_aarch64_instrs_float_arithmetic_round_frint (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s
theorem obs_frintz_float_aarch64_instrs_float_arithmetic_round_frint_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) (s : State) :
    obs_frintz_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s =
      Arch.project .clause s (stateOf ((decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn rmode ftype) s)) (Clauses.obs_frintz_float_aarch64_instrs_float_arithmetic_round_frint real Rd Rn rmode ftype s) := rfl

def obs_gcsb_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_gcsb_aarch64_instrs_system_hints op2 CRm) s
theorem obs_gcsb_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_gcsb_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_gcsb_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_gcsb_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_hint_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_hint_aarch64_instrs_system_hints op2 CRm) s
theorem obs_hint_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_hint_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_hint_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_hint_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_hlt_aarch64_instrs_system_exceptions_debug_halt (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) : Arch.Observation :=
  Arch.observe (decode_hlt_aarch64_instrs_system_exceptions_debug_halt imm16) s
theorem obs_hlt_aarch64_instrs_system_exceptions_debug_halt_mapping (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) :
    obs_hlt_aarch64_instrs_system_exceptions_debug_halt real imm16 s =
      Arch.project .clause s (stateOf ((decode_hlt_aarch64_instrs_system_exceptions_debug_halt imm16) s)) (Clauses.obs_hlt_aarch64_instrs_system_exceptions_debug_halt real imm16 s) := rfl

def obs_hvc_aarch64_instrs_system_exceptions_runtime_hvc (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) : Arch.Observation :=
  Arch.observe (decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc imm16) s
theorem obs_hvc_aarch64_instrs_system_exceptions_runtime_hvc_mapping (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) :
    obs_hvc_aarch64_instrs_system_exceptions_runtime_hvc real imm16 s =
      Arch.project .clause s (stateOf ((decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc imm16) s)) (Clauses.obs_hvc_aarch64_instrs_system_exceptions_runtime_hvc real imm16 s) := rfl

def obs_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (imm5 : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert Rd Rn imm4 imm5) s
theorem obs_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (imm5 : (BitVec 5)) (s : State) :
    obs_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert real Rd Rn imm4 imm5 s =
      Arch.project .clause s (stateOf ((decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert Rd Rn imm4 imm5) s)) (Clauses.obs_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert real Rd Rn imm4 imm5 s) := rfl

def obs_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert Rd Rn imm5) s
theorem obs_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (s : State) :
    obs_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert real Rd Rn imm5 s =
      Arch.project .clause s (stateOf ((decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert Rd Rn imm5) s)) (Clauses.obs_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert real Rd Rn imm5 s) := rfl

def obs_isb_aarch64_instrs_system_barriers_isb (real : Type) [SailReal real] (opc : (BitVec 2)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_isb_aarch64_instrs_system_barriers_isb opc CRm) s
theorem obs_isb_aarch64_instrs_system_barriers_isb_mapping (real : Type) [SailReal real] (opc : (BitVec 2)) (CRm : (BitVec 4)) (s : State) :
    obs_isb_aarch64_instrs_system_barriers_isb real opc CRm s =
      Arch.project .clause s (stateOf ((decode_isb_aarch64_instrs_system_barriers_isb opc CRm) s)) (Clauses.obs_isb_aarch64_instrs_system_barriers_isb real opc CRm s) := rfl

def obs_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s
theorem obs_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s =
      Arch.project .clause s (stateOf ((decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s)) (Clauses.obs_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s) := rfl

def obs_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s
theorem obs_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s =
      Arch.project .clause s (stateOf ((decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s)) (Clauses.obs_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s) := rfl

def obs_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s
theorem obs_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s =
      Arch.project .clause s (stateOf ((decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s)) (Clauses.obs_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s) := rfl

def obs_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s
theorem obs_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s =
      Arch.project .clause s (stateOf ((decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s)) (Clauses.obs_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s) := rfl

def obs_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s
theorem obs_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s =
      Arch.project .clause s (stateOf ((decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s)) (Clauses.obs_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s) := rfl

def obs_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s
theorem obs_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s =
      Arch.project .clause s (stateOf ((decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s)) (Clauses.obs_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s) := rfl

def obs_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s
theorem obs_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s =
      Arch.project .clause s (stateOf ((decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s)) (Clauses.obs_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s) := rfl

def obs_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s
theorem obs_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s =
      Arch.project .clause s (stateOf ((decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s)) (Clauses.obs_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s) := rfl

def obs_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_ld64b_aarch64_instrs_memory_atomicops_ld_acc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ld64b_aarch64_instrs_memory_atomicops_ld_acc Rt Rn) s
theorem obs_ld64b_aarch64_instrs_memory_atomicops_ld_acc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (s : State) :
    obs_ld64b_aarch64_instrs_memory_atomicops_ld_acc real Rt Rn s =
      Arch.project .clause s (stateOf ((decode_ld64b_aarch64_instrs_memory_atomicops_ld_acc Rt Rn) s)) (Clauses.obs_ld64b_aarch64_instrs_memory_atomicops_ld_acc real Rt Rn s) := rfl

def obs_ldadd_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldadd_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldadd_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldadd_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldadd_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldadd_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldaddb_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldaddb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldaddb_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldaddb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldaddb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldaddb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldaddh_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldaddh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldaddh_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldaddh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldaddh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldaddh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldapr_aarch64_instrs_memory_ordered_rcpc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldapr_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs size) s
theorem obs_ldapr_aarch64_instrs_memory_ordered_rcpc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_ldapr_aarch64_instrs_memory_ordered_rcpc real Rt Rn Rs size s =
      Arch.project .clause s (stateOf ((decode_ldapr_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs size) s)) (Clauses.obs_ldapr_aarch64_instrs_memory_ordered_rcpc real Rt Rn Rs size s) := rfl

def obs_ldapr_aarch64_instrs_memory_ordered_rcpc_writeback (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldapr_aarch64_instrs_memory_ordered_rcpc_writeback Rt Rn size) s
theorem obs_ldapr_aarch64_instrs_memory_ordered_rcpc_writeback_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_ldapr_aarch64_instrs_memory_ordered_rcpc_writeback real Rt Rn size s =
      Arch.project .clause s (stateOf ((decode_ldapr_aarch64_instrs_memory_ordered_rcpc_writeback Rt Rn size) s)) (Clauses.obs_ldapr_aarch64_instrs_memory_ordered_rcpc_writeback real Rt Rn size s) := rfl

def obs_ldaprb_aarch64_instrs_memory_ordered_rcpc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldaprb_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs size) s
theorem obs_ldaprb_aarch64_instrs_memory_ordered_rcpc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_ldaprb_aarch64_instrs_memory_ordered_rcpc real Rt Rn Rs size s =
      Arch.project .clause s (stateOf ((decode_ldaprb_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs size) s)) (Clauses.obs_ldaprb_aarch64_instrs_memory_ordered_rcpc real Rt Rn Rs size s) := rfl

def obs_ldaprh_aarch64_instrs_memory_ordered_rcpc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldaprh_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs size) s
theorem obs_ldaprh_aarch64_instrs_memory_ordered_rcpc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_ldaprh_aarch64_instrs_memory_ordered_rcpc real Rt Rn Rs size s =
      Arch.project .clause s (stateOf ((decode_ldaprh_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs size) s)) (Clauses.obs_ldaprh_aarch64_instrs_memory_ordered_rcpc real Rt Rn Rs size s) := rfl

def obs_ldapur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldapur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered Rt Rn imm9 opc size) s
theorem obs_ldapur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldapur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldapur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered Rt Rn imm9 opc size) s)) (Clauses.obs_ldapur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered real Rt Rn imm9 opc size s) := rfl

def obs_ldapur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldapur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s
theorem obs_ldapur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldapur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldapur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s)) (Clauses.obs_ldapur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s) := rfl

def obs_ldapurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldapurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s
theorem obs_ldapurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldapurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldapurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s)) (Clauses.obs_ldapurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s) := rfl

def obs_ldapurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldapurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s
theorem obs_ldapurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldapurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldapurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s)) (Clauses.obs_ldapurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s) := rfl

def obs_ldapursb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldapursb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s
theorem obs_ldapursb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldapursb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldapursb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s)) (Clauses.obs_ldapursb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s) := rfl

def obs_ldapursh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldapursh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s
theorem obs_ldapursh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldapursh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldapursh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s)) (Clauses.obs_ldapursh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s) := rfl

def obs_ldapursw_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldapursw_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s
theorem obs_ldapursw_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldapursw_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldapursw_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s)) (Clauses.obs_ldapursw_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s) := rfl

def obs_ldar_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldar_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldar_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldar_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldar_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldar_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldarb_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldarb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldarb_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldarb_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldarb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldarb_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldarh_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldarh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldarh_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldarh_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldarh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldarh_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldaxp_aarch64_instrs_memory_exclusive_pair (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldaxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz) s
theorem obs_ldaxp_aarch64_instrs_memory_exclusive_pair_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) (s : State) :
    obs_ldaxp_aarch64_instrs_memory_exclusive_pair real Rt Rn Rt2 o0 Rs L sz s =
      Arch.project .clause s (stateOf ((decode_ldaxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz) s)) (Clauses.obs_ldaxp_aarch64_instrs_memory_exclusive_pair real Rt Rn Rt2 o0 Rs L sz s) := rfl

def obs_ldaxr_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldaxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldaxr_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldaxr_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldaxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldaxr_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldaxrb_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldaxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldaxrb_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldaxrb_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldaxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldaxrb_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldaxrh_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldaxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldaxrh_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldaxrh_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldaxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldaxrh_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldclr_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldclr_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldclr_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldclr_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldclr_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldclr_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldclrb_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldclrb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldclrb_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldclrb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldclrb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldclrb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldclrh_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldclrh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldclrh_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldclrh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldclrh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldclrh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldclrp_aarch64_instrs_memory_atomicops_ld_128_ldclrp (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldclrp_aarch64_instrs_memory_atomicops_ld_128_ldclrp Rt Rn opc o3 Rt2 R A S) s
theorem obs_ldclrp_aarch64_instrs_memory_atomicops_ld_128_ldclrp_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) (s : State) :
    obs_ldclrp_aarch64_instrs_memory_atomicops_ld_128_ldclrp real Rt Rn opc o3 Rt2 R A S s =
      Arch.project .clause s (stateOf ((decode_ldclrp_aarch64_instrs_memory_atomicops_ld_128_ldclrp Rt Rn opc o3 Rt2 R A S) s)) (Clauses.obs_ldclrp_aarch64_instrs_memory_atomicops_ld_128_ldclrp real Rt Rn opc o3 Rt2 R A S s) := rfl

def obs_ldeor_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldeor_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldeor_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldeor_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldeor_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldeor_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldeorb_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldeorb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldeorb_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldeorb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldeorb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldeorb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldeorh_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldeorh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldeorh_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldeorh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldeorh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldeorh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldlar_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldlar_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldlar_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldlar_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldlar_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldlar_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldlarb_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldlarb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldlarb_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldlarb_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldlarb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldlarb_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldlarh_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldlarh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldlarh_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldlarh_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldlarh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldlarh_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L opc) s
theorem obs_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc Rt Rn Rt2 imm7 L opc) s
theorem obs_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2 imm7 L opc) s
theorem obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldp_gen_aarch64_instrs_memory_pair_general_offset (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L opc) s
theorem obs_ldp_gen_aarch64_instrs_memory_pair_general_offset_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldp_gen_aarch64_instrs_memory_pair_general_offset real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldp_gen_aarch64_instrs_memory_pair_general_offset real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldp_gen_aarch64_instrs_memory_pair_general_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_ldp_gen_aarch64_instrs_memory_pair_general_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldp_gen_aarch64_instrs_memory_pair_general_post_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldp_gen_aarch64_instrs_memory_pair_general_post_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldpsw_aarch64_instrs_memory_pair_general_offset (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldpsw_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L opc) s
theorem obs_ldpsw_aarch64_instrs_memory_pair_general_offset_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldpsw_aarch64_instrs_memory_pair_general_offset real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldpsw_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldpsw_aarch64_instrs_memory_pair_general_offset real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldpsw_aarch64_instrs_memory_pair_general_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_ldpsw_aarch64_instrs_memory_pair_general_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldpsw_aarch64_instrs_memory_pair_general_post_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldpsw_aarch64_instrs_memory_pair_general_post_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldpsw_aarch64_instrs_memory_pair_general_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_ldpsw_aarch64_instrs_memory_pair_general_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_ldpsw_aarch64_instrs_memory_pair_general_pre_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_ldpsw_aarch64_instrs_memory_pair_general_pre_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp Rt imm19 opc) s
theorem obs_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) (s : State) :
    obs_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp real Rt imm19 opc s =
      Arch.project .clause s (stateOf ((decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp Rt imm19 opc) s)) (Clauses.obs_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp real Rt imm19 opc s) := rfl

def obs_ldr_lit_gen_aarch64_instrs_memory_literal_general (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_lit_gen_aarch64_instrs_memory_literal_general Rt imm19 opc) s
theorem obs_ldr_lit_gen_aarch64_instrs_memory_literal_general_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) (s : State) :
    obs_ldr_lit_gen_aarch64_instrs_memory_literal_general real Rt imm19 opc s =
      Arch.project .clause s (stateOf ((decode_ldr_lit_gen_aarch64_instrs_memory_literal_general Rt imm19 opc) s)) (Clauses.obs_ldr_lit_gen_aarch64_instrs_memory_literal_general real Rt imm19 opc s) := rfl

def obs_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register Rt Rn S option_name Rm opc size) s
theorem obs_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_ldr_reg_gen_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_ldr_reg_gen_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldr_reg_gen_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_ldr_reg_gen_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_ldra_aarch64_instrs_memory_single_general_immediate_signed_pac (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (W : (BitVec 1)) (imm9 : (BitVec 9)) (S : (BitVec 1)) (M : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldra_aarch64_instrs_memory_single_general_immediate_signed_pac Rt Rn W imm9 S M size) s
theorem obs_ldra_aarch64_instrs_memory_single_general_immediate_signed_pac_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (W : (BitVec 1)) (imm9 : (BitVec 9)) (S : (BitVec 1)) (M : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldra_aarch64_instrs_memory_single_general_immediate_signed_pac real Rt Rn W imm9 S M size s =
      Arch.project .clause s (stateOf ((decode_ldra_aarch64_instrs_memory_single_general_immediate_signed_pac Rt Rn W imm9 S M size) s)) (Clauses.obs_ldra_aarch64_instrs_memory_single_general_immediate_signed_pac real Rt Rn W imm9 S M size s) := rfl

def obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_ldrb_reg_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_ldrb_reg_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrb_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_ldrb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_ldrb_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_ldrh_reg_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_ldrh_reg_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrh_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_ldrh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_ldrh_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_ldrsb_reg_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_ldrsb_reg_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsb_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_ldrsb_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_ldrsh_reg_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_ldrsh_reg_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsh_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_ldrsh_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_ldrsw_lit_aarch64_instrs_memory_literal_general (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsw_lit_aarch64_instrs_memory_literal_general Rt imm19 opc) s
theorem obs_ldrsw_lit_aarch64_instrs_memory_literal_general_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) (s : State) :
    obs_ldrsw_lit_aarch64_instrs_memory_literal_general real Rt imm19 opc s =
      Arch.project .clause s (stateOf ((decode_ldrsw_lit_aarch64_instrs_memory_literal_general Rt imm19 opc) s)) (Clauses.obs_ldrsw_lit_aarch64_instrs_memory_literal_general real Rt imm19 opc s) := rfl

def obs_ldrsw_reg_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldrsw_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_ldrsw_reg_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldrsw_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_ldrsw_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_ldrsw_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_ldset_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldset_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldset_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldset_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldset_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldset_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldsetb_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldsetb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldsetb_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldsetb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldsetb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldsetb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldseth_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldseth_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldseth_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldseth_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldseth_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldseth_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldsetp_aarch64_instrs_memory_atomicops_ld_128_ldsetp (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldsetp_aarch64_instrs_memory_atomicops_ld_128_ldsetp Rt Rn opc o3 Rt2 R A S) s
theorem obs_ldsetp_aarch64_instrs_memory_atomicops_ld_128_ldsetp_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) (s : State) :
    obs_ldsetp_aarch64_instrs_memory_atomicops_ld_128_ldsetp real Rt Rn opc o3 Rt2 R A S s =
      Arch.project .clause s (stateOf ((decode_ldsetp_aarch64_instrs_memory_atomicops_ld_128_ldsetp Rt Rn opc o3 Rt2 R A S) s)) (Clauses.obs_ldsetp_aarch64_instrs_memory_atomicops_ld_128_ldsetp real Rt Rn opc o3 Rt2 R A S s) := rfl

def obs_ldsmax_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldsmax_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldsmax_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldsmax_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldsmax_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldsmax_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldsmaxb_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldsmaxb_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldsmaxb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldsmaxb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldsmaxh_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldsmaxh_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldsmaxh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldsmaxh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldsmin_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldsmin_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldsmin_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldsmin_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldsmin_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldsmin_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldsminb_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldsminb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldsminb_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldsminb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldsminb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldsminb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldsminh_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldsminh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldsminh_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldsminh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldsminh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldsminh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s
theorem obs_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s)) (Clauses.obs_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s) := rfl

def obs_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s
theorem obs_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s)) (Clauses.obs_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s) := rfl

def obs_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s
theorem obs_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s)) (Clauses.obs_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s) := rfl

def obs_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s
theorem obs_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s)) (Clauses.obs_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s) := rfl

def obs_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s
theorem obs_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s)) (Clauses.obs_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s) := rfl

def obs_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s
theorem obs_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s)) (Clauses.obs_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s) := rfl

def obs_ldumax_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldumax_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldumax_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldumax_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldumax_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldumax_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldumaxb_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldumaxb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldumaxb_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldumaxb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldumaxb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldumaxb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldumaxh_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldumaxh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldumaxh_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldumaxh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldumaxh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldumaxh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldumin_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldumin_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_ldumin_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldumin_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_ldumin_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_ldumin_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_lduminb_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_lduminb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_lduminb_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_lduminb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_lduminb_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_lduminb_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_lduminh_aarch64_instrs_memory_atomicops_ld (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_lduminh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s
theorem obs_lduminh_aarch64_instrs_memory_atomicops_ld_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_lduminh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s =
      Arch.project .clause s (stateOf ((decode_lduminh_aarch64_instrs_memory_atomicops_ld Rt Rn opc Rs R A size) s)) (Clauses.obs_lduminh_aarch64_instrs_memory_atomicops_ld real Rt Rn opc Rs R A size s) := rfl

def obs_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_ldxp_aarch64_instrs_memory_exclusive_pair (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz) s
theorem obs_ldxp_aarch64_instrs_memory_exclusive_pair_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) (s : State) :
    obs_ldxp_aarch64_instrs_memory_exclusive_pair real Rt Rn Rt2 o0 Rs L sz s =
      Arch.project .clause s (stateOf ((decode_ldxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz) s)) (Clauses.obs_ldxp_aarch64_instrs_memory_exclusive_pair real Rt Rn Rt2 o0 Rs L sz s) := rfl

def obs_ldxr_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldxr_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldxr_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldxr_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldxrb_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldxrb_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldxrb_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldxrb_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_ldxrh_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ldxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_ldxrh_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_ldxrh_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_ldxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_ldxrh_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_lslv_aarch64_instrs_integer_shift_variable (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_lslv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf) s
theorem obs_lslv_aarch64_instrs_integer_shift_variable_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_lslv_aarch64_instrs_integer_shift_variable real Rd Rn op2 Rm sf s =
      Arch.project .clause s (stateOf ((decode_lslv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf) s)) (Clauses.obs_lslv_aarch64_instrs_integer_shift_variable real Rd Rn op2 Rm sf s) := rfl

def obs_lsrv_aarch64_instrs_integer_shift_variable (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_lsrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf) s
theorem obs_lsrv_aarch64_instrs_integer_shift_variable_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_lsrv_aarch64_instrs_integer_shift_variable real Rd Rn op2 Rm sf s =
      Arch.project .clause s (stateOf ((decode_lsrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf) s)) (Clauses.obs_lsrv_aarch64_instrs_integer_shift_variable real Rd Rn op2 Rm sf s) := rfl

def obs_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm sf) s
theorem obs_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub real Rd Rn Ra o0 Rm sf s =
      Arch.project .clause s (stateOf ((decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm sf) s)) (Clauses.obs_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub real Rd Rn Ra o0 Rm sf s) := rfl

def obs_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int Rd Rn H o2 Rm M L size Q) s
theorem obs_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int real Rd Rn H o2 Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int Rd Rn H o2 Rm M L size Q) s)) (Clauses.obs_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int real Rd Rn H o2 Rm M L size Q s) := rfl

def obs_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum Rd Rn Rm size U Q) s
theorem obs_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum Rd Rn Rm size U Q) s)) (Clauses.obs_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum real Rd Rn Rm size U Q s) := rfl

def obs_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int Rd Rn H o2 Rm M L size Q) s
theorem obs_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int real Rd Rn H o2 Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int Rd Rn H o2 Rm M L size Q) s)) (Clauses.obs_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int real Rd Rn H o2 Rm M L size Q s) := rfl

def obs_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum Rd Rn Rm size U Q) s
theorem obs_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum Rd Rn Rm size U Q) s)) (Clauses.obs_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum real Rd Rn Rm size U Q s) := rfl

def obs_movi_advsimd_aarch64_instrs_vector_logical (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_movi_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s
theorem obs_movi_advsimd_aarch64_instrs_vector_logical_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_movi_advsimd_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s =
      Arch.project .clause s (stateOf ((decode_movi_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s)) (Clauses.obs_movi_advsimd_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s) := rfl

def obs_movk_aarch64_instrs_integer_ins_ext_insert_movewide (real : Type) [SailReal real] (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf) s
theorem obs_movk_aarch64_instrs_integer_ins_ext_insert_movewide_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_movk_aarch64_instrs_integer_ins_ext_insert_movewide real Rd imm16 hw opc sf s =
      Arch.project .clause s (stateOf ((decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf) s)) (Clauses.obs_movk_aarch64_instrs_integer_ins_ext_insert_movewide real Rd imm16 hw opc sf s) := rfl

def obs_movn_aarch64_instrs_integer_ins_ext_insert_movewide (real : Type) [SailReal real] (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf) s
theorem obs_movn_aarch64_instrs_integer_ins_ext_insert_movewide_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_movn_aarch64_instrs_integer_ins_ext_insert_movewide real Rd imm16 hw opc sf s =
      Arch.project .clause s (stateOf ((decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf) s)) (Clauses.obs_movn_aarch64_instrs_integer_ins_ext_insert_movewide real Rd imm16 hw opc sf s) := rfl

def obs_movz_aarch64_instrs_integer_ins_ext_insert_movewide (real : Type) [SailReal real] (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf) s
theorem obs_movz_aarch64_instrs_integer_ins_ext_insert_movewide_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_movz_aarch64_instrs_integer_ins_ext_insert_movewide real Rd imm16 hw opc sf s =
      Arch.project .clause s (stateOf ((decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf) s)) (Clauses.obs_movz_aarch64_instrs_integer_ins_ext_insert_movewide real Rd imm16 hw opc sf s) := rfl

def obs_mrs_aarch64_instrs_system_register_system (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_mrs_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L) s
theorem obs_mrs_aarch64_instrs_system_register_system_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) (s : State) :
    obs_mrs_aarch64_instrs_system_register_system real Rt op2 CRm CRn op1 o0 L s =
      Arch.project .clause s (stateOf ((decode_mrs_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L) s)) (Clauses.obs_mrs_aarch64_instrs_system_register_system real Rt op2 CRm CRn op1 o0 L s) := rfl

def obs_msr_imm_aarch64_instrs_system_register_cpsr (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (op1 : (BitVec 3)) (s : State) : Arch.Observation :=
  Arch.observe (decode_msr_imm_aarch64_instrs_system_register_cpsr op2 CRm op1) s
theorem obs_msr_imm_aarch64_instrs_system_register_cpsr_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (op1 : (BitVec 3)) (s : State) :
    obs_msr_imm_aarch64_instrs_system_register_cpsr real op2 CRm op1 s =
      Arch.project .clause s (stateOf ((decode_msr_imm_aarch64_instrs_system_register_cpsr op2 CRm op1) s)) (Clauses.obs_msr_imm_aarch64_instrs_system_register_cpsr real op2 CRm op1 s) := rfl

def obs_msr_reg_aarch64_instrs_system_register_system (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_msr_reg_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L) s
theorem obs_msr_reg_aarch64_instrs_system_register_system_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) (s : State) :
    obs_msr_reg_aarch64_instrs_system_register_system real Rt op2 CRm CRn op1 o0 L s =
      Arch.project .clause s (stateOf ((decode_msr_reg_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L) s)) (Clauses.obs_msr_reg_aarch64_instrs_system_register_system real Rt op2 CRm CRn op1 o0 L s) := rfl

def obs_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm sf) s
theorem obs_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub real Rd Rn Ra o0 Rm sf s =
      Arch.project .clause s (stateOf ((decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm sf) s)) (Clauses.obs_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub real Rd Rn Ra o0 Rm sf s) := rfl

def obs_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int Rd Rn H Rm M L size Q) s
theorem obs_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int real Rd Rn H Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int Rd Rn H Rm M L size Q) s)) (Clauses.obs_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int real Rd Rn H Rm M L size Q s) := rfl

def obs_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product Rd Rn Rm size U Q) s
theorem obs_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product Rd Rn Rm size U Q) s)) (Clauses.obs_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product real Rd Rn Rm size U Q s) := rfl

def obs_mvni_advsimd_aarch64_instrs_vector_logical (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_mvni_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s
theorem obs_mvni_advsimd_aarch64_instrs_vector_logical_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_mvni_advsimd_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s =
      Arch.project .clause s (stateOf ((decode_mvni_advsimd_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s)) (Clauses.obs_mvni_advsimd_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s) := rfl

def obs_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd Rd Rn size U Q) s
theorem obs_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd Rd Rn size U Q) s)) (Clauses.obs_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd real Rd Rn size U Q s) := rfl

def obs_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd Rd Rn size U) s
theorem obs_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd real Rd Rn size U s =
      Arch.project .clause s (stateOf ((decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd Rd Rn size U) s)) (Clauses.obs_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd real Rd Rn size U s) := rfl

def obs_nop_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_nop_aarch64_instrs_system_hints op2 CRm) s
theorem obs_nop_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_nop_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_nop_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_nop_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not Rd Rn Q) s
theorem obs_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not real Rd Rn Q s =
      Arch.project .clause s (stateOf ((decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not Rd Rn Q) s)) (Clauses.obs_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not real Rd Rn Q s) := rfl

def obs_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size Q) s
theorem obs_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr real Rd Rn Rm size Q s =
      Arch.project .clause s (stateOf ((decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size Q) s)) (Clauses.obs_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr real Rd Rn Rm size Q s) := rfl

def obs_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s
theorem obs_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s =
      Arch.project .clause s (stateOf ((decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s)) (Clauses.obs_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s) := rfl

def obs_orr_advsimd_imm_aarch64_instrs_vector_logical (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_orr_advsimd_imm_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s
theorem obs_orr_advsimd_imm_aarch64_instrs_vector_logical_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_orr_advsimd_imm_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s =
      Arch.project .clause s (stateOf ((decode_orr_advsimd_imm_aarch64_instrs_vector_logical Rd h g f e d cmode c b a op Q) s)) (Clauses.obs_orr_advsimd_imm_aarch64_instrs_vector_logical real Rd h g f e d cmode c b a op Q s) := rfl

def obs_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size Q) s
theorem obs_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr real Rd Rn Rm size Q s =
      Arch.project .clause s (stateOf ((decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr Rd Rn Rm size Q) s)) (Clauses.obs_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr real Rd Rn Rm size Q s) := rfl

def obs_orr_log_imm_aarch64_instrs_integer_logical_immediate (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf) s
theorem obs_orr_log_imm_aarch64_instrs_integer_logical_immediate_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_orr_log_imm_aarch64_instrs_integer_logical_immediate real Rd Rn imms immr N opc sf s =
      Arch.project .clause s (stateOf ((decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf) s)) (Clauses.obs_orr_log_imm_aarch64_instrs_integer_logical_immediate real Rd Rn imms immr N opc sf s) := rfl

def obs_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s
theorem obs_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s =
      Arch.project .clause s (stateOf ((decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf) s)) (Clauses.obs_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg real Rd Rn imm6 Rm N shift opc sf s) := rfl

def obs_pacda_aarch64_instrs_integer_pac_pacda_dp_1src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_pacda_aarch64_instrs_integer_pac_pacda_dp_1src Rd Rn Z) s
theorem obs_pacda_aarch64_instrs_integer_pac_pacda_dp_1src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) :
    obs_pacda_aarch64_instrs_integer_pac_pacda_dp_1src real Rd Rn Z s =
      Arch.project .clause s (stateOf ((decode_pacda_aarch64_instrs_integer_pac_pacda_dp_1src Rd Rn Z) s)) (Clauses.obs_pacda_aarch64_instrs_integer_pac_pacda_dp_1src real Rd Rn Z s) := rfl

def obs_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src Rd Rn Z) s
theorem obs_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) :
    obs_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src real Rd Rn Z s =
      Arch.project .clause s (stateOf ((decode_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src Rd Rn Z) s)) (Clauses.obs_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src real Rd Rn Z s) := rfl

def obs_pacga_aarch64_instrs_integer_pac_pacga_dp_2src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_pacga_aarch64_instrs_integer_pac_pacga_dp_2src Rd Rn Rm) s
theorem obs_pacga_aarch64_instrs_integer_pac_pacga_dp_2src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_pacga_aarch64_instrs_integer_pac_pacga_dp_2src real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_pacga_aarch64_instrs_integer_pac_pacga_dp_2src Rd Rn Rm) s)) (Clauses.obs_pacga_aarch64_instrs_integer_pac_pacga_dp_2src real Rd Rn Rm s) := rfl

def obs_pacia_aarch64_instrs_integer_pac_pacia_dp_1src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_pacia_aarch64_instrs_integer_pac_pacia_dp_1src Rd Rn Z) s
theorem obs_pacia_aarch64_instrs_integer_pac_pacia_dp_1src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) :
    obs_pacia_aarch64_instrs_integer_pac_pacia_dp_1src real Rd Rn Z s =
      Arch.project .clause s (stateOf ((decode_pacia_aarch64_instrs_integer_pac_pacia_dp_1src Rd Rn Z) s)) (Clauses.obs_pacia_aarch64_instrs_integer_pac_pacia_dp_1src real Rd Rn Z s) := rfl

def obs_pacia_aarch64_instrs_integer_pac_pacia_hint (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_pacia_aarch64_instrs_integer_pac_pacia_hint op2 CRm) s
theorem obs_pacia_aarch64_instrs_integer_pac_pacia_hint_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_pacia_aarch64_instrs_integer_pac_pacia_hint real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_pacia_aarch64_instrs_integer_pac_pacia_hint op2 CRm) s)) (Clauses.obs_pacia_aarch64_instrs_integer_pac_pacia_hint real op2 CRm s) := rfl

def obs_pacib_aarch64_instrs_integer_pac_pacib_dp_1src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_pacib_aarch64_instrs_integer_pac_pacib_dp_1src Rd Rn Z) s
theorem obs_pacib_aarch64_instrs_integer_pac_pacib_dp_1src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) (s : State) :
    obs_pacib_aarch64_instrs_integer_pac_pacib_dp_1src real Rd Rn Z s =
      Arch.project .clause s (stateOf ((decode_pacib_aarch64_instrs_integer_pac_pacib_dp_1src Rd Rn Z) s)) (Clauses.obs_pacib_aarch64_instrs_integer_pac_pacib_dp_1src real Rd Rn Z s) := rfl

def obs_pacib_aarch64_instrs_integer_pac_pacib_hint (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_pacib_aarch64_instrs_integer_pac_pacib_hint op2 CRm) s
theorem obs_pacib_aarch64_instrs_integer_pac_pacib_hint_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_pacib_aarch64_instrs_integer_pac_pacib_hint real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_pacib_aarch64_instrs_integer_pac_pacib_hint op2 CRm) s)) (Clauses.obs_pacib_aarch64_instrs_integer_pac_pacib_hint real op2 CRm s) := rfl

def obs_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product Rd Rn Rm size U Q) s
theorem obs_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product Rd Rn Rm size U Q) s)) (Clauses.obs_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product real Rd Rn Rm size U Q s) := rfl

def obs_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly Rd Rn Rm size Q) s
theorem obs_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly real Rd Rn Rm size Q s =
      Arch.project .clause s (stateOf ((decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly Rd Rn Rm size Q) s)) (Clauses.obs_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly real Rd Rn Rm size Q s) := rfl

def obs_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_prfm_lit_aarch64_instrs_memory_literal_general (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_prfm_lit_aarch64_instrs_memory_literal_general Rt imm19 opc) s
theorem obs_prfm_lit_aarch64_instrs_memory_literal_general_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) (s : State) :
    obs_prfm_lit_aarch64_instrs_memory_literal_general real Rt imm19 opc s =
      Arch.project .clause s (stateOf ((decode_prfm_lit_aarch64_instrs_memory_literal_general Rt imm19 opc) s)) (Clauses.obs_prfm_lit_aarch64_instrs_memory_literal_general real Rt imm19 opc s) := rfl

def obs_prfm_reg_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_prfm_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_prfm_reg_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_prfm_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_prfm_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_prfm_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_psb_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_psb_aarch64_instrs_system_hints op2 CRm) s
theorem obs_psb_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_psb_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_psb_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_psb_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm size U Q) s
theorem obs_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm size U Q) s)) (Clauses.obs_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow real Rd Rn o1 Rm size U Q s) := rfl

def obs_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1 Rd Rn Rm) s
theorem obs_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1 real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1 Rd Rn Rm) s)) (Clauses.obs_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1 real Rd Rn Rm s) := rfl

def obs_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit Rd Rn Q) s
theorem obs_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit real Rd Rn Q s =
      Arch.project .clause s (stateOf ((decode_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit Rd Rn Q) s)) (Clauses.obs_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit real Rd Rn Q s) := rfl

def obs_rbit_int_aarch64_instrs_integer_arithmetic_rbit (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit Rd Rn sf) s
theorem obs_rbit_int_aarch64_instrs_integer_arithmetic_rbit_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_rbit_int_aarch64_instrs_integer_arithmetic_rbit real Rd Rn sf s =
      Arch.project .clause s (stateOf ((decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit Rd Rn sf) s)) (Clauses.obs_rbit_int_aarch64_instrs_integer_arithmetic_rbit real Rd Rn sf s) := rfl

def obs_ret_aarch64_instrs_branch_unconditional_register (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ret_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s
theorem obs_ret_aarch64_instrs_branch_unconditional_register_mapping (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) :
    obs_ret_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s =
      Arch.project .clause s (stateOf ((decode_ret_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s)) (Clauses.obs_ret_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s) := rfl

def obs_reta_aarch64_instrs_branch_unconditional_register (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_reta_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s
theorem obs_reta_aarch64_instrs_branch_unconditional_register_mapping (real : Type) [SailReal real] (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) (s : State) :
    obs_reta_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s =
      Arch.project .clause s (stateOf ((decode_reta_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z) s)) (Clauses.obs_reta_aarch64_instrs_branch_unconditional_register real Rm Rn M A op Z s) := rfl

def obs_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 size U Q) s
theorem obs_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev real Rd Rn o0 size U Q s =
      Arch.project .clause s (stateOf ((decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 size U Q) s)) (Clauses.obs_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev real Rd Rn o0 size U Q s) := rfl

def obs_rev16_int_aarch64_instrs_integer_arithmetic_rev (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rev16_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc sf) s
theorem obs_rev16_int_aarch64_instrs_integer_arithmetic_rev_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_rev16_int_aarch64_instrs_integer_arithmetic_rev real Rd Rn opc sf s =
      Arch.project .clause s (stateOf ((decode_rev16_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc sf) s)) (Clauses.obs_rev16_int_aarch64_instrs_integer_arithmetic_rev real Rd Rn opc sf s) := rfl

def obs_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 size U Q) s
theorem obs_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev real Rd Rn o0 size U Q s =
      Arch.project .clause s (stateOf ((decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 size U Q) s)) (Clauses.obs_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev real Rd Rn o0 size U Q s) := rfl

def obs_rev32_int_aarch64_instrs_integer_arithmetic_rev (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rev32_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc sf) s
theorem obs_rev32_int_aarch64_instrs_integer_arithmetic_rev_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_rev32_int_aarch64_instrs_integer_arithmetic_rev real Rd Rn opc sf s =
      Arch.project .clause s (stateOf ((decode_rev32_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc sf) s)) (Clauses.obs_rev32_int_aarch64_instrs_integer_arithmetic_rev real Rd Rn opc sf s) := rfl

def obs_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 size U Q) s
theorem obs_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev real Rd Rn o0 size U Q s =
      Arch.project .clause s (stateOf ((decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev Rd Rn o0 size U Q) s)) (Clauses.obs_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev real Rd Rn o0 size U Q s) := rfl

def obs_rev_aarch64_instrs_integer_arithmetic_rev (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rev_aarch64_instrs_integer_arithmetic_rev Rd Rn opc sf) s
theorem obs_rev_aarch64_instrs_integer_arithmetic_rev_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_rev_aarch64_instrs_integer_arithmetic_rev real Rd Rn opc sf s =
      Arch.project .clause s (stateOf ((decode_rev_aarch64_instrs_integer_arithmetic_rev Rd Rn opc sf) s)) (Clauses.obs_rev_aarch64_instrs_integer_arithmetic_rev real Rd Rn opc sf s) := rfl

def obs_rmif_aarch64_instrs_integer_flags_rmif (real : Type) [SailReal real] (mask : (BitVec 4)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rmif_aarch64_instrs_integer_flags_rmif mask Rn imm6 sf) s
theorem obs_rmif_aarch64_instrs_integer_flags_rmif_mapping (real : Type) [SailReal real] (mask : (BitVec 4)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (sf : (BitVec 1)) (s : State) :
    obs_rmif_aarch64_instrs_integer_flags_rmif real mask Rn imm6 sf s =
      Arch.project .clause s (stateOf ((decode_rmif_aarch64_instrs_integer_flags_rmif mask Rn imm6 sf) s)) (Clauses.obs_rmif_aarch64_instrs_integer_flags_rmif real mask Rn imm6 sf s) := rfl

def obs_rorv_aarch64_instrs_integer_shift_variable (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rorv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf) s
theorem obs_rorv_aarch64_instrs_integer_shift_variable_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_rorv_aarch64_instrs_integer_shift_variable real Rd Rn op2 Rm sf s =
      Arch.project .clause s (stateOf ((decode_rorv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf) s)) (Clauses.obs_rorv_aarch64_instrs_integer_shift_variable real Rd Rn op2 Rm sf s) := rfl

def obs_rprfm_reg_aarch64_instrs_memory_single_general_range (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rprfm_reg_aarch64_instrs_memory_single_general_range Rt Rn S option_name Rm opc size) s
theorem obs_rprfm_reg_aarch64_instrs_memory_single_general_range_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_rprfm_reg_aarch64_instrs_memory_single_general_range real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_rprfm_reg_aarch64_instrs_memory_single_general_range Rt Rn S option_name Rm opc size) s)) (Clauses.obs_rprfm_reg_aarch64_instrs_memory_single_general_range real Rt Rn S option_name Rm opc size s) := rfl

def obs_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical Rd Rn op immb immh Q) s
theorem obs_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) :
    obs_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical real Rd Rn op immb immh Q s =
      Arch.project .clause s (stateOf ((decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical Rd Rn op immb immh Q) s)) (Clauses.obs_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical real Rd Rn op immb immh Q s) := rfl

def obs_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm size U Q) s
theorem obs_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm size U Q) s)) (Clauses.obs_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow real Rd Rn o1 Rm size U Q s) := rfl

def obs_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm size U Q) s
theorem obs_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff real Rd Rn ac Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm size U Q) s)) (Clauses.obs_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff real Rd Rn ac Rm size U Q s) := rfl

def obs_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm size U Q) s
theorem obs_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff real Rd Rn op Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm size U Q) s)) (Clauses.obs_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff real Rd Rn op Rm size U Q s) := rfl

def obs_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm size U Q) s
theorem obs_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff real Rd Rn ac Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm size U Q) s)) (Clauses.obs_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff real Rd Rn ac Rm size U Q s) := rfl

def obs_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm size U Q) s
theorem obs_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff real Rd Rn op Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm size U Q) s)) (Clauses.obs_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff real Rd Rn op Rm size U Q s) := rfl

def obs_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op size U Q) s
theorem obs_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op size U Q) s)) (Clauses.obs_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise real Rd Rn op size U Q s) := rfl

def obs_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm size U Q) s
theorem obs_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm size U Q) s)) (Clauses.obs_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long real Rd Rn o1 Rm size U Q s) := rfl

def obs_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op size U Q) s
theorem obs_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op size U Q) s)) (Clauses.obs_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise real Rd Rn op size U Q s) := rfl

def obs_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long Rd Rn size U Q) s
theorem obs_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long Rd Rn size U Q) s)) (Clauses.obs_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long real Rd Rn size U Q s) := rfl

def obs_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm size U Q) s
theorem obs_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm size U Q) s)) (Clauses.obs_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide real Rd Rn o1 Rm size U Q s) := rfl

def obs_sb_aarch64_instrs_system_barriers_sb (real : Type) [SailReal real] (opc : (BitVec 2)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sb_aarch64_instrs_system_barriers_sb opc CRm) s
theorem obs_sb_aarch64_instrs_system_barriers_sb_mapping (real : Type) [SailReal real] (opc : (BitVec 2)) (CRm : (BitVec 4)) (s : State) :
    obs_sb_aarch64_instrs_system_barriers_sb real opc CRm s =
      Arch.project .clause s (stateOf ((decode_sb_aarch64_instrs_system_barriers_sb opc CRm) s)) (Clauses.obs_sb_aarch64_instrs_system_barriers_sb real opc CRm s) := rfl

def obs_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf) s
theorem obs_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry real Rd Rn Rm S op sf s =
      Arch.project .clause s (stateOf ((decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf) s)) (Clauses.obs_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry real Rd Rn Rm S op sf s) := rfl

def obs_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf) s
theorem obs_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry real Rd Rn Rm S op sf s =
      Arch.project .clause s (stateOf ((decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf) s)) (Clauses.obs_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry real Rd Rn Rm S op sf s) := rfl

def obs_sbfm_aarch64_instrs_integer_bitfield (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sbfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc sf) s
theorem obs_sbfm_aarch64_instrs_integer_bitfield_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_sbfm_aarch64_instrs_integer_bitfield real Rd Rn imms immr N opc sf s =
      Arch.project .clause s (stateOf ((decode_sbfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc sf) s)) (Clauses.obs_sbfm_aarch64_instrs_integer_bitfield real Rd Rn imms immr N opc sf s) := rfl

def obs_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd Rd Rn immb immh U Q) s
theorem obs_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd real Rd Rn immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd Rd Rn immb immh U Q) s)) (Clauses.obs_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd real Rd Rn immb immh U Q s) := rfl

def obs_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd Rd Rn immb immh U) s
theorem obs_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd real Rd Rn immb immh U s =
      Arch.project .clause s (stateOf ((decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd Rd Rn immb immh U) s)) (Clauses.obs_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd real Rd Rn immb immh U s) := rfl

def obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd Rd Rn sz U Q) s
theorem obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd real Rd Rn sz U Q s =
      Arch.project .clause s (stateOf ((decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd Rd Rn sz U Q) s)) (Clauses.obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd real Rd Rn sz U Q s) := rfl

def obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd Rd Rn sz U) s
theorem obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd real Rd Rn sz U s =
      Arch.project .clause s (stateOf ((decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd Rd Rn sz U) s)) (Clauses.obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd real Rd Rn sz U s) := rfl

def obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd Rd Rn U Q) s
theorem obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd real Rd Rn U Q s =
      Arch.project .clause s (stateOf ((decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd Rd Rn U Q) s)) (Clauses.obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd real Rd Rn U Q s) := rfl

def obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd Rd Rn U) s
theorem obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd real Rd Rn U s =
      Arch.project .clause s (stateOf ((decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd Rd Rn U) s)) (Clauses.obs_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd real Rd Rn U s) := rfl

def obs_scvtf_float_fix_aarch64_instrs_float_convert_fix (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_scvtf_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode ftype sf) s
theorem obs_scvtf_float_fix_aarch64_instrs_float_convert_fix_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_scvtf_float_fix_aarch64_instrs_float_convert_fix real Rd Rn scale opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_scvtf_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode ftype sf) s)) (Clauses.obs_scvtf_float_fix_aarch64_instrs_float_convert_fix real Rd Rn scale opcode rmode ftype sf s) := rfl

def obs_scvtf_float_int_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_scvtf_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_scvtf_float_int_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_scvtf_float_int_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_scvtf_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_scvtf_float_int_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_sdiv_aarch64_instrs_integer_arithmetic_div (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sdiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm sf) s
theorem obs_sdiv_aarch64_instrs_integer_arithmetic_div_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_sdiv_aarch64_instrs_integer_arithmetic_div real Rd Rn o1 Rm sf s =
      Arch.project .clause s (stateOf ((decode_sdiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm sf) s)) (Clauses.obs_sdiv_aarch64_instrs_integer_arithmetic_div real Rd Rn o1 Rm sf s) := rfl

def obs_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp Rd Rn H Rm M L size U Q) s
theorem obs_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp real Rd Rn H Rm M L size U Q s =
      Arch.project .clause s (stateOf ((decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp Rd Rn H Rm M L size U Q) s)) (Clauses.obs_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp real Rd Rn H Rm M L size U Q s) := rfl

def obs_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp Rd Rn Rm size U Q) s
theorem obs_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp Rd Rn Rm size U Q) s)) (Clauses.obs_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp real Rd Rn Rm size U Q s) := rfl

def obs_setf_aarch64_instrs_integer_flags_setf (real : Type) [SailReal real] (Rn : (BitVec 5)) (sz : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_setf_aarch64_instrs_integer_flags_setf Rn sz sf) s
theorem obs_setf_aarch64_instrs_integer_flags_setf_mapping (real : Type) [SailReal real] (Rn : (BitVec 5)) (sz : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_setf_aarch64_instrs_integer_flags_setf real Rn sz sf s =
      Arch.project .clause s (stateOf ((decode_setf_aarch64_instrs_integer_flags_setf Rn sz sf) s)) (Clauses.obs_setf_aarch64_instrs_integer_flags_setf real Rn sz sf s) := rfl

def obs_sev_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sev_aarch64_instrs_system_hints op2 CRm) s
theorem obs_sev_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_sev_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_sev_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_sev_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_sevl_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sevl_aarch64_instrs_system_hints op2 CRm) s
theorem obs_sevl_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_sevl_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_sevl_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_sevl_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose Rd Rn Rm) s
theorem obs_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose Rd Rn Rm) s)) (Clauses.obs_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose real Rd Rn Rm s) := rfl

def obs_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash Rd Rn) s
theorem obs_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) :
    obs_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash real Rd Rn s =
      Arch.project .clause s (stateOf ((decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash Rd Rn) s)) (Clauses.obs_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash real Rd Rn s) := rfl

def obs_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority Rd Rn Rm) s
theorem obs_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority Rd Rn Rm) s)) (Clauses.obs_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority real Rd Rn Rm s) := rfl

def obs_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity Rd Rn Rm) s
theorem obs_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity Rd Rn Rm) s)) (Clauses.obs_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity real Rd Rn Rm s) := rfl

def obs_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 Rd Rn Rm) s
theorem obs_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 Rd Rn Rm) s)) (Clauses.obs_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 real Rd Rn Rm s) := rfl

def obs_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 Rd Rn) s
theorem obs_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) :
    obs_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 real Rd Rn s =
      Arch.project .clause s (stateOf ((decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 Rd Rn) s)) (Clauses.obs_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 real Rd Rn s) := rfl

def obs_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash Rd Rn P Rm) s
theorem obs_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) (s : State) :
    obs_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash real Rd Rn P Rm s =
      Arch.project .clause s (stateOf ((decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash Rd Rn P Rm) s)) (Clauses.obs_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash real Rd Rn P Rm s) := rfl

def obs_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash Rd Rn P Rm) s
theorem obs_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) (s : State) :
    obs_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash real Rd Rn P Rm s =
      Arch.project .clause s (stateOf ((decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash Rd Rn P Rm) s)) (Clauses.obs_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash real Rd Rn P Rm s) := rfl

def obs_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 Rd Rn) s
theorem obs_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) :
    obs_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 real Rd Rn s =
      Arch.project .clause s (stateOf ((decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 Rd Rn) s)) (Clauses.obs_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 real Rd Rn s) := rfl

def obs_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 Rd Rn Rm) s
theorem obs_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 Rd Rn Rm) s)) (Clauses.obs_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 real Rd Rn Rm s) := rfl

def obs_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 Rd Rn Rm) s
theorem obs_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 Rd Rn Rm) s)) (Clauses.obs_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 real Rd Rn Rm s) := rfl

def obs_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h Rd Rn Rm) s
theorem obs_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h Rd Rn Rm) s)) (Clauses.obs_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h real Rd Rn Rm s) := rfl

def obs_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 Rd Rn) s
theorem obs_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) :
    obs_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 real Rd Rn s =
      Arch.project .clause s (stateOf ((decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 Rd Rn) s)) (Clauses.obs_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 real Rd Rn s) := rfl

def obs_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 Rd Rn Rm) s
theorem obs_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 Rd Rn Rm) s)) (Clauses.obs_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 real Rd Rn Rm s) := rfl

def obs_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating Rd Rn Rm size U Q) s
theorem obs_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating Rd Rn Rm size U Q) s)) (Clauses.obs_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating real Rd Rn Rm size U Q s) := rfl

def obs_shl_advsimd_aarch64_instrs_vector_shift_left_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd Rd Rn immb immh Q) s
theorem obs_shl_advsimd_aarch64_instrs_vector_shift_left_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) :
    obs_shl_advsimd_aarch64_instrs_vector_shift_left_simd real Rd Rn immb immh Q s =
      Arch.project .clause s (stateOf ((decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd Rd Rn immb immh Q) s)) (Clauses.obs_shl_advsimd_aarch64_instrs_vector_shift_left_simd real Rd Rn immb immh Q s) := rfl

def obs_shl_advsimd_aarch64_instrs_vector_shift_left_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd Rd Rn immb immh) s
theorem obs_shl_advsimd_aarch64_instrs_vector_shift_left_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) :
    obs_shl_advsimd_aarch64_instrs_vector_shift_left_sisd real Rd Rn immb immh s =
      Arch.project .clause s (stateOf ((decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd Rd Rn immb immh) s)) (Clauses.obs_shl_advsimd_aarch64_instrs_vector_shift_left_sisd real Rd Rn immb immh s) := rfl

def obs_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift Rd Rn size Q) s
theorem obs_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift real Rd Rn size Q s =
      Arch.project .clause s (stateOf ((decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift Rd Rn size Q) s)) (Clauses.obs_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift real Rd Rn size Q s) := rfl

def obs_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical Rd Rn op immb immh Q) s
theorem obs_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) :
    obs_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical real Rd Rn op immb immh Q s =
      Arch.project .clause s (stateOf ((decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical Rd Rn op immb immh Q) s)) (Clauses.obs_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical real Rd Rn op immb immh Q s) := rfl

def obs_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int Rd Rn Rm size U Q) s
theorem obs_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int Rd Rn Rm size U Q) s)) (Clauses.obs_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int real Rd Rn Rm size U Q s) := rfl

def obs_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd Rd Rn immb immh Q) s
theorem obs_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) :
    obs_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd real Rd Rn immb immh Q s =
      Arch.project .clause s (stateOf ((decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd Rd Rn immb immh Q) s)) (Clauses.obs_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd real Rd Rn immb immh Q s) := rfl

def obs_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd Rd Rn immb immh) s
theorem obs_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) :
    obs_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd real Rd Rn immb immh s =
      Arch.project .clause s (stateOf ((decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd Rd Rn immb immh) s)) (Clauses.obs_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd real Rd Rn immb immh s) := rfl

def obs_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1 Rd Rn Rm) s
theorem obs_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1 real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1 Rd Rn Rm) s)) (Clauses.obs_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1 real Rd Rn Rm s) := rfl

def obs_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 Rd Rn Rm) s
theorem obs_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 Rd Rn Rm) s)) (Clauses.obs_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 real Rd Rn Rm s) := rfl

def obs_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 Rd Rn Ra Rm) s
theorem obs_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 real Rd Rn Ra Rm s =
      Arch.project .clause s (stateOf ((decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 Rd Rn Ra Rm) s)) (Clauses.obs_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 real Rd Rn Ra Rm s) := rfl

def obs_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a Rd Rn imm2 Rm) s
theorem obs_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) (s : State) :
    obs_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a real Rd Rn imm2 Rm s =
      Arch.project .clause s (stateOf ((decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a Rd Rn imm2 Rm) s)) (Clauses.obs_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a real Rd Rn imm2 Rm s) := rfl

def obs_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b Rd Rn imm2 Rm) s
theorem obs_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) (s : State) :
    obs_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b real Rd Rn imm2 Rm s =
      Arch.project .clause s (stateOf ((decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b Rd Rn imm2 Rm) s)) (Clauses.obs_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b real Rd Rn imm2 Rm s) := rfl

def obs_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a Rd Rn imm2 Rm) s
theorem obs_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) (s : State) :
    obs_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a real Rd Rn imm2 Rm s =
      Arch.project .clause s (stateOf ((decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a Rd Rn imm2 Rm) s)) (Clauses.obs_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a real Rd Rn imm2 Rm s) := rfl

def obs_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b Rd Rn imm2 Rm) s
theorem obs_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) (s : State) :
    obs_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b real Rd Rn imm2 Rm s =
      Arch.project .clause s (stateOf ((decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b Rd Rn imm2 Rm) s)) (Clauses.obs_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b real Rd Rn imm2 Rm s) := rfl

def obs_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc Rd Rn) s
theorem obs_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (s : State) :
    obs_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc real Rd Rn s =
      Arch.project .clause s (stateOf ((decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc Rd Rn) s)) (Clauses.obs_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc real Rd Rn s) := rfl

def obs_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey Rd Rn Rm) s
theorem obs_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (s : State) :
    obs_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey real Rd Rn Rm s =
      Arch.project .clause s (stateOf ((decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey Rd Rn Rm) s)) (Clauses.obs_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey real Rd Rn Rm s) := rfl

def obs_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s
theorem obs_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 real Rd Rn Ra o0 Rm U s =
      Arch.project .clause s (stateOf ((decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s)) (Clauses.obs_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 real Rd Rn Ra o0 Rm U s) := rfl

def obs_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm size U Q) s
theorem obs_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm size U Q) s)) (Clauses.obs_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single real Rd Rn o1 Rm size U Q s) := rfl

def obs_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg Rd Rn Rm sf) s
theorem obs_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg real Rd Rn Rm sf s =
      Arch.project .clause s (stateOf ((decode_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg Rd Rn Rm sf) s)) (Clauses.obs_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg real Rd Rn Rm sf s) := rfl

def obs_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm size U Q) s
theorem obs_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm size U Q) s)) (Clauses.obs_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair real Rd Rn o1 Rm size U Q s) := rfl

def obs_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q) s
theorem obs_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q) s)) (Clauses.obs_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max real Rd Rn op size U Q s) := rfl

def obs_smc_aarch64_instrs_system_exceptions_runtime_smc (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smc_aarch64_instrs_system_exceptions_runtime_smc imm16) s
theorem obs_smc_aarch64_instrs_system_exceptions_runtime_smc_mapping (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) :
    obs_smc_aarch64_instrs_system_exceptions_runtime_smc real imm16 s =
      Arch.project .clause s (stateOf ((decode_smc_aarch64_instrs_system_exceptions_runtime_smc imm16) s)) (Clauses.obs_smc_aarch64_instrs_system_exceptions_runtime_smc real imm16 s) := rfl

def obs_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm size U Q) s
theorem obs_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm size U Q) s)) (Clauses.obs_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single real Rd Rn o1 Rm size U Q s) := rfl

def obs_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg Rd Rn Rm sf) s
theorem obs_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg real Rd Rn Rm sf s =
      Arch.project .clause s (stateOf ((decode_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg Rd Rn Rm sf) s)) (Clauses.obs_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg real Rd Rn Rm sf s) := rfl

def obs_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm size U Q) s
theorem obs_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm size U Q) s)) (Clauses.obs_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair real Rd Rn o1 Rm size U Q s) := rfl

def obs_sminv_advsimd_aarch64_instrs_vector_reduce_int_max (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q) s
theorem obs_sminv_advsimd_aarch64_instrs_vector_reduce_int_max_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sminv_advsimd_aarch64_instrs_vector_reduce_int_max real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q) s)) (Clauses.obs_sminv_advsimd_aarch64_instrs_vector_reduce_int_max real Rd Rn op size U Q s) := rfl

def obs_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn H o2 Rm M L size U Q) s
theorem obs_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long real Rd Rn H o2 Rm M L size U Q s =
      Arch.project .clause s (stateOf ((decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn H o2 Rm M L size U Q) s)) (Clauses.obs_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long real Rd Rn H o2 Rm M L size U Q s) := rfl

def obs_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm size U Q) s
theorem obs_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm size U Q) s)) (Clauses.obs_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum real Rd Rn o1 Rm size U Q s) := rfl

def obs_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn H o2 Rm M L size U Q) s
theorem obs_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long real Rd Rn H o2 Rm M L size U Q s =
      Arch.project .clause s (stateOf ((decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn H o2 Rm M L size U Q) s)) (Clauses.obs_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long real Rd Rn H o2 Rm M L size U Q s) := rfl

def obs_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm size U Q) s
theorem obs_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm size U Q) s)) (Clauses.obs_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum real Rd Rn o1 Rm size U Q s) := rfl

def obs_smmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla Rd Rn B Rm U) s
theorem obs_smmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_smmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla real Rd Rn B Rm U s =
      Arch.project .clause s (stateOf ((decode_smmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla Rd Rn B Rm U) s)) (Clauses.obs_smmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla real Rd Rn B Rm U s) := rfl

def obs_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed Rd Rn imm5 Q) s
theorem obs_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed real Rd Rn imm5 Q s =
      Arch.project .clause s (stateOf ((decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed Rd Rn imm5 Q) s)) (Clauses.obs_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed real Rd Rn imm5 Q s) := rfl

def obs_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s
theorem obs_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 real Rd Rn Ra o0 Rm U s =
      Arch.project .clause s (stateOf ((decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s)) (Clauses.obs_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 real Rd Rn Ra o0 Rm U s) := rfl

def obs_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U) s
theorem obs_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi real Rd Rn Ra Rm U s =
      Arch.project .clause s (stateOf ((decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U) s)) (Clauses.obs_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi real Rd Rn Ra Rm U s) := rfl

def obs_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long Rd Rn H Rm M L size U Q) s
theorem obs_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long real Rd Rn H Rm M L size U Q s =
      Arch.project .clause s (stateOf ((decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long Rd Rn H Rm M L size U Q) s)) (Clauses.obs_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long real Rd Rn H Rm M L size U Q s) := rfl

def obs_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product Rd Rn Rm size U Q) s
theorem obs_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product Rd Rn Rm size U Q) s)) (Clauses.obs_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product real Rd Rn Rm size U Q s) := rfl

def obs_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd Rd Rn size U Q) s
theorem obs_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd Rd Rn size U Q) s)) (Clauses.obs_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd real Rd Rn size U Q s) := rfl

def obs_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd Rd Rn size U) s
theorem obs_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd real Rd Rn size U s =
      Arch.project .clause s (stateOf ((decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd Rd Rn size U) s)) (Clauses.obs_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd real Rd Rn size U s) := rfl

def obs_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd Rd Rn Rm size U Q) s
theorem obs_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd Rd Rn Rm size U Q) s)) (Clauses.obs_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd real Rd Rn Rm size U Q s) := rfl

def obs_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd Rd Rn Rm size U) s
theorem obs_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd Rd Rn Rm size U) s)) (Clauses.obs_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd real Rd Rn Rm size U s) := rfl

def obs_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd Rd Rn H o2 Rm M L size Q) s
theorem obs_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd real Rd Rn H o2 Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd Rd Rn H o2 Rm M L size Q) s)) (Clauses.obs_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd real Rd Rn H o2 Rm M L size Q s) := rfl

def obs_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd Rd Rn H o2 Rm M L size) s
theorem obs_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd real Rd Rn H o2 Rm M L size s =
      Arch.project .clause s (stateOf ((decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd Rd Rn H o2 Rm M L size) s)) (Clauses.obs_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd real Rd Rn H o2 Rm M L size s) := rfl

def obs_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd Rd Rn o1 Rm size Q) s
theorem obs_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd real Rd Rn o1 Rm size Q s =
      Arch.project .clause s (stateOf ((decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd Rd Rn o1 Rm size Q) s)) (Clauses.obs_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd real Rd Rn o1 Rm size Q s) := rfl

def obs_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd Rd Rn o1 Rm size) s
theorem obs_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd real Rd Rn o1 Rm size s =
      Arch.project .clause s (stateOf ((decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd Rd Rn o1 Rm size) s)) (Clauses.obs_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd real Rd Rn o1 Rm size s) := rfl

def obs_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd Rd Rn H o2 Rm M L size Q) s
theorem obs_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd real Rd Rn H o2 Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd Rd Rn H o2 Rm M L size Q) s)) (Clauses.obs_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd real Rd Rn H o2 Rm M L size Q s) := rfl

def obs_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd Rd Rn H o2 Rm M L size) s
theorem obs_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd real Rd Rn H o2 Rm M L size s =
      Arch.project .clause s (stateOf ((decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd Rd Rn H o2 Rm M L size) s)) (Clauses.obs_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd real Rd Rn H o2 Rm M L size s) := rfl

def obs_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd Rd Rn o1 Rm size Q) s
theorem obs_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd real Rd Rn o1 Rm size Q s =
      Arch.project .clause s (stateOf ((decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd Rd Rn o1 Rm size Q) s)) (Clauses.obs_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd real Rd Rn o1 Rm size Q s) := rfl

def obs_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd Rd Rn o1 Rm size) s
theorem obs_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd real Rd Rn o1 Rm size s =
      Arch.project .clause s (stateOf ((decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd Rd Rn o1 Rm size) s)) (Clauses.obs_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd real Rd Rn o1 Rm size s) := rfl

def obs_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd Rd Rn H op Rm M L size Q) s
theorem obs_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd real Rd Rn H op Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd Rd Rn H op Rm M L size Q) s)) (Clauses.obs_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd real Rd Rn H op Rm M L size Q s) := rfl

def obs_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd Rd Rn H op Rm M L size) s
theorem obs_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd real Rd Rn H op Rm M L size s =
      Arch.project .clause s (stateOf ((decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd Rd Rn H op Rm M L size) s)) (Clauses.obs_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd real Rd Rn H op Rm M L size s) := rfl

def obs_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd Rd Rn Rm size U Q) s
theorem obs_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd Rd Rn Rm size U Q) s)) (Clauses.obs_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd real Rd Rn Rm size U Q s) := rfl

def obs_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd Rd Rn Rm size U) s
theorem obs_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd Rd Rn Rm size U) s)) (Clauses.obs_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd real Rd Rn Rm size U s) := rfl

def obs_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd Rd Rn H Rm M L size Q) s
theorem obs_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd real Rd Rn H Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd Rd Rn H Rm M L size Q) s)) (Clauses.obs_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd real Rd Rn H Rm M L size Q s) := rfl

def obs_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd Rd Rn H Rm M L size) s
theorem obs_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd real Rd Rn H Rm M L size s =
      Arch.project .clause s (stateOf ((decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd Rd Rn H Rm M L size) s)) (Clauses.obs_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd real Rd Rn H Rm M L size s) := rfl

def obs_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd Rd Rn Rm size Q) s
theorem obs_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd real Rd Rn Rm size Q s =
      Arch.project .clause s (stateOf ((decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd Rd Rn Rm size Q) s)) (Clauses.obs_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd real Rd Rn Rm size Q s) := rfl

def obs_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd Rd Rn Rm size) s
theorem obs_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd real Rd Rn Rm size s =
      Arch.project .clause s (stateOf ((decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd Rd Rn Rm size) s)) (Clauses.obs_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd real Rd Rn Rm size s) := rfl

def obs_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd Rd Rn size U Q) s
theorem obs_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd Rd Rn size U Q) s)) (Clauses.obs_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd real Rd Rn size U Q s) := rfl

def obs_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd Rd Rn size U) s
theorem obs_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd real Rd Rn size U s =
      Arch.project .clause s (stateOf ((decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd Rd Rn size U) s)) (Clauses.obs_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd real Rd Rn size U s) := rfl

def obs_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd Rd Rn H S Rm M L size Q) s
theorem obs_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd real Rd Rn H S Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd Rd Rn H S Rm M L size Q) s)) (Clauses.obs_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd real Rd Rn H S Rm M L size Q s) := rfl

def obs_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd Rd Rn H S Rm M L size) s
theorem obs_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd real Rd Rn H S Rm M L size s =
      Arch.project .clause s (stateOf ((decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd Rd Rn H S Rm M L size) s)) (Clauses.obs_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd real Rd Rn H S Rm M L size s) := rfl

def obs_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd Rd Rn S Rm size Q) s
theorem obs_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd real Rd Rn S Rm size Q s =
      Arch.project .clause s (stateOf ((decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd Rd Rn S Rm size Q) s)) (Clauses.obs_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd real Rd Rn S Rm size Q s) := rfl

def obs_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd Rd Rn S Rm size) s
theorem obs_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd real Rd Rn S Rm size s =
      Arch.project .clause s (stateOf ((decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd Rd Rn S Rm size) s)) (Clauses.obs_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd real Rd Rn S Rm size s) := rfl

def obs_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd Rd Rn H S Rm M L size Q) s
theorem obs_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd real Rd Rn H S Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd Rd Rn H S Rm M L size Q) s)) (Clauses.obs_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd real Rd Rn H S Rm M L size Q s) := rfl

def obs_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd Rd Rn H S Rm M L size) s
theorem obs_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd real Rd Rn H S Rm M L size s =
      Arch.project .clause s (stateOf ((decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd Rd Rn H S Rm M L size) s)) (Clauses.obs_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd real Rd Rn H S Rm M L size s) := rfl

def obs_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd Rd Rn S Rm size Q) s
theorem obs_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd real Rd Rn S Rm size Q s =
      Arch.project .clause s (stateOf ((decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd Rd Rn S Rm size Q) s)) (Clauses.obs_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd real Rd Rn S Rm size Q s) := rfl

def obs_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd Rd Rn S Rm size) s
theorem obs_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd real Rd Rn S Rm size s =
      Arch.project .clause s (stateOf ((decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd Rd Rn S Rm size) s)) (Clauses.obs_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd real Rd Rn S Rm size s) := rfl

def obs_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd Rd Rn H op Rm M L size Q) s
theorem obs_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd real Rd Rn H op Rm M L size Q s =
      Arch.project .clause s (stateOf ((decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd Rd Rn H op Rm M L size Q) s)) (Clauses.obs_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd real Rd Rn H op Rm M L size Q s) := rfl

def obs_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd Rd Rn H op Rm M L size) s
theorem obs_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd real Rd Rn H op Rm M L size s =
      Arch.project .clause s (stateOf ((decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd Rd Rn H op Rm M L size) s)) (Clauses.obs_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd real Rd Rn H op Rm M L size s) := rfl

def obs_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd Rd Rn Rm size U Q) s
theorem obs_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd Rd Rn Rm size U Q) s)) (Clauses.obs_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd real Rd Rn Rm size U Q s) := rfl

def obs_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd Rd Rn Rm size U) s
theorem obs_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd Rd Rn Rm size U) s)) (Clauses.obs_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd real Rd Rn Rm size U s) := rfl

def obs_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s
theorem obs_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s)) (Clauses.obs_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s) := rfl

def obs_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s
theorem obs_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s =
      Arch.project .clause s (stateOf ((decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s)) (Clauses.obs_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s) := rfl

def obs_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb immh U Q) s
theorem obs_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd real Rd Rn op immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb immh U Q) s)) (Clauses.obs_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd real Rd Rn op immb immh U Q s) := rfl

def obs_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb immh U) s
theorem obs_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd real Rd Rn op immb immh U s =
      Arch.project .clause s (stateOf ((decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb immh U) s)) (Clauses.obs_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd real Rd Rn op immb immh U s) := rfl

def obs_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd Rd Rn op immb immh Q) s
theorem obs_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) :
    obs_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd real Rd Rn op immb immh Q s =
      Arch.project .clause s (stateOf ((decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd Rd Rn op immb immh Q) s)) (Clauses.obs_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd real Rd Rn op immb immh Q s) := rfl

def obs_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd Rd Rn op immb immh) s
theorem obs_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) :
    obs_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd real Rd Rn op immb immh s =
      Arch.project .clause s (stateOf ((decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd Rd Rn op immb immh) s)) (Clauses.obs_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd real Rd Rn op immb immh s) := rfl

def obs_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb immh U Q) s
theorem obs_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd real Rd Rn op immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb immh U Q) s)) (Clauses.obs_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd real Rd Rn op immb immh U Q s) := rfl

def obs_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb immh U) s
theorem obs_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd real Rd Rn op immb immh U s =
      Arch.project .clause s (stateOf ((decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb immh U) s)) (Clauses.obs_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd real Rd Rn op immb immh U s) := rfl

def obs_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s
theorem obs_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s)) (Clauses.obs_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s) := rfl

def obs_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s
theorem obs_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s =
      Arch.project .clause s (stateOf ((decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s)) (Clauses.obs_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s) := rfl

def obs_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb immh U Q) s
theorem obs_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd real Rd Rn op immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb immh U Q) s)) (Clauses.obs_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd real Rd Rn op immb immh U Q s) := rfl

def obs_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb immh U) s
theorem obs_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd real Rd Rn op immb immh U s =
      Arch.project .clause s (stateOf ((decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb immh U) s)) (Clauses.obs_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd real Rd Rn op immb immh U s) := rfl

def obs_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb immh U Q) s
theorem obs_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd real Rd Rn op immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb immh U Q) s)) (Clauses.obs_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd real Rd Rn op immb immh U Q s) := rfl

def obs_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb immh U) s
theorem obs_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd real Rd Rn op immb immh U s =
      Arch.project .clause s (stateOf ((decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb immh U) s)) (Clauses.obs_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd real Rd Rn op immb immh U s) := rfl

def obs_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd Rd Rn op immb immh Q) s
theorem obs_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) :
    obs_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd real Rd Rn op immb immh Q s =
      Arch.project .clause s (stateOf ((decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd Rd Rn op immb immh Q) s)) (Clauses.obs_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd real Rd Rn op immb immh Q s) := rfl

def obs_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd Rd Rn op immb immh) s
theorem obs_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) :
    obs_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd real Rd Rn op immb immh s =
      Arch.project .clause s (stateOf ((decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd Rd Rn op immb immh) s)) (Clauses.obs_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd real Rd Rn op immb immh s) := rfl

def obs_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd Rd Rn Rm size U Q) s
theorem obs_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd Rd Rn Rm size U Q) s)) (Clauses.obs_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd real Rd Rn Rm size U Q s) := rfl

def obs_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd Rd Rn Rm size U) s
theorem obs_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd Rd Rn Rm size U) s)) (Clauses.obs_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd real Rd Rn Rm size U s) := rfl

def obs_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd Rd Rn size U Q) s
theorem obs_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd Rd Rn size U Q) s)) (Clauses.obs_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd real Rd Rn size U Q s) := rfl

def obs_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd Rd Rn size U) s
theorem obs_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd real Rd Rn size U s =
      Arch.project .clause s (stateOf ((decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd Rd Rn size U) s)) (Clauses.obs_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd real Rd Rn size U s) := rfl

def obs_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd Rd Rn size Q) s
theorem obs_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd real Rd Rn size Q s =
      Arch.project .clause s (stateOf ((decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd Rd Rn size Q) s)) (Clauses.obs_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd real Rd Rn size Q s) := rfl

def obs_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd Rd Rn size) s
theorem obs_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd real Rd Rn size s =
      Arch.project .clause s (stateOf ((decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd Rd Rn size) s)) (Clauses.obs_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd real Rd Rn size s) := rfl

def obs_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding Rd Rn Rm size U Q) s
theorem obs_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding Rd Rn Rm size U Q) s)) (Clauses.obs_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding real Rd Rn Rm size U Q s) := rfl

def obs_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd Rd Rn immb immh Q) s
theorem obs_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) (s : State) :
    obs_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd real Rd Rn immb immh Q s =
      Arch.project .clause s (stateOf ((decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd Rd Rn immb immh Q) s)) (Clauses.obs_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd real Rd Rn immb immh Q s) := rfl

def obs_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd Rd Rn immb immh) s
theorem obs_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (s : State) :
    obs_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd real Rd Rn immb immh s =
      Arch.project .clause s (stateOf ((decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd Rd Rn immb immh) s)) (Clauses.obs_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd real Rd Rn immb immh s) := rfl

def obs_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s
theorem obs_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s)) (Clauses.obs_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s) := rfl

def obs_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s
theorem obs_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s =
      Arch.project .clause s (stateOf ((decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s)) (Clauses.obs_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s) := rfl

def obs_srshr_advsimd_aarch64_instrs_vector_shift_right_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s
theorem obs_srshr_advsimd_aarch64_instrs_vector_shift_right_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_srshr_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s)) (Clauses.obs_srshr_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s) := rfl

def obs_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s
theorem obs_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s =
      Arch.project .clause s (stateOf ((decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s)) (Clauses.obs_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s) := rfl

def obs_srsra_advsimd_aarch64_instrs_vector_shift_right_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s
theorem obs_srsra_advsimd_aarch64_instrs_vector_shift_right_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_srsra_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s)) (Clauses.obs_srsra_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s) := rfl

def obs_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s
theorem obs_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s =
      Arch.project .clause s (stateOf ((decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s)) (Clauses.obs_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s) := rfl

def obs_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s
theorem obs_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s)) (Clauses.obs_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s) := rfl

def obs_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s
theorem obs_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s =
      Arch.project .clause s (stateOf ((decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s)) (Clauses.obs_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s) := rfl

def obs_sshll_advsimd_aarch64_instrs_vector_shift_left_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long Rd Rn immb immh U Q) s
theorem obs_sshll_advsimd_aarch64_instrs_vector_shift_left_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sshll_advsimd_aarch64_instrs_vector_shift_left_long real Rd Rn immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long Rd Rn immb immh U Q) s)) (Clauses.obs_sshll_advsimd_aarch64_instrs_vector_shift_left_long real Rd Rn immb immh U Q s) := rfl

def obs_sshr_advsimd_aarch64_instrs_vector_shift_right_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s
theorem obs_sshr_advsimd_aarch64_instrs_vector_shift_right_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sshr_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s)) (Clauses.obs_sshr_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s) := rfl

def obs_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s
theorem obs_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s =
      Arch.project .clause s (stateOf ((decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s)) (Clauses.obs_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s) := rfl

def obs_ssra_advsimd_aarch64_instrs_vector_shift_right_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s
theorem obs_ssra_advsimd_aarch64_instrs_vector_shift_right_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ssra_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s)) (Clauses.obs_ssra_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s) := rfl

def obs_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s
theorem obs_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s =
      Arch.project .clause s (stateOf ((decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s)) (Clauses.obs_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s) := rfl

def obs_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm size U Q) s
theorem obs_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm size U Q) s)) (Clauses.obs_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long real Rd Rn o1 Rm size U Q s) := rfl

def obs_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm size U Q) s
theorem obs_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm size U Q) s)) (Clauses.obs_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide real Rd Rn o1 Rm size U Q s) := rfl

def obs_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s
theorem obs_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s =
      Arch.project .clause s (stateOf ((decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s)) (Clauses.obs_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s) := rfl

def obs_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s
theorem obs_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s =
      Arch.project .clause s (stateOf ((decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s)) (Clauses.obs_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s) := rfl

def obs_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s
theorem obs_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s =
      Arch.project .clause s (stateOf ((decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s)) (Clauses.obs_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s) := rfl

def obs_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s
theorem obs_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s =
      Arch.project .clause s (stateOf ((decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s)) (Clauses.obs_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s) := rfl

def obs_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s
theorem obs_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s =
      Arch.project .clause s (stateOf ((decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s)) (Clauses.obs_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s) := rfl

def obs_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s
theorem obs_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s =
      Arch.project .clause s (stateOf ((decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s)) (Clauses.obs_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s) := rfl

def obs_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s
theorem obs_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s =
      Arch.project .clause s (stateOf ((decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb Rt Rn size opcode L Q) s)) (Clauses.obs_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb real Rt Rn size opcode L Q s) := rfl

def obs_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s
theorem obs_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s =
      Arch.project .clause s (stateOf ((decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc Rt Rn size opcode Rm L Q) s)) (Clauses.obs_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc real Rt Rn size opcode Rm L Q s) := rfl

def obs_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s
theorem obs_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s =
      Arch.project .clause s (stateOf ((decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb Rt Rn size S opcode o2 R L Q) s)) (Clauses.obs_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb real Rt Rn size S opcode o2 R L Q s) := rfl

def obs_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s
theorem obs_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s =
      Arch.project .clause s (stateOf ((decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc Rt Rn size S opcode Rm R L Q) s)) (Clauses.obs_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc real Rt Rn size S opcode Rm R L Q s) := rfl

def obs_st64b_aarch64_instrs_memory_atomicops_st_acc_st64b (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st64b_aarch64_instrs_memory_atomicops_st_acc_st64b Rt Rn) s
theorem obs_st64b_aarch64_instrs_memory_atomicops_st_acc_st64b_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (s : State) :
    obs_st64b_aarch64_instrs_memory_atomicops_st_acc_st64b real Rt Rn s =
      Arch.project .clause s (stateOf ((decode_st64b_aarch64_instrs_memory_atomicops_st_acc_st64b Rt Rn) s)) (Clauses.obs_st64b_aarch64_instrs_memory_atomicops_st_acc_st64b real Rt Rn s) := rfl

def obs_st64bv0_aarch64_instrs_memory_atomicops_st_acc_st64bv0 (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st64bv0_aarch64_instrs_memory_atomicops_st_acc_st64bv0 Rt Rn Rs) s
theorem obs_st64bv0_aarch64_instrs_memory_atomicops_st_acc_st64bv0_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (s : State) :
    obs_st64bv0_aarch64_instrs_memory_atomicops_st_acc_st64bv0 real Rt Rn Rs s =
      Arch.project .clause s (stateOf ((decode_st64bv0_aarch64_instrs_memory_atomicops_st_acc_st64bv0 Rt Rn Rs) s)) (Clauses.obs_st64bv0_aarch64_instrs_memory_atomicops_st_acc_st64bv0 real Rt Rn Rs s) := rfl

def obs_st64bv_aarch64_instrs_memory_atomicops_st_acc_st64bv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_st64bv_aarch64_instrs_memory_atomicops_st_acc_st64bv Rt Rn Rs) s
theorem obs_st64bv_aarch64_instrs_memory_atomicops_st_acc_st64bv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (s : State) :
    obs_st64bv_aarch64_instrs_memory_atomicops_st_acc_st64bv real Rt Rn Rs s =
      Arch.project .clause s (stateOf ((decode_st64bv_aarch64_instrs_memory_atomicops_st_acc_st64bv Rt Rn Rs) s)) (Clauses.obs_st64bv_aarch64_instrs_memory_atomicops_st_acc_st64bv real Rt Rn Rs s) := rfl

def obs_stllr_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stllr_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_stllr_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stllr_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stllr_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stllr_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stllrb_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stllrb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_stllrb_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stllrb_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stllrb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stllrb_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stllrh_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stllrh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_stllrh_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stllrh_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stllrh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stllrh_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stlr_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlr_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_stlr_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stlr_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stlr_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stlr_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stlr_aarch64_instrs_memory_ordered_writeback (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlr_aarch64_instrs_memory_ordered_writeback Rt Rn size) s
theorem obs_stlr_aarch64_instrs_memory_ordered_writeback_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (s : State) :
    obs_stlr_aarch64_instrs_memory_ordered_writeback real Rt Rn size s =
      Arch.project .clause s (stateOf ((decode_stlr_aarch64_instrs_memory_ordered_writeback Rt Rn size) s)) (Clauses.obs_stlr_aarch64_instrs_memory_ordered_writeback real Rt Rn size s) := rfl

def obs_stlrb_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlrb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_stlrb_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stlrb_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stlrb_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stlrb_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stlrh_aarch64_instrs_memory_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlrh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s
theorem obs_stlrh_aarch64_instrs_memory_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stlrh_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stlrh_aarch64_instrs_memory_ordered Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stlrh_aarch64_instrs_memory_ordered real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stlur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered Rt Rn imm9 opc size) s
theorem obs_stlur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_stlur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_stlur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered Rt Rn imm9 opc size) s)) (Clauses.obs_stlur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered real Rt Rn imm9 opc size s) := rfl

def obs_stlur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s
theorem obs_stlur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_stlur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_stlur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s)) (Clauses.obs_stlur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s) := rfl

def obs_stlurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s
theorem obs_stlurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_stlurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_stlurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s)) (Clauses.obs_stlurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s) := rfl

def obs_stlurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s
theorem obs_stlurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_stlurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_stlurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl Rt Rn imm9 opc size) s)) (Clauses.obs_stlurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl real Rt Rn imm9 opc size s) := rfl

def obs_stlxp_aarch64_instrs_memory_exclusive_pair (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz) s
theorem obs_stlxp_aarch64_instrs_memory_exclusive_pair_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) (s : State) :
    obs_stlxp_aarch64_instrs_memory_exclusive_pair real Rt Rn Rt2 o0 Rs L sz s =
      Arch.project .clause s (stateOf ((decode_stlxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz) s)) (Clauses.obs_stlxp_aarch64_instrs_memory_exclusive_pair real Rt Rn Rt2 o0 Rs L sz s) := rfl

def obs_stlxr_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_stlxr_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stlxr_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stlxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stlxr_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stlxrb_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_stlxrb_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stlxrb_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stlxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stlxrb_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stlxrh_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stlxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_stlxrh_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stlxrh_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stlxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stlxrh_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L opc) s
theorem obs_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc Rt Rn Rt2 imm7 L opc) s
theorem obs_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2 imm7 L opc) s
theorem obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_stp_gen_aarch64_instrs_memory_pair_general_offset (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L opc) s
theorem obs_stp_gen_aarch64_instrs_memory_pair_general_offset_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_stp_gen_aarch64_instrs_memory_pair_general_offset real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_stp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_stp_gen_aarch64_instrs_memory_pair_general_offset real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_stp_gen_aarch64_instrs_memory_pair_general_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_stp_gen_aarch64_instrs_memory_pair_general_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_stp_gen_aarch64_instrs_memory_pair_general_post_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_stp_gen_aarch64_instrs_memory_pair_general_post_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_stp_gen_aarch64_instrs_memory_pair_general_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L opc) s
theorem obs_stp_gen_aarch64_instrs_memory_pair_general_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) (s : State) :
    obs_stp_gen_aarch64_instrs_memory_pair_general_pre_idx real Rt Rn Rt2 imm7 L opc s =
      Arch.project .clause s (stateOf ((decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx Rt Rn Rt2 imm7 L opc) s)) (Clauses.obs_stp_gen_aarch64_instrs_memory_pair_general_pre_idx real Rt Rn Rt2 imm7 L opc s) := rfl

def obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register Rt Rn S option_name Rm opc size) s
theorem obs_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_str_reg_gen_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_str_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_str_reg_gen_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_str_reg_gen_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_str_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_str_reg_gen_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_strb_reg_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_strb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_strb_reg_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_strb_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_strb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_strb_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s
theorem obs_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 opc size) s)) (Clauses.obs_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx real Rt Rn imm9 opc size s) := rfl

def obs_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s
theorem obs_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 opc size) s)) (Clauses.obs_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx real Rt Rn imm9 opc size s) := rfl

def obs_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s
theorem obs_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s =
      Arch.project .clause s (stateOf ((decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 opc size) s)) (Clauses.obs_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned real Rt Rn imm12 opc size s) := rfl

def obs_strh_reg_aarch64_instrs_memory_single_general_register (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_strh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s
theorem obs_strh_reg_aarch64_instrs_memory_single_general_register_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_strh_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s =
      Arch.project .clause s (stateOf ((decode_strh_reg_aarch64_instrs_memory_single_general_register Rt Rn S option_name Rm opc size) s)) (Clauses.obs_strh_reg_aarch64_instrs_memory_single_general_register real Rt Rn S option_name Rm opc size s) := rfl

def obs_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s
theorem obs_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s)) (Clauses.obs_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s) := rfl

def obs_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s
theorem obs_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s)) (Clauses.obs_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s) := rfl

def obs_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s
theorem obs_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv Rt Rn imm9 opc size) s)) (Clauses.obs_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv real Rt Rn imm9 opc size s) := rfl

def obs_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s
theorem obs_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) (s : State) :
    obs_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s =
      Arch.project .clause s (stateOf ((decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 opc size) s)) (Clauses.obs_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal real Rt Rn imm9 opc size s) := rfl

def obs_stxp_aarch64_instrs_memory_exclusive_pair (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz) s
theorem obs_stxp_aarch64_instrs_memory_exclusive_pair_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) (s : State) :
    obs_stxp_aarch64_instrs_memory_exclusive_pair real Rt Rn Rt2 o0 Rs L sz s =
      Arch.project .clause s (stateOf ((decode_stxp_aarch64_instrs_memory_exclusive_pair Rt Rn Rt2 o0 Rs L sz) s)) (Clauses.obs_stxp_aarch64_instrs_memory_exclusive_pair real Rt Rn Rt2 o0 Rs L sz s) := rfl

def obs_stxr_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_stxr_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stxr_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stxr_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stxrb_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_stxrb_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stxrb_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stxrb_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_stxrh_aarch64_instrs_memory_exclusive_single (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_stxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s
theorem obs_stxrh_aarch64_instrs_memory_exclusive_single_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_stxrh_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s =
      Arch.project .clause s (stateOf ((decode_stxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 o0 Rs L size) s)) (Clauses.obs_stxrh_aarch64_instrs_memory_exclusive_single real Rt Rn Rt2 o0 Rs L size s) := rfl

def obs_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf) s
theorem obs_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg real Rd Rn imm3 option_name Rm S op sf s =
      Arch.project .clause s (stateOf ((decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf) s)) (Clauses.obs_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg real Rd Rn imm3 option_name Rm S op sf s) := rfl

def obs_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf) s
theorem obs_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate real Rd Rn imm12 sh S op sf s =
      Arch.project .clause s (stateOf ((decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf) s)) (Clauses.obs_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate real Rd Rn imm12 sh S op sf s) := rfl

def obs_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf) s
theorem obs_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg real Rd Rn imm6 Rm shift S op sf s =
      Arch.project .clause s (stateOf ((decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf) s)) (Clauses.obs_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg real Rd Rn imm6 Rm shift S op sf s) := rfl

def obs_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd Rd Rn Rm size U Q) s
theorem obs_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd Rd Rn Rm size U Q) s)) (Clauses.obs_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd real Rd Rn Rm size U Q s) := rfl

def obs_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd Rd Rn Rm size U) s
theorem obs_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd Rd Rn Rm size U) s)) (Clauses.obs_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd real Rd Rn Rm size U s) := rfl

def obs_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm size U Q) s
theorem obs_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow Rd Rn o1 Rm size U Q) s)) (Clauses.obs_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow real Rd Rn o1 Rm size U Q s) := rfl

def obs_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress (real : Type) [SailReal real] (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress Xd Xn Xm) s
theorem obs_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress_mapping (real : Type) [SailReal real] (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) (s : State) :
    obs_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress real Xd Xn Xm s =
      Arch.project .clause s (stateOf ((decode_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress Xd Xn Xm) s)) (Clauses.obs_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress real Xd Xn Xm s) := rfl

def obs_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags (real : Type) [SailReal real] (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags Xd Xn Xm) s
theorem obs_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags_mapping (real : Type) [SailReal real] (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) (s : State) :
    obs_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags real Xd Xn Xm s =
      Arch.project .clause s (stateOf ((decode_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags Xd Xn Xm) s)) (Clauses.obs_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags real Xd Xn Xm s) := rfl

def obs_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf) s
theorem obs_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg real Rd Rn imm3 option_name Rm S op sf s =
      Arch.project .clause s (stateOf ((decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf) s)) (Clauses.obs_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg real Rd Rn imm3 option_name Rm S op sf s) := rfl

def obs_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf) s
theorem obs_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate real Rd Rn imm12 sh S op sf s =
      Arch.project .clause s (stateOf ((decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf) s)) (Clauses.obs_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate real Rd Rn imm12 sh S op sf s) := rfl

def obs_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf) s
theorem obs_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) (s : State) :
    obs_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg real Rd Rn imm6 Rm shift S op sf s =
      Arch.project .clause s (stateOf ((decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf) s)) (Clauses.obs_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg real Rd Rn imm6 Rm shift S op sf s) := rfl

def obs_sudot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (US : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sudot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp Rd Rn H Rm M L US Q) s
theorem obs_sudot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (US : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_sudot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp real Rd Rn H Rm M L US Q s =
      Arch.project .clause s (stateOf ((decode_sudot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp Rd Rn H Rm M L US Q) s)) (Clauses.obs_sudot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp real Rd Rn H Rm M L US Q s) := rfl

def obs_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd Rd Rn size U Q) s
theorem obs_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd Rd Rn size U Q) s)) (Clauses.obs_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd real Rd Rn size U Q s) := rfl

def obs_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd Rd Rn size U) s
theorem obs_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd real Rd Rn size U s =
      Arch.project .clause s (stateOf ((decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd Rd Rn size U) s)) (Clauses.obs_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd real Rd Rn size U s) := rfl

def obs_svc_aarch64_instrs_system_exceptions_runtime_svc (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) : Arch.Observation :=
  Arch.observe (decode_svc_aarch64_instrs_system_exceptions_runtime_svc imm16) s
theorem obs_svc_aarch64_instrs_system_exceptions_runtime_svc_mapping (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) :
    obs_svc_aarch64_instrs_system_exceptions_runtime_svc real imm16 s =
      Arch.project .clause s (stateOf ((decode_svc_aarch64_instrs_system_exceptions_runtime_svc imm16) s)) (Clauses.obs_svc_aarch64_instrs_system_exceptions_runtime_svc real imm16 s) := rfl

def obs_swp_aarch64_instrs_memory_atomicops_swp (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_swp_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A size) s
theorem obs_swp_aarch64_instrs_memory_atomicops_swp_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_swp_aarch64_instrs_memory_atomicops_swp real Rt Rn Rs R A size s =
      Arch.project .clause s (stateOf ((decode_swp_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A size) s)) (Clauses.obs_swp_aarch64_instrs_memory_atomicops_swp real Rt Rn Rs R A size s) := rfl

def obs_swpb_aarch64_instrs_memory_atomicops_swp (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_swpb_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A size) s
theorem obs_swpb_aarch64_instrs_memory_atomicops_swp_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_swpb_aarch64_instrs_memory_atomicops_swp real Rt Rn Rs R A size s =
      Arch.project .clause s (stateOf ((decode_swpb_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A size) s)) (Clauses.obs_swpb_aarch64_instrs_memory_atomicops_swp real Rt Rn Rs R A size s) := rfl

def obs_swph_aarch64_instrs_memory_atomicops_swp (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) : Arch.Observation :=
  Arch.observe (decode_swph_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A size) s
theorem obs_swph_aarch64_instrs_memory_atomicops_swp_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) (s : State) :
    obs_swph_aarch64_instrs_memory_atomicops_swp real Rt Rn Rs R A size s =
      Arch.project .clause s (stateOf ((decode_swph_aarch64_instrs_memory_atomicops_swp Rt Rn Rs R A size) s)) (Clauses.obs_swph_aarch64_instrs_memory_atomicops_swp real Rt Rn Rs R A size s) := rfl

def obs_swpp_aarch64_instrs_memory_atomicops_swp_128 (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_swpp_aarch64_instrs_memory_atomicops_swp_128 Rt Rn opc o3 Rt2 R A S) s
theorem obs_swpp_aarch64_instrs_memory_atomicops_swp_128_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) (s : State) :
    obs_swpp_aarch64_instrs_memory_atomicops_swp_128 real Rt Rn opc o3 Rt2 R A S s =
      Arch.project .clause s (stateOf ((decode_swpp_aarch64_instrs_memory_atomicops_swp_128 Rt Rn opc o3 Rt2 R A S) s)) (Clauses.obs_swpp_aarch64_instrs_memory_atomicops_swp_128 real Rt Rn opc o3 Rt2 R A S s) := rfl

def obs_sys_aarch64_instrs_system_sysops (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sys_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L) s
theorem obs_sys_aarch64_instrs_system_sysops_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) (s : State) :
    obs_sys_aarch64_instrs_system_sysops real Rt op2 CRm CRn op1 L s =
      Arch.project .clause s (stateOf ((decode_sys_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L) s)) (Clauses.obs_sys_aarch64_instrs_system_sysops real Rt op2 CRm CRn op1 L s) := rfl

def obs_sysl_aarch64_instrs_system_sysops (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sysl_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L) s
theorem obs_sysl_aarch64_instrs_system_sysops_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) (s : State) :
    obs_sysl_aarch64_instrs_system_sysops real Rt op2 CRm CRn op1 L s =
      Arch.project .clause s (stateOf ((decode_sysl_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L) s)) (Clauses.obs_sysl_aarch64_instrs_system_sysops real Rt op2 CRm CRn op1 L s) := rfl

def obs_sysp_aarch64_instrs_system_sysops_128 (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_sysp_aarch64_instrs_system_sysops_128 Rt op2 CRm CRn op1 L) s
theorem obs_sysp_aarch64_instrs_system_sysops_128_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) (s : State) :
    obs_sysp_aarch64_instrs_system_sysops_128 real Rt op2 CRm CRn op1 L s =
      Arch.project .clause s (stateOf ((decode_sysp_aarch64_instrs_system_sysops_128 Rt op2 CRm CRn op1 L) s)) (Clauses.obs_sysp_aarch64_instrs_system_sysops_128 real Rt op2 CRm CRn op1 L s) := rfl

def obs_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (len : (BitVec 2)) (Rm : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table Rd Rn op len Rm Q) s
theorem obs_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (len : (BitVec 2)) (Rm : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table real Rd Rn op len Rm Q s =
      Arch.project .clause s (stateOf ((decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table Rd Rn op len Rm Q) s)) (Clauses.obs_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table real Rd Rn op len Rm Q s) := rfl

def obs_tbnz_aarch64_instrs_branch_conditional_test (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5) s
theorem obs_tbnz_aarch64_instrs_branch_conditional_test_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) (s : State) :
    obs_tbnz_aarch64_instrs_branch_conditional_test real Rt imm14 b40 op b5 s =
      Arch.project .clause s (stateOf ((decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5) s)) (Clauses.obs_tbnz_aarch64_instrs_branch_conditional_test real Rt imm14 b40 op b5 s) := rfl

def obs_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (len : (BitVec 2)) (Rm : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table Rd Rn op len Rm Q) s
theorem obs_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (len : (BitVec 2)) (Rm : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table real Rd Rn op len Rm Q s =
      Arch.project .clause s (stateOf ((decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table Rd Rn op len Rm Q) s)) (Clauses.obs_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table real Rd Rn op len Rm Q s) := rfl

def obs_tbz_aarch64_instrs_branch_conditional_test (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_tbz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5) s
theorem obs_tbz_aarch64_instrs_branch_conditional_test_mapping (real : Type) [SailReal real] (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) (s : State) :
    obs_tbz_aarch64_instrs_branch_conditional_test real Rt imm14 b40 op b5 s =
      Arch.project .clause s (stateOf ((decode_tbz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5) s)) (Clauses.obs_tbz_aarch64_instrs_branch_conditional_test real Rt imm14 b40 op b5 s) := rfl

def obs_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose Rd Rn op Rm size Q) s
theorem obs_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose real Rd Rn op Rm size Q s =
      Arch.project .clause s (stateOf ((decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose Rd Rn op Rm size Q) s)) (Clauses.obs_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose real Rd Rn op Rm size Q s) := rfl

def obs_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose Rd Rn op Rm size Q) s
theorem obs_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose real Rd Rn op Rm size Q s =
      Arch.project .clause s (stateOf ((decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose Rd Rn op Rm size Q) s)) (Clauses.obs_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose real Rd Rn op Rm size Q s) := rfl

def obs_tsb_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_tsb_aarch64_instrs_system_hints op2 CRm) s
theorem obs_tsb_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_tsb_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_tsb_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_tsb_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm size U Q) s
theorem obs_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff real Rd Rn ac Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm size U Q) s)) (Clauses.obs_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff real Rd Rn ac Rm size U Q s) := rfl

def obs_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm size U Q) s
theorem obs_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff real Rd Rn op Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm size U Q) s)) (Clauses.obs_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff real Rd Rn op Rm size U Q s) := rfl

def obs_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm size U Q) s
theorem obs_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff real Rd Rn ac Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff Rd Rn ac Rm size U Q) s)) (Clauses.obs_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff real Rd Rn ac Rm size U Q s) := rfl

def obs_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm size U Q) s
theorem obs_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff real Rd Rn op Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff Rd Rn op Rm size U Q) s)) (Clauses.obs_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff real Rd Rn op Rm size U Q s) := rfl

def obs_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op size U Q) s
theorem obs_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op size U Q) s)) (Clauses.obs_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise real Rd Rn op size U Q s) := rfl

def obs_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm size U Q) s
theorem obs_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm size U Q) s)) (Clauses.obs_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long real Rd Rn o1 Rm size U Q s) := rfl

def obs_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op size U Q) s
theorem obs_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise Rd Rn op size U Q) s)) (Clauses.obs_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise real Rd Rn op size U Q s) := rfl

def obs_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long Rd Rn size U Q) s
theorem obs_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long Rd Rn size U Q) s)) (Clauses.obs_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long real Rd Rn size U Q s) := rfl

def obs_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm size U Q) s
theorem obs_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm size U Q) s)) (Clauses.obs_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide real Rd Rn o1 Rm size U Q s) := rfl

def obs_ubfm_aarch64_instrs_integer_bitfield (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc sf) s
theorem obs_ubfm_aarch64_instrs_integer_bitfield_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_ubfm_aarch64_instrs_integer_bitfield real Rd Rn imms immr N opc sf s =
      Arch.project .clause s (stateOf ((decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc sf) s)) (Clauses.obs_ubfm_aarch64_instrs_integer_bitfield real Rd Rn imms immr N opc sf s) := rfl

def obs_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd Rd Rn immb immh U Q) s
theorem obs_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd real Rd Rn immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd Rd Rn immb immh U Q) s)) (Clauses.obs_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd real Rd Rn immb immh U Q s) := rfl

def obs_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd Rd Rn immb immh U) s
theorem obs_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd real Rd Rn immb immh U s =
      Arch.project .clause s (stateOf ((decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd Rd Rn immb immh U) s)) (Clauses.obs_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd real Rd Rn immb immh U s) := rfl

def obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd Rd Rn sz U Q) s
theorem obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd real Rd Rn sz U Q s =
      Arch.project .clause s (stateOf ((decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd Rd Rn sz U Q) s)) (Clauses.obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd real Rd Rn sz U Q s) := rfl

def obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd Rd Rn sz U) s
theorem obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (s : State) :
    obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd real Rd Rn sz U s =
      Arch.project .clause s (stateOf ((decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd Rd Rn sz U) s)) (Clauses.obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd real Rd Rn sz U s) := rfl

def obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd Rd Rn U Q) s
theorem obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd real Rd Rn U Q s =
      Arch.project .clause s (stateOf ((decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd Rd Rn U Q) s)) (Clauses.obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd real Rd Rn U Q s) := rfl

def obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd Rd Rn U) s
theorem obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd real Rd Rn U s =
      Arch.project .clause s (stateOf ((decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd Rd Rn U) s)) (Clauses.obs_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd real Rd Rn U s) := rfl

def obs_ucvtf_float_fix_aarch64_instrs_float_convert_fix (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode ftype sf) s
theorem obs_ucvtf_float_fix_aarch64_instrs_float_convert_fix_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_ucvtf_float_fix_aarch64_instrs_float_convert_fix real Rd Rn scale opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix Rd Rn scale opcode rmode ftype sf) s)) (Clauses.obs_ucvtf_float_fix_aarch64_instrs_float_convert_fix real Rd Rn scale opcode rmode ftype sf s) := rfl

def obs_ucvtf_float_int_aarch64_instrs_float_convert_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ucvtf_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s
theorem obs_ucvtf_float_int_aarch64_instrs_float_convert_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) (s : State) :
    obs_ucvtf_float_int_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s =
      Arch.project .clause s (stateOf ((decode_ucvtf_float_int_aarch64_instrs_float_convert_int Rd Rn opcode rmode ftype sf) s)) (Clauses.obs_ucvtf_float_int_aarch64_instrs_float_convert_int real Rd Rn opcode rmode ftype sf s) := rfl

def obs_udf_perm_undef_aarch64_instrs_udf (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) : Arch.Observation :=
  Arch.observe (decode_udf_perm_undef_aarch64_instrs_udf imm16) s
theorem obs_udf_perm_undef_aarch64_instrs_udf_mapping (real : Type) [SailReal real] (imm16 : (BitVec 16)) (s : State) :
    obs_udf_perm_undef_aarch64_instrs_udf real imm16 s =
      Arch.project .clause s (stateOf ((decode_udf_perm_undef_aarch64_instrs_udf imm16) s)) (Clauses.obs_udf_perm_undef_aarch64_instrs_udf real imm16 s) := rfl

def obs_udiv_aarch64_instrs_integer_arithmetic_div (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_udiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm sf) s
theorem obs_udiv_aarch64_instrs_integer_arithmetic_div_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_udiv_aarch64_instrs_integer_arithmetic_div real Rd Rn o1 Rm sf s =
      Arch.project .clause s (stateOf ((decode_udiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm sf) s)) (Clauses.obs_udiv_aarch64_instrs_integer_arithmetic_div real Rd Rn o1 Rm sf s) := rfl

def obs_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp Rd Rn H Rm M L size U Q) s
theorem obs_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp real Rd Rn H Rm M L size U Q s =
      Arch.project .clause s (stateOf ((decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp Rd Rn H Rm M L size U Q) s)) (Clauses.obs_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp real Rd Rn H Rm M L size U Q s) := rfl

def obs_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp Rd Rn Rm size U Q) s
theorem obs_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp Rd Rn Rm size U Q) s)) (Clauses.obs_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp real Rd Rn Rm size U Q s) := rfl

def obs_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating Rd Rn Rm size U Q) s
theorem obs_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating Rd Rn Rm size U Q) s)) (Clauses.obs_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating real Rd Rn Rm size U Q s) := rfl

def obs_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int Rd Rn Rm size U Q) s
theorem obs_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int Rd Rn Rm size U Q) s)) (Clauses.obs_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int real Rd Rn Rm size U Q s) := rfl

def obs_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s
theorem obs_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 real Rd Rn Ra o0 Rm U s =
      Arch.project .clause s (stateOf ((decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s)) (Clauses.obs_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 real Rd Rn Ra o0 Rm U s) := rfl

def obs_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm size U Q) s
theorem obs_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm size U Q) s)) (Clauses.obs_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single real Rd Rn o1 Rm size U Q s) := rfl

def obs_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg Rd Rn Rm sf) s
theorem obs_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg real Rd Rn Rm sf s =
      Arch.project .clause s (stateOf ((decode_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg Rd Rn Rm sf) s)) (Clauses.obs_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg real Rd Rn Rm sf s) := rfl

def obs_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm size U Q) s
theorem obs_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm size U Q) s)) (Clauses.obs_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair real Rd Rn o1 Rm size U Q s) := rfl

def obs_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q) s
theorem obs_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q) s)) (Clauses.obs_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max real Rd Rn op size U Q s) := rfl

def obs_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm size U Q) s
theorem obs_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single Rd Rn o1 Rm size U Q) s)) (Clauses.obs_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single real Rd Rn o1 Rm size U Q s) := rfl

def obs_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg Rd Rn Rm sf) s
theorem obs_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (s : State) :
    obs_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg real Rd Rn Rm sf s =
      Arch.project .clause s (stateOf ((decode_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg Rd Rn Rm sf) s)) (Clauses.obs_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg real Rd Rn Rm sf s) := rfl

def obs_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm size U Q) s
theorem obs_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair Rd Rn o1 Rm size U Q) s)) (Clauses.obs_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair real Rd Rn o1 Rm size U Q s) := rfl

def obs_uminv_advsimd_aarch64_instrs_vector_reduce_int_max (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q) s
theorem obs_uminv_advsimd_aarch64_instrs_vector_reduce_int_max_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uminv_advsimd_aarch64_instrs_vector_reduce_int_max real Rd Rn op size U Q s =
      Arch.project .clause s (stateOf ((decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max Rd Rn op size U Q) s)) (Clauses.obs_uminv_advsimd_aarch64_instrs_vector_reduce_int_max real Rd Rn op size U Q s) := rfl

def obs_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn H o2 Rm M L size U Q) s
theorem obs_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long real Rd Rn H o2 Rm M L size U Q s =
      Arch.project .clause s (stateOf ((decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn H o2 Rm M L size U Q) s)) (Clauses.obs_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long real Rd Rn H o2 Rm M L size U Q s) := rfl

def obs_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm size U Q) s
theorem obs_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm size U Q) s)) (Clauses.obs_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum real Rd Rn o1 Rm size U Q s) := rfl

def obs_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn H o2 Rm M L size U Q) s
theorem obs_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long real Rd Rn H o2 Rm M L size U Q s =
      Arch.project .clause s (stateOf ((decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long Rd Rn H o2 Rm M L size U Q) s)) (Clauses.obs_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long real Rd Rn H o2 Rm M L size U Q s) := rfl

def obs_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm size U Q) s
theorem obs_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum Rd Rn o1 Rm size U Q) s)) (Clauses.obs_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum real Rd Rn o1 Rm size U Q s) := rfl

def obs_ummla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ummla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla Rd Rn B Rm U) s
theorem obs_ummla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_ummla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla real Rd Rn B Rm U s =
      Arch.project .clause s (stateOf ((decode_ummla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla Rd Rn B Rm U) s)) (Clauses.obs_ummla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla real Rd Rn B Rm U s) := rfl

def obs_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned Rd Rn imm5 Q) s
theorem obs_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned real Rd Rn imm5 Q s =
      Arch.project .clause s (stateOf ((decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned Rd Rn imm5 Q) s)) (Clauses.obs_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned real Rd Rn imm5 Q s) := rfl

def obs_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s
theorem obs_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 real Rd Rn Ra o0 Rm U s =
      Arch.project .clause s (stateOf ((decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U) s)) (Clauses.obs_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 real Rd Rn Ra o0 Rm U s) := rfl

def obs_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U) s
theorem obs_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi real Rd Rn Ra Rm U s =
      Arch.project .clause s (stateOf ((decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U) s)) (Clauses.obs_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi real Rd Rn Ra Rm U s) := rfl

def obs_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long Rd Rn H Rm M L size U Q) s
theorem obs_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long real Rd Rn H Rm M L size U Q s =
      Arch.project .clause s (stateOf ((decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long Rd Rn H Rm M L size U Q) s)) (Clauses.obs_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long real Rd Rn H Rm M L size U Q s) := rfl

def obs_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product Rd Rn Rm size U Q) s
theorem obs_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product Rd Rn Rm size U Q) s)) (Clauses.obs_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product real Rd Rn Rm size U Q s) := rfl

def obs_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd Rd Rn Rm size U Q) s
theorem obs_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd Rd Rn Rm size U Q) s)) (Clauses.obs_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd real Rd Rn Rm size U Q s) := rfl

def obs_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd Rd Rn Rm size U) s
theorem obs_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd Rd Rn Rm size U) s)) (Clauses.obs_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd real Rd Rn Rm size U s) := rfl

def obs_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s
theorem obs_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s)) (Clauses.obs_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s) := rfl

def obs_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s
theorem obs_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s =
      Arch.project .clause s (stateOf ((decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s)) (Clauses.obs_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s) := rfl

def obs_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb immh U Q) s
theorem obs_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd real Rd Rn op immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb immh U Q) s)) (Clauses.obs_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd real Rd Rn op immb immh U Q s) := rfl

def obs_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb immh U) s
theorem obs_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd real Rd Rn op immb immh U s =
      Arch.project .clause s (stateOf ((decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb immh U) s)) (Clauses.obs_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd real Rd Rn op immb immh U s) := rfl

def obs_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb immh U Q) s
theorem obs_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd real Rd Rn op immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd Rd Rn op immb immh U Q) s)) (Clauses.obs_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd real Rd Rn op immb immh U Q s) := rfl

def obs_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb immh U) s
theorem obs_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd real Rd Rn op immb immh U s =
      Arch.project .clause s (stateOf ((decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd Rd Rn op immb immh U) s)) (Clauses.obs_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd real Rd Rn op immb immh U s) := rfl

def obs_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s
theorem obs_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s)) (Clauses.obs_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s) := rfl

def obs_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s
theorem obs_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s =
      Arch.project .clause s (stateOf ((decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s)) (Clauses.obs_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s) := rfl

def obs_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb immh U Q) s
theorem obs_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd real Rd Rn op immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd Rd Rn op immb immh U Q) s)) (Clauses.obs_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd real Rd Rn op immb immh U Q s) := rfl

def obs_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb immh U) s
theorem obs_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd real Rd Rn op immb immh U s =
      Arch.project .clause s (stateOf ((decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd Rd Rn op immb immh U) s)) (Clauses.obs_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd real Rd Rn op immb immh U s) := rfl

def obs_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd Rd Rn Rm size U Q) s
theorem obs_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd Rd Rn Rm size U Q) s)) (Clauses.obs_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd real Rd Rn Rm size U Q s) := rfl

def obs_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd Rd Rn Rm size U) s
theorem obs_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd real Rd Rn Rm size U s =
      Arch.project .clause s (stateOf ((decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd Rd Rn Rm size U) s)) (Clauses.obs_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd real Rd Rn Rm size U s) := rfl

def obs_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd Rd Rn size U Q) s
theorem obs_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd Rd Rn size U Q) s)) (Clauses.obs_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd real Rd Rn size U Q s) := rfl

def obs_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd Rd Rn size U) s
theorem obs_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd real Rd Rn size U s =
      Arch.project .clause s (stateOf ((decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd Rd Rn size U) s)) (Clauses.obs_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd real Rd Rn size U s) := rfl

def obs_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int Rd Rn sz Q) s
theorem obs_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int real Rd Rn sz Q s =
      Arch.project .clause s (stateOf ((decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int Rd Rn sz Q) s)) (Clauses.obs_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int real Rd Rn sz Q s) := rfl

def obs_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding Rd Rn Rm size U Q) s
theorem obs_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding real Rd Rn Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding Rd Rn Rm size U Q) s)) (Clauses.obs_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding real Rd Rn Rm size U Q s) := rfl

def obs_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s
theorem obs_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s)) (Clauses.obs_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s) := rfl

def obs_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s
theorem obs_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s =
      Arch.project .clause s (stateOf ((decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s)) (Clauses.obs_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s) := rfl

def obs_urshr_advsimd_aarch64_instrs_vector_shift_right_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s
theorem obs_urshr_advsimd_aarch64_instrs_vector_shift_right_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_urshr_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s)) (Clauses.obs_urshr_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s) := rfl

def obs_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s
theorem obs_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s =
      Arch.project .clause s (stateOf ((decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s)) (Clauses.obs_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s) := rfl

def obs_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int Rd Rn sz Q) s
theorem obs_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int real Rd Rn sz Q s =
      Arch.project .clause s (stateOf ((decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int Rd Rn sz Q) s)) (Clauses.obs_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int real Rd Rn sz Q s) := rfl

def obs_ursra_advsimd_aarch64_instrs_vector_shift_right_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s
theorem obs_ursra_advsimd_aarch64_instrs_vector_shift_right_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ursra_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s)) (Clauses.obs_ursra_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s) := rfl

def obs_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s
theorem obs_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s =
      Arch.project .clause s (stateOf ((decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s)) (Clauses.obs_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s) := rfl

def obs_usdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (US : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_usdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp Rd Rn H Rm M L US Q) s
theorem obs_usdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (US : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_usdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp real Rd Rn H Rm M L US Q s =
      Arch.project .clause s (stateOf ((decode_usdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp Rd Rn H Rm M L US Q) s)) (Clauses.obs_usdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp real Rd Rn H Rm M L US Q s) := rfl

def obs_usdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_usdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot Rd Rn Rm Q) s
theorem obs_usdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) (s : State) :
    obs_usdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot real Rd Rn Rm Q s =
      Arch.project .clause s (stateOf ((decode_usdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot Rd Rn Rm Q) s)) (Clauses.obs_usdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot real Rd Rn Rm Q s) := rfl

def obs_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s
theorem obs_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd Rd Rn S R Rm size U Q) s)) (Clauses.obs_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd real Rd Rn S R Rm size U Q s) := rfl

def obs_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s
theorem obs_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s =
      Arch.project .clause s (stateOf ((decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd Rd Rn S R Rm size U) s)) (Clauses.obs_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd real Rd Rn S R Rm size U s) := rfl

def obs_ushll_advsimd_aarch64_instrs_vector_shift_left_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long Rd Rn immb immh U Q) s
theorem obs_ushll_advsimd_aarch64_instrs_vector_shift_left_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ushll_advsimd_aarch64_instrs_vector_shift_left_long real Rd Rn immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long Rd Rn immb immh U Q) s)) (Clauses.obs_ushll_advsimd_aarch64_instrs_vector_shift_left_long real Rd Rn immb immh U Q s) := rfl

def obs_ushr_advsimd_aarch64_instrs_vector_shift_right_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s
theorem obs_ushr_advsimd_aarch64_instrs_vector_shift_right_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_ushr_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s)) (Clauses.obs_ushr_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s) := rfl

def obs_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s
theorem obs_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s =
      Arch.project .clause s (stateOf ((decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s)) (Clauses.obs_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s) := rfl

def obs_usmmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_usmmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla Rd Rn B Rm U) s
theorem obs_usmmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) (s : State) :
    obs_usmmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla real Rd Rn B Rm U s =
      Arch.project .clause s (stateOf ((decode_usmmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla Rd Rn B Rm U) s)) (Clauses.obs_usmmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla real Rd Rn B Rm U s) := rfl

def obs_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd Rd Rn size U Q) s
theorem obs_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd real Rd Rn size U Q s =
      Arch.project .clause s (stateOf ((decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd Rd Rn size U Q) s)) (Clauses.obs_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd real Rd Rn size U Q s) := rfl

def obs_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd Rd Rn size U) s
theorem obs_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (s : State) :
    obs_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd real Rd Rn size U s =
      Arch.project .clause s (stateOf ((decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd Rd Rn size U) s)) (Clauses.obs_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd real Rd Rn size U s) := rfl

def obs_usra_advsimd_aarch64_instrs_vector_shift_right_simd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s
theorem obs_usra_advsimd_aarch64_instrs_vector_shift_right_simd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_usra_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s =
      Arch.project .clause s (stateOf ((decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd Rd Rn o0 o1 immb immh U Q) s)) (Clauses.obs_usra_advsimd_aarch64_instrs_vector_shift_right_simd real Rd Rn o0 o1 immb immh U Q s) := rfl

def obs_usra_advsimd_aarch64_instrs_vector_shift_right_sisd (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s
theorem obs_usra_advsimd_aarch64_instrs_vector_shift_right_sisd_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (s : State) :
    obs_usra_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s =
      Arch.project .clause s (stateOf ((decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd Rd Rn o0 o1 immb immh U) s)) (Clauses.obs_usra_advsimd_aarch64_instrs_vector_shift_right_sisd real Rd Rn o0 o1 immb immh U s) := rfl

def obs_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm size U Q) s
theorem obs_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long Rd Rn o1 Rm size U Q) s)) (Clauses.obs_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long real Rd Rn o1 Rm size U Q s) := rfl

def obs_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm size U Q) s
theorem obs_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) (s : State) :
    obs_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide real Rd Rn o1 Rm size U Q s =
      Arch.project .clause s (stateOf ((decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide Rd Rn o1 Rm size U Q) s)) (Clauses.obs_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide real Rd Rn o1 Rm size U Q s) := rfl

def obs_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip Rd Rn op Rm size Q) s
theorem obs_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip real Rd Rn op Rm size Q s =
      Arch.project .clause s (stateOf ((decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip Rd Rn op Rm size Q) s)) (Clauses.obs_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip real Rd Rn op Rm size Q s) := rfl

def obs_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip Rd Rn op Rm size Q) s
theorem obs_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip real Rd Rn op Rm size Q s =
      Arch.project .clause s (stateOf ((decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip Rd Rn op Rm size Q) s)) (Clauses.obs_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip real Rd Rn op Rm size Q s) := rfl

def obs_wfe_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_wfe_aarch64_instrs_system_hints op2 CRm) s
theorem obs_wfe_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_wfe_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_wfe_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_wfe_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_wfet_aarch64_instrs_system_sysinstwithreg_wfet (real : Type) [SailReal real] (Rd : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_wfet_aarch64_instrs_system_sysinstwithreg_wfet Rd) s
theorem obs_wfet_aarch64_instrs_system_sysinstwithreg_wfet_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (s : State) :
    obs_wfet_aarch64_instrs_system_sysinstwithreg_wfet real Rd s =
      Arch.project .clause s (stateOf ((decode_wfet_aarch64_instrs_system_sysinstwithreg_wfet Rd) s)) (Clauses.obs_wfet_aarch64_instrs_system_sysinstwithreg_wfet real Rd s) := rfl

def obs_wfi_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_wfi_aarch64_instrs_system_hints op2 CRm) s
theorem obs_wfi_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_wfi_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_wfi_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_wfi_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_wfit_aarch64_instrs_system_sysinstwithreg_wfit (real : Type) [SailReal real] (Rd : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_wfit_aarch64_instrs_system_sysinstwithreg_wfit Rd) s
theorem obs_wfit_aarch64_instrs_system_sysinstwithreg_wfit_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (s : State) :
    obs_wfit_aarch64_instrs_system_sysinstwithreg_wfit real Rd s =
      Arch.project .clause s (stateOf ((decode_wfit_aarch64_instrs_system_sysinstwithreg_wfit Rd) s)) (Clauses.obs_wfit_aarch64_instrs_system_sysinstwithreg_wfit real Rd s) := rfl

def obs_xaflag_aarch64_instrs_integer_flags_xaflag (real : Type) [SailReal real] (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_xaflag_aarch64_instrs_integer_flags_xaflag CRm) s
theorem obs_xaflag_aarch64_instrs_integer_flags_xaflag_mapping (real : Type) [SailReal real] (CRm : (BitVec 4)) (s : State) :
    obs_xaflag_aarch64_instrs_integer_flags_xaflag real CRm s =
      Arch.project .clause s (stateOf ((decode_xaflag_aarch64_instrs_integer_flags_xaflag CRm) s)) (Clauses.obs_xaflag_aarch64_instrs_integer_flags_xaflag real CRm s) := rfl

def obs_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (s : State) : Arch.Observation :=
  Arch.observe (decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar Rd Rn imm6 Rm) s
theorem obs_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (s : State) :
    obs_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar real Rd Rn imm6 Rm s =
      Arch.project .clause s (stateOf ((decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar Rd Rn imm6 Rm) s)) (Clauses.obs_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar real Rd Rn imm6 Rm s) := rfl

def obs_xpac_aarch64_instrs_integer_pac_strip_dp_1src (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_xpac_aarch64_instrs_integer_pac_strip_dp_1src Rd Rn D) s
theorem obs_xpac_aarch64_instrs_integer_pac_strip_dp_1src_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) (s : State) :
    obs_xpac_aarch64_instrs_integer_pac_strip_dp_1src real Rd Rn D s =
      Arch.project .clause s (stateOf ((decode_xpac_aarch64_instrs_integer_pac_strip_dp_1src Rd Rn D) s)) (Clauses.obs_xpac_aarch64_instrs_integer_pac_strip_dp_1src real Rd Rn D s) := rfl

def obs_xpac_aarch64_instrs_integer_pac_strip_hint (real : Type) [SailReal real] (obs_unit : Unit) (s : State) : Arch.Observation :=
  Arch.observe (decode_xpac_aarch64_instrs_integer_pac_strip_hint obs_unit) s
theorem obs_xpac_aarch64_instrs_integer_pac_strip_hint_mapping (real : Type) [SailReal real] (obs_unit : Unit) (s : State) :
    obs_xpac_aarch64_instrs_integer_pac_strip_hint real obs_unit s =
      Arch.project .clause s (stateOf ((decode_xpac_aarch64_instrs_integer_pac_strip_hint obs_unit) s)) (Clauses.obs_xpac_aarch64_instrs_integer_pac_strip_hint real obs_unit s) := rfl

def obs_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat Rd Rn size Q) s
theorem obs_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat real Rd Rn size Q s =
      Arch.project .clause s (stateOf ((decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat Rd Rn size Q) s)) (Clauses.obs_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat real Rd Rn size Q s) := rfl

def obs_yield_aarch64_instrs_system_hints (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) : Arch.Observation :=
  Arch.observe (decode_yield_aarch64_instrs_system_hints op2 CRm) s
theorem obs_yield_aarch64_instrs_system_hints_mapping (real : Type) [SailReal real] (op2 : (BitVec 3)) (CRm : (BitVec 4)) (s : State) :
    obs_yield_aarch64_instrs_system_hints real op2 CRm s =
      Arch.project .clause s (stateOf ((decode_yield_aarch64_instrs_system_hints op2 CRm) s)) (Clauses.obs_yield_aarch64_instrs_system_hints real op2 CRm s) := rfl

def obs_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm size Q) s
theorem obs_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip real Rd Rn op Rm size Q s =
      Arch.project .clause s (stateOf ((decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm size Q) s)) (Clauses.obs_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip real Rd Rn op Rm size Q s) := rfl

def obs_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) : Arch.Observation :=
  Arch.observe (decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm size Q) s
theorem obs_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip_mapping (real : Type) [SailReal real] (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) (s : State) :
    obs_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip real Rd Rn op Rm size Q s =
      Arch.project .clause s (stateOf ((decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm size Q) s)) (Clauses.obs_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip real Rd Rn op Rm size Q s) := rfl

end ObsGen.ArchClauses
