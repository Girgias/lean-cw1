import tactic
import group_theory.subgroup.basic

namespace my_kernel_norm_sub

variables {G J : Type} [group G] [group J]
variable {H : subgroup G}
variable {I : subgroup J}
variable {φ : H →* I}

lemma x_in_kernel_is_identity {k : H}(hk : k ∈ φ.ker) : φ(k) = 1 :=
begin
  exact hk,
end

lemma conjugating_k_in_kernel_by_x_is_identity
  {k : H}(hk : k ∈ φ.ker){x : H} : φ(x * k * x⁻¹) = 1 :=
begin
  -- multiplication 
  have hhom : φ(x * k * x⁻¹) = φ(x) * φ(k) * φ(x⁻¹), {
    -- rewrite twice to get an obvious identiy
    rw map_mul,
    rw map_mul,
  },
  -- rewrite our hypothethis to expand to multiplication by function
  rw hhom,
  -- kernel element goes to the identity
  rw x_in_kernel_is_identity hk,
  -- Remove the multiplication by 1
  rw mul_one,
  -- bring back the multiplication by maps to multiplication within a map
  rw ← map_mul,
  -- cancel x * x⁻¹
  rw mul_right_inv,
  -- identity maps to identity
  rw map_one,
end

lemma conjugating_kernel_by_x_is_in_kernel
  {k : H}(hk : k ∈ φ.ker){x : H} : x * k * x⁻¹ ∈ φ.ker :=
begin
    apply conjugating_k_in_kernel_by_x_is_identity,
    exact hk,
end

theorem kernel_is_normal_subgroup_of_domain (φ : H →* I) : subgroup.normal (φ.ker) :=
begin
  -- TODO Look up what refine does
  refine {conj_mem := _},
  apply conjugating_kernel_by_x_is_in_kernel,
end

-- Proof wiki: https://proofwiki.org/wiki/Preimage_of_Normal_Subgroup_of_Quotient_Group_under_Quotient_Epimorphism_is_Normal

end my_kernel_norm_sub