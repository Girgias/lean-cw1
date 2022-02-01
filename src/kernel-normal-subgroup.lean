import tactic
import group_theory.subgroup.basic
import data.set.basic

namespace my_kernel_norm_sub

variables {G H : Type} [group G] [group H]
variable {I : subgroup H}
variable {φ : G →* H}

lemma map_mul_2 {x y : G} : φ(x * y * x⁻¹) = φ(x) * φ(y) * φ(x)⁻¹ :=
begin
    -- rewrite twice to get an obvious identiy
  rw map_mul,
  rw map_mul,
end

lemma x_in_kernel_is_identity {k : G}(hk : k ∈ φ.ker) : φ(k) = 1 :=
begin
  exact hk,
end

lemma conjugating_k_in_kernel_by_x_is_identity
  {k x : G}(hk : k ∈ φ.ker) : φ(x * k * x⁻¹) = 1 :=
begin
  -- rewrite our hypothethis to expand to multiplication by function
  rw map_mul_2,
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
  {k : G}(hk : k ∈ φ.ker){x : G} : x * k * x⁻¹ ∈ φ.ker :=
begin
    apply conjugating_k_in_kernel_by_x_is_identity,
    exact hk,
end

theorem kernel_is_normal_subgroup_of_domain (φ : G →* H) : subgroup.normal (φ.ker) :=
begin
  -- Change the goal to be the hypothethis of what a normal group is
  apply subgroup.normal.mk,
  apply conjugating_kernel_by_x_is_in_kernel,
end

-- Proof wiki: https://proofwiki.org/wiki/Preimage_of_Normal_Subgroup_of_Quotient_Group_under_Quotient_Epimorphism_is_Normal

#check subgroup.normal.mk
#check I.comap φ

lemma foo (φ : G →* H) {x y : subgroup.comap φ I} :
  φ(x*y*x⁻¹) =  φ(x) * φ(y) * φ(x)⁻¹ :=
begin
  exact map_mul_2,
end

lemma preimage_exist (φ : G →* H) {g : G}{h : H} {hg: subgroup.comap φ I} :
  φ(g) = h :=
begin
  
end

lemma bar (φ : G →* H) {i j : H} {x y : subgroup.comap φ I} :
  φ(x*y*x⁻¹) =  φ(x) * φ(y) * φ(x)⁻¹ :=
begin
  exact map_mul_2,
end

theorem preimage_of_normal_subgroup_is_normal
  (φ : G →* H) (hn : subgroup.normal(I)) : subgroup.normal (subgroup.comap φ I) :=
begin
  -- Change the goal to be the hypothethis of what a normal group is
  apply subgroup.normal.mk,
  intro hg,
  intro hpreim,
  rw foo,
  sorry,
end

-- example (h ; S.normal ) : (S.comap f).normal

end my_kernel_norm_sub
