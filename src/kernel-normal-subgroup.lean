import tactic
import group_theory.subgroup.basic
import algebra.group.hom

namespace my_kernel_norm_sub

/-- Lean should really have subgroups as types...
-- Taken from https://tqft.net/web/notes/load.php?name=students/20180219-MitchRowett-ASC-report-on-Lean
variables {G I : Type} [group G] [group I]
class subgroup [group G] (S : set G) : Prop :=
  (mul_mem : ∀ {a b}, a ∈ S → b ∈ S → a * b ∈ S)
  (one_mem : (1 : G) ∈ S)
  (inv_mem : ∀ {a}, a ∈ S → a⁻¹ ∈ S)

class normal_subgroup [group G] (S : set G) extends subgroup S : Prop :=
  (normal : ∀ n ∈ S, ∀ g : G, g * n * g⁻¹ ∈ S)

def trivial (G : Type) [group G] : set G := {1}

instance trivial_in [group G] : normal_subgroup (trivial G) :=
  begin
    apply subgroup.one_mem
  end

class group_hom [group G] [group H] (f : G → H) : Prop :=
  (hom_mul : ∀ a b, f (a * b) = f a * f b)

def kernel [group G] [group H] (f : G → H) [group_hom f] : set G :=
  preimage f (trivial H)
--/
--def f : H →* H := monoid_hom.id H 

variables {G J : Type} [group G] [group J]
variables {H : subgroup G}
variables {N : subgroup G}
variables {I : subgroup J}
variable {φ : H →* I}

lemma x_in_kernel_is_identity (k : H)(hk : k ∈ φ.ker) : φ(k) = 1 :=
begin
  exact hk,
end

#check x_in_kernel_is_identity

lemma foo (k : H)(hk : k ∈ φ.ker)(x : H) : φ(x * k * x⁻¹) = 1 :=
begin
  -- multiplication 
  have hhom : φ(x * k * x⁻¹) = φ(x) * φ(k) * φ(x⁻¹), {
    -- rewrite twice to get an obvious identiy
    rw map_mul,rw map_mul,
  },
  -- rewrite our hypothethis
  rw hhom,
  -- homomorphism preseve inverses
  rw map_inv,
  rw x_in_kernel_is_identity k hk,
end

lemma blah (f : H →* I) : subgroup.normal (f.ker) :=

begin

  exact monoid_hom.normal_ker f,
end

let k ∈ φ.ker 
-- {hk : k ∈ φ.ker} 
lemma xkxinv_in_k (i : id I)(x : H)(k ∈ φ.ker) : φ(x * k * x⁻¹) = i  :=
begin

end

-- type issue...
theorem kernel_is_normal_subgroup_of_domain (k : H) : φ.ker → H.normal :=
begin
  intro K,
end

end my_kernel_norm_sub