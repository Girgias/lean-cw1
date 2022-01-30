import tactic
import group_theory.subgroup.basic

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

variables {G J : Type} [group G] [group J]
variables (H : subgroup G)
variables (N : subgroup G)
variables (I : subgroup J)

def f : H →* H := monoid_hom.id H 

#check f -- f : Π (G : Type) [_inst_1 : group G] (H : subgroup G), ↥H →* ↥H

--variables {N : Type} [group N]
variable {φ : H →* I}

def K := φ.ker

-- TODO proving that the kernel is a normal subgroup
-- ProofWiki: https://proofwiki.org/wiki/Kernel_is_Normal_Subgroup_of_Domain

-- `\``trianglel`: ◃ 

-- We use notation `N ◃ H` to say N is a normal subgroup of H.
notation N ` ◃ ` H := N → H.normal

/--
lemma in_k_is_identity (k : H) (i : id I) (hk: k ∈ φ.ker) : φ(k) = i :=
begin
  sorry,
end
--/

lemma blah (f : G →* I) : (f.ker) -> H.normal :=
begin

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