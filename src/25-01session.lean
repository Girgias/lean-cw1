import tactic
import data.real.basic

#check set ℕ

variable (S: set ℕ)

#check S

def X : set ℕ := {1,2,3}

def Y : set ℕ := {n : ℕ | ∃ t, n = 2 * t}

def Z := X ∩ Y

#check Z


-- #check (1 : Z) -- fails because set is not a type but somehoh a subset

-- set_option pp.notation false

example : 2 ∈ Z :=
begin
  -- unfold is very useful to figure out what you're working with
  --unfold Z, -- evil tactic as you're not using the API/interface for it
  --have h : 2 ∈ X ∧ 2 ∈ Y,
  -- Introduce a new goal (i.e. a sub lemma)
  -- suffices h : 2 ∈ X ∧ 2 ∈ Y,
  -- Same as have but the order is reversed
  --swap, -- Swap the order of goals
  split,
  {
    --unfold X,
    right, left, refl,
  },
  {
    --change ∃ t, 2 = 2 * t,
    --use 1,
    --norm_num,
    -- or using term mode
    exact ⟨1, rfl⟩,
  }
end