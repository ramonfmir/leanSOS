import data.int.basic
import data.rat.basic
import data.real.basic
import tactic

-- Float structure before quotiening. Basic operations.

structure float_raw := (m : ℤ) (e : ℤ)

namespace float_raw 

def neg (x : float_raw) : float_raw :=
⟨-x.m, x.e⟩

def add (x y : float_raw) : float_raw :=
if x.e ≤ y.e 
then ⟨x.m + y.m * 2 ^ int.to_nat (y.e - x.e), x.e⟩ 
else ⟨y.m + x.m * 2 ^ int.to_nat (x.e - y.e), y.e⟩ 

def mul (x y : float_raw) : float_raw :=
⟨x.m * y.m, x.e + y.e⟩

end float_raw

-- To rational number properties.

def to_rat : float_raw → ℚ := λ x, x.m * 2 ^ x.e

-- TODO: Move
lemma pow_rat_cast (x : ℤ) {y : ℤ} (hy : 0 ≤ y) : ((x ^ int.to_nat y) : ℚ) = (x : ℚ) ^ (y : ℤ) :=
begin
  lift y to ℕ using hy, rw [int.to_nat_coe_nat], norm_num,
end 

-- Some tactics.

open tactic
open interactive (parse)
open interactive.types
open lean.parser (ident)

namespace tactic 
namespace interactive

meta def apply_pow_rat_cast (h : parse ident) : tactic unit := do 
  e ← get_local h,
  t ← infer_type e,
  r ← match t with 
  | `(%%a ≤ %%b) := tactic.to_expr ``(pow_rat_cast 2 (sub_nonneg.2 %%e))
  | `(¬(%%a ≤ %%b)) := tactic.to_expr ``(pow_rat_cast 2 (sub_nonneg.2 (le_of_not_le %%e)))
  | _ := failed
  end,
  rewrite_target r {md := semireducible}

meta def simplify_add : tactic unit := do
  `[simp only [float_raw.add] at *, split_ifs; 
    try { simp only [has_equiv.equiv, setoid.r, R, to_rat] }; 
    try { dsimp }; push_cast]

meta def simplify_mul : tactic unit := do
  `[simp only [float_raw.mul] at *;
    try { simp only [has_equiv.equiv, setoid.r, R, to_rat] }; 
    try { dsimp }; push_cast]

end interactive
end tactic

lemma to_rat.neg {x y : float_raw} (h : to_rat x = to_rat y) 
: to_rat (float_raw.neg x) = to_rat (float_raw.neg y) :=
begin 
  simp [float_raw.neg, to_rat] at *, dsimp,
  iterate 2 { rw [int.cast_neg, ←neg_mul_eq_neg_mul], }, rw h,
end

lemma to_rat.add {x y x' y' : float_raw} (h : to_rat x = to_rat y) (h' : to_rat x' = to_rat y')
: to_rat (float_raw.add x x') = to_rat (float_raw.add y y') :=
begin 
  simp [float_raw.add, to_rat] at *, split_ifs; push_cast;
  iterate 2 { rw [add_mul], };
  try { erw [pow_rat_cast 2 (sub_nonneg.2 h_1)], };
  try { erw [pow_rat_cast 2 (sub_nonneg.2 (le_of_not_le h_1))], };
  try { erw [pow_rat_cast 2 (sub_nonneg.2 h_2)], };
  try { erw [pow_rat_cast 2 (sub_nonneg.2 (le_of_not_le h_2))], };
  iterate 2 { erw [mul_assoc, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0)], }; simp; 
  try { rw [h, h']; ring, }; 
  try { rw [h, ←h']; ring, }; 
  try { rw [←h, h']; ring, }; 
  try { rw [←h, ←h']; ring, },
end 

lemma to_rat.mul {x y x' y' : float_raw} (h : to_rat x = to_rat y) (h' : to_rat x' = to_rat y')
: to_rat (float_raw.mul x x') = to_rat (float_raw.mul y y') :=
begin 
  simp [float_raw.mul, to_rat] at *, dsimp,
  simp only [fpow_add (by norm_num : (2 : ℚ) ≠ 0)], push_cast,
  calc ↑(x.m) * ↑(x'.m) * ((2 : ℚ) ^ x.e * (2 : ℚ) ^ x'.e) 
      = (↑(x.m) * 2 ^ x.e) * (↑(x'.m) * 2 ^ x'.e) : by ring 
  ... = (↑(y.m) * 2 ^ y.e) * (↑(y'.m) * 2 ^ y'.e) : by rw [h, h']
  ... = ↑(y.m) * ↑(y'.m) * (2 ^ y.e * 2 ^ y'.e) : by ring,
end 

-- Define floats as float_raw modulo to_rat.

@[reducible] private def R : float_raw → float_raw → Prop := λ x y, to_rat x = to_rat y
private lemma R.reflexive : reflexive R := λ x, by unfold R; exact eq.refl
private lemma R.symmetric : symmetric R := λ x y, by unfold R; exact eq.symm
private lemma R.transitive : transitive R := λ x y z, by unfold R; exact eq.trans
private lemma R.equivalence : equivalence R := ⟨R.reflexive, R.symmetric, R.transitive⟩

instance float_raw.setoid : setoid float_raw := ⟨R, R.equivalence⟩

def float : Type* := quotient float_raw.setoid

local notation `𝔽` := float

namespace float

def mk : ℤ × ℤ → 𝔽 := λ x, ⟦⟨x.1, x.2⟩⟧ 

def eval : 𝔽 → ℚ := quotient.lift to_rat (λ a b h, h)

instance : comm_semiring 𝔽 := {
  zero := ⟦⟨0, 0⟩⟧,
  one := ⟦⟨1, 0⟩⟧,    
  add := quotient.lift₂ (λ x y, ⟦float_raw.add x y⟧) (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound $ to_rat.add h₁ h₂),
  mul := quotient.lift₂ (λ x y, ⟦float_raw.mul x y⟧) (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound $ to_rat.mul h₁ h₂),
  zero_add := λ x, quotient.induction_on x (λ a, quotient.sound $
    begin 
      simplify_add; apply_pow_rat_cast h; simp,
    end), 
  add_zero := λ x, quotient.induction_on x (λ a, quotient.sound $
    begin 
      simplify_add; apply_pow_rat_cast h; simp,
    end), 
  add_assoc := λ x y z, quotient.induction_on₃ x y z (λ a b c, quotient.sound $
    begin 
      simplify_add; apply_pow_rat_cast h; apply_pow_rat_cast h_1; try { apply_pow_rat_cast h_2, };
      simp [add_mul, mul_assoc, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0), add_comm, add_assoc]; ring,
    end),
  add_comm := λ x y, quotient.induction_on₂ x y (λ a b, quotient.sound $
    begin 
      simplify_add; apply_pow_rat_cast h; apply_pow_rat_cast h_1;
      simp [add_mul, mul_assoc, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0), add_comm],
    end), 
  zero_mul := λ x, quotient.induction_on x (λ a, quotient.sound $
    begin 
      simplify_mul; simp,
    end), 
  mul_zero := λ x, quotient.induction_on x (λ a, quotient.sound $
    begin 
      simplify_mul; simp,
    end), 
  one_mul := λ x, quotient.induction_on x (λ a, quotient.sound $
    begin 
      simplify_mul; simp,
    end), 
  mul_one := λ x, quotient.induction_on x (λ a, quotient.sound $
    begin 
      simplify_mul; simp,
    end), 
  mul_comm := λ x y, quotient.induction_on₂ x y (λ a b, quotient.sound $
    begin 
      simplify_mul, simp [fpow_add (by norm_num : (2 : ℚ) ≠ 0)], ring,
    end),
  mul_assoc := λ x y z, quotient.induction_on₃ x y z (λ a b c, quotient.sound $
    begin 
      simplify_mul, simp [fpow_add (by norm_num : (2 : ℚ) ≠ 0)], ring,
    end),
  left_distrib := λ x y z, quotient.induction_on₃ x y z (λ a b c, quotient.sound $
    begin 
      simplify_mul; simplify_add; apply_pow_rat_cast h; apply_pow_rat_cast h_1;
      simp [add_mul, mul_add, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0)]; ring!,
      { left, ring, },
      { replace h_1 := (add_le_add_iff_left a.e).1 (le_of_not_le h_1),
        simp [le_antisymm h h_1], left, ring, },
      { replace h_1 := (add_le_add_iff_left a.e).1 h_1,
        simp [le_antisymm (le_of_not_le h) h_1], left, ring, },
      { left, ring, },
    end),
  right_distrib := λ x y z, quotient.induction_on₃ x y z (λ a b c, quotient.sound $
    begin 
      simplify_mul; simplify_add; apply_pow_rat_cast h; apply_pow_rat_cast h_1;
      simp [add_mul, mul_add, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0)]; ring!,
      { left, ring, },
      { replace h_1 := (add_le_add_iff_right c.e).1 (le_of_not_le h_1),
        simp [le_antisymm h h_1], left, ring, },
      { replace h_1 := (add_le_add_iff_right c.e).1 h_1,
        simp [le_antisymm (le_of_not_le h) h_1], left, ring, },
      { left, ring, },
    end),
}

def f : 𝔽 → 𝔽 → 𝔽 := 
quotient.lift₂ (λ x y, ⟦float_raw.add x y⟧) (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound $ to_rat.add h₁ h₂)

-- Nice!
#eval eval (f (⟦⟨2, -8⟩⟧ : 𝔽) (⟦⟨50, 3⟩⟧ : 𝔽))

end float
