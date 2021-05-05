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

-- Transforming floats to rational numbers.

def to_rat : float_raw → ℚ := λ x, x.m * 2 ^ x.e

-- Some tactics to make the proofs shorter.

namespace tactic 
namespace interactive

-- TODO: Move
lemma pow_rat_cast (x : ℤ) {y : ℤ} (hy : 0 ≤ y) : ((x ^ int.to_nat y) : ℚ) = (x : ℚ) ^ (y : ℤ) :=
begin
  lift y to ℕ using hy, rw [int.to_nat_coe_nat], norm_num,
end 

open tactic
open interactive (parse)
open interactive.types
open lean.parser (ident)

meta def apply_pow_rat_cast (h : parse ident) : tactic unit := do 
  e ← get_local h,
  t ← infer_type e,
  r ← match t with 
  | `(%%a ≤ %%b) := tactic.to_expr ``(pow_rat_cast 2 (sub_nonneg.2 %%e))
  | `(¬(%%a ≤ %%b)) := tactic.to_expr ``(pow_rat_cast 2 (sub_nonneg.2 (le_of_not_le %%e)))
  | _ := failed
  end,
  rewrite_target r {md := semireducible}

meta def simplify_neg : tactic unit := do
  `[simp only [float_raw.neg] at *;
    try { simp only [has_equiv.equiv, setoid.r, R, to_rat] }; 
    try { dsimp }; push_cast]

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

-- Properties of `to_rat`.

namespace to_rat 

lemma neg {x y : float_raw} (h : to_rat x = to_rat y) 
: to_rat (float_raw.neg x) = to_rat (float_raw.neg y) :=
begin 
  simp [float_raw.neg, to_rat] at *, dsimp,
  iterate 2 { rw [int.cast_neg, ←neg_mul_eq_neg_mul], }, rw h,
end

lemma add {x y x' y' : float_raw} (h : to_rat x = to_rat y) (h' : to_rat x' = to_rat y')
: to_rat (float_raw.add x x') = to_rat (float_raw.add y y') :=
begin 
  simp [float_raw.add, to_rat] at *, split_ifs; push_cast;
  iterate 2 { rw [add_mul], };
  apply_pow_rat_cast h_1; apply_pow_rat_cast h_2;
  iterate 2 { erw [mul_assoc, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0)], }; simp,
  { rw [h, h']; ring, }, 
  { rw [h, ←h']; ring, },
  { rw [←h, h']; ring, }, 
  { rw [←h, ←h']; ring, },
end 

lemma mul {x y x' y' : float_raw} (h : to_rat x = to_rat y) (h' : to_rat x' = to_rat y')
: to_rat (float_raw.mul x x') = to_rat (float_raw.mul y y') :=
begin 
  simp [float_raw.mul, to_rat] at *, dsimp,
  simp only [fpow_add (by norm_num : (2 : ℚ) ≠ 0)], push_cast,
  calc ↑(x.m) * ↑(x'.m) * ((2 : ℚ) ^ x.e * (2 : ℚ) ^ x'.e) 
      = (↑(x.m) * 2 ^ x.e) * (↑(x'.m) * 2 ^ x'.e) : by ring 
  ... = (↑(y.m) * 2 ^ y.e) * (↑(y'.m) * 2 ^ y'.e) : by rw [h, h']
  ... = ↑(y.m) * ↑(y'.m) * (2 ^ y.e * 2 ^ y'.e) : by ring,
end 

end to_rat 

-- Define `float` as `float_raw` modulo `to_rat`.

@[reducible] private def R (x y : float_raw) : Prop := to_rat x = to_rat y
private lemma R.reflexive : reflexive R := λ x, by unfold R; exact eq.refl
private lemma R.symmetric : symmetric R := λ x y, by unfold R; exact eq.symm
private lemma R.transitive : transitive R := λ x y z, by unfold R; exact eq.trans
private lemma R.equivalence : equivalence R := ⟨R.reflexive, R.symmetric, R.transitive⟩

instance float_raw.setoid : setoid float_raw := ⟨R, R.equivalence⟩

def float : Type* := quotient float_raw.setoid

notation `𝔽` := float

namespace float 

def mk  (m e : ℤ) : 𝔽 := ⟦⟨m, e⟩⟧ 

def of_int (n : ℤ) : float := mk n 0

def eval : 𝔽 → ℚ := quotient.lift to_rat (λ a b h, h)

def repr : 𝔽 → string := rat.repr ∘ eval

instance : has_repr 𝔽 := ⟨float.repr⟩
instance : has_to_string 𝔽 := ⟨float.repr⟩
meta instance : has_to_format 𝔽 := ⟨coe ∘ float.repr⟩

-- `float` is a linearly ordered commutative ring.

instance : has_zero float := ⟨mk 0 0⟩
instance : has_one float := ⟨mk 1 0⟩
instance : inhabited float := ⟨0⟩

@[simp] lemma mk_zero (e : ℤ) : mk 0 e = 0 := 
begin 
  apply quotient.sound, show to_rat _ = _, simp [to_rat],
end

/-- Negation of floats. -/
def neg : 𝔽 → 𝔽 :=
quotient.lift (λ x, ⟦float_raw.neg x⟧) (λ a b h, quotient.sound $ to_rat.neg h)

instance : has_neg 𝔽 := ⟨neg⟩

@[simp] lemma neg_def {m e : ℤ} 
: - mk m e = mk (-m) e :=
begin 
  simp [mk], apply quotient.sound, show to_rat _ = _, simp [to_rat, float_raw.neg],
end 

/-- Addition of floats. -/
def add : 𝔽 → 𝔽 → 𝔽 :=
quotient.lift₂ (λ x y, ⟦float_raw.add x y⟧) (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound $ to_rat.add h₁ h₂)

instance : has_add 𝔽 := ⟨add⟩

@[simp] lemma add_def {m₁ m₂ e₁ e₂ : ℤ}
: (mk m₁ e₁) + (mk m₂ e₂) =
  if e₁ ≤ e₂ 
  then mk (m₁ + m₂ * 2 ^ int.to_nat (e₂ - e₁)) e₁ 
  else mk (m₂ + m₁ * 2 ^ int.to_nat (e₁ - e₂)) e₂ :=
begin 
  split_ifs, all_goals { 
    simp [mk], apply quotient.sound, 
    show to_rat _ = _, simp [to_rat, float_raw.add], 
    split_ifs, refl, },
end 

/-- Multiplication of floats. -/
def mul : 𝔽 → 𝔽 → 𝔽 :=
quotient.lift₂ (λ x y, ⟦float_raw.mul x y⟧) (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound $ to_rat.mul h₁ h₂)

instance : has_mul 𝔽 := ⟨mul⟩

@[simp] lemma mul_def {m₁ m₂ e₁ e₂ : ℤ}
: (mk m₁ e₁) * (mk m₂ e₂) = mk (m₁ * m₂) (e₁ + e₂) :=
begin 
  simp [mk], apply quotient.sound, show to_rat _ = _, simp [to_rat, float_raw.mul],
end 

-- Lemmas to prove that 𝔽 is a `comm_ring`. 

variables (x y z : 𝔽)

protected lemma add_zero : x + 0 = x :=
quotient.induction_on x (λ a, quotient.sound $ by simplify_add; apply_pow_rat_cast h; simp)

protected lemma zero_add : 0 + x = x :=
quotient.induction_on x (λ a, quotient.sound $ by simplify_add; apply_pow_rat_cast h; simp)

protected lemma add_comm : x + y = y + x :=
quotient.induction_on₂ x y (λ a b, quotient.sound $ 
begin 
  simplify_add; apply_pow_rat_cast h; apply_pow_rat_cast h_1;
  simp [add_mul, mul_assoc, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0), add_comm],
end)

protected lemma add_assoc : x + y + z = x + (y + z) :=
quotient.induction_on₃ x y z (λ a b c, quotient.sound $
begin 
  simplify_add; apply_pow_rat_cast h; apply_pow_rat_cast h_1; try { apply_pow_rat_cast h_2, };
  simp [add_mul, mul_assoc, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0), add_comm, add_assoc]; ring,
end)

protected lemma add_left_neg : -x + x = 0 := 
quotient.induction_on x (λ a, quotient.sound $ by simplify_add; simplify_neg; simp)

protected lemma mul_zero : x * 0 = 0 :=
quotient.induction_on x (λ a, quotient.sound $ by simplify_mul; simp)

protected lemma zero_mul : 0 * x = 0 :=
quotient.induction_on x (λ a, quotient.sound $ by simplify_mul; simp)

protected lemma mul_one : x * 1 = x :=
quotient.induction_on x (λ a, quotient.sound $ by simplify_mul; simp)

protected lemma one_mul : 1 * x = x :=
quotient.induction_on x (λ a, quotient.sound $ by simplify_mul; simp)

protected lemma mul_comm : x * y = y * x :=
quotient.induction_on₂ x y (λ a b, quotient.sound $
begin 
  simplify_mul, simp [fpow_add (by norm_num : (2 : ℚ) ≠ 0)], ring,
end)

protected lemma mul_assoc : x * y * z = x * (y * z) :=
quotient.induction_on₃ x y z (λ a b c, quotient.sound $
begin 
  simplify_mul, simp [fpow_add (by norm_num : (2 : ℚ) ≠ 0)], ring,
end)

protected lemma left_distrib : x * (y + z) = (x * y) + (x * z) := 
quotient.induction_on₃ x y z (λ a b c, quotient.sound $
begin 
  simplify_mul; simplify_add; apply_pow_rat_cast h; apply_pow_rat_cast h_1;
  simp [add_mul, mul_add, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0)]; ring!,
  { left, ring, },
  { replace h_1 := (add_le_add_iff_left a.e).1 (le_of_not_le h_1),
    simp [le_antisymm h h_1], left, ring, },
  { replace h_1 := (add_le_add_iff_left a.e).1 h_1,
    simp [le_antisymm (le_of_not_le h) h_1], left, ring, },
  { left, ring, },
end)

protected lemma right_distrib : (x + y) * z = (x * z) + (y * z) := 
quotient.induction_on₃ x y z (λ a b c, quotient.sound $
begin 
  simplify_mul; simplify_add; apply_pow_rat_cast h; apply_pow_rat_cast h_1;
  simp [add_mul, mul_add, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0)]; ring!,
  { left, ring, },
  { replace h_1 := (add_le_add_iff_right c.e).1 (le_of_not_le h_1),
    simp [le_antisymm h h_1], left, ring, },
  { replace h_1 := (add_le_add_iff_right c.e).1 h_1,
    simp [le_antisymm (le_of_not_le h) h_1], left, ring, },
  { left, ring, },
end)

instance : comm_ring 𝔽 := {
  zero := 0,
  one := 1,
  neg := float.neg,    
  add := float.add,
  mul := float.mul,
  add_zero := float.add_zero, 
  zero_add := float.zero_add, 
  add_comm := float.add_comm, 
  add_assoc := float.add_assoc,
  add_left_neg := float.add_left_neg,
  mul_one := float.mul_one, 
  one_mul := float.one_mul, 
  mul_comm := float.mul_comm,
  mul_assoc := float.mul_assoc,
  left_distrib := float.left_distrib,
  right_distrib := float.right_distrib,
}

-- Lemmas to prove that 𝔽 is a `linear_ordered_comm_ring`. 

@[simp] lemma eval_mk {m e : ℤ} : eval (mk m e) = m * 2 ^ e := rfl

@[simp] lemma eval_add (x y : 𝔽) : eval (x + y) = (eval x) + (eval y) :=
begin 
  apply quotient.induction_on₂ x y, intros a b, show to_rat _ = to_rat _ + to_rat _, 
  simplify_add; apply_pow_rat_cast h; 
  simp [add_mul, mul_assoc, ←fpow_add (by norm_num : (2 : ℚ) ≠ 0)], ring,
end

@[simp] lemma eval_mul (x y : 𝔽) : eval (x * y) = (eval x) * (eval y) :=
begin 
  apply quotient.induction_on₂ x y, intros a b, show to_rat _ = to_rat _ * to_rat _, 
  simplify_mul, simp [fpow_add (by norm_num : (2 : ℚ) ≠ 0)], ring,
end

/-- Comparison of floats. -/
def le : 𝔽 → 𝔽 → Prop := λ x y, eval x ≤ eval y
def lt : 𝔽 → 𝔽 → Prop := λ x y, eval x < eval y

instance : has_le 𝔽 := ⟨le⟩
instance : has_lt 𝔽 := ⟨lt⟩

protected lemma le_refl : x ≤ x := 
quotient.induction_on x (λ a, rat.le_refl _)

protected lemma le_trans : x ≤ y → y ≤ z → x ≤ z := 
quotient.induction_on₃ x y z (λ a b c h1 h2, rat.le_trans h1 h2)

protected lemma le_antisymm : x ≤ y → y ≤ x → x = y :=
quotient.induction_on₂ x y (λ a b h1 h2, by apply quotient.sound; exact (rat.le_antisymm h1 h2))

protected lemma add_le_add_left : x ≤ y → ∀ (c : 𝔽), c + x ≤ c + y :=
begin 
  apply quotient.induction_on₂ x y, intros a b h z, 
  apply quotient.induction_on z, intros c,
  show eval _ ≤ eval _, simp only [eval_add],
  exact (rat.add_le_add_left.2 h),
end

protected lemma zero_le_one : (0 : 𝔽) ≤ 1 :=
begin 
  show to_rat _ ≤ to_rat _, simp [to_rat], push_cast, simp, linarith,
end

protected lemma mul_pos : 0 < x → 0 < y → 0 < x * y :=
begin 
  apply quotient.induction_on₂ x y, intros a b h1 h2,
  show _ < eval _, simp only [eval_mul],
  exact (mul_pos h1 h2),
end

protected lemma le_total : x ≤ y ∨ y ≤ x :=
begin 
  apply quotient.induction_on₂ x y, intros a b, exact (rat.le_total _ _),
end

-- protected lemma decidable_le : decidable (x ≤ y) := 
-- rat.decidable_le (eval x) (eval y)

instance decidable_le : decidable_rel ((≤) : 𝔽 → 𝔽 → Prop) :=
λ a b, rat.decidable_le (eval a) (eval b)

protected lemma exists_pair_ne : ∃ (x y : 𝔽), x ≠ y :=
begin 
  use [⟦⟨0, 0⟩⟧, ⟦⟨1, 0⟩⟧], simp, show ¬(to_rat _ = to_rat _), 
  intros hc, simp [to_rat] at hc, exact hc,
end

instance : linear_ordered_comm_ring 𝔽 := {
  le := float.le,
  le_refl := float.le_refl, 
  le_trans := float.le_trans, 
  le_antisymm := float.le_antisymm,
  add_le_add_left := float.add_le_add_left,
  zero_le_one := float.zero_le_one, 
  mul_pos := float.mul_pos, 
  le_total := float.le_total, 
  decidable_le := float.decidable_le,
  exists_pair_ne := float.exists_pair_ne,
  ..float.comm_ring 
}

end float
