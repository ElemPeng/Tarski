import Tarski.Ch7

section Ch8
namespace Geom
-- Def 8.1 : Right angles
/- ∠ abc is a right angle if a is equidistant from c and the reflection of
c through the point b. (insert picture of isosceles triangle a c c' with
base midpoint b here.)
-/
def Right {G : Geom} (a b c : Point) := E a c a (b.R c)

-- Satz 8.2
theorem right_symm {G : Geom} {a b c : Point} : Right a b c → Right c b a := by
  intro h; have h1 : E a (b.R c) (b.R a) c := by
    conv in (occs := 2) c => rw [←double_reflect b c]
    exact R_isometry
  unfold Right at h ⊢; exact (E_trans h h1).lr

-- Satz 8.3
/-  if a ≠ b ∧ ∠abc is a right angle, then so is ∠a'bc for any point
    a' on Line a b
-/
theorem right_extend {G : Geom} {a b c a' : Point} : Right a b c → a ≠ b → Col a b a' →
  Right a' b c := by
  intro hr1 hne1 hcol1; unfold Right at hr1 ⊢
  apply E_of_ne_col_E hne1 hcol1 hr1 (?_)
  conv in (occs := 2) b => rw [←R_self b]
  exact R_isometry

-- Satz 8.4
theorem right_R {G : Geom} {a b c : Point} : Right a b c → Right a b (b.R c) := by
  intro h; unfold Right at h ⊢
  conv in (b.R (b.R c)) => rw [double_reflect b c]
  exact h.symm

-- Satz 8.5
theorem right_triv {G : Geom} {a b : Point} : Right a b b := by
  unfold Right; rw [R_self b]; exact E_refl

-- Satz 8.6
end Geom
end Ch8
