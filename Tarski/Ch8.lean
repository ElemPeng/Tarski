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
@[symm] theorem right_symm {G : Geom} {a b c : Point} : Right a b c → Right c b a := by
  intro h; have h1 : E a (b.R c) (b.R a) c := by
    conv in (occs := 2) c => rw [←double_reflect b c]
    exact R_isometry
  unfold Right at h ⊢; exact (E_trans h h1).lr

theorem Right.symm {G : Geom} {a b c : Point} (h : Right a b c) : Right c b a := right_symm h
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
theorem right_abRc_of_Rabc {G : Geom} {a b c : Point} : Right a b c → Right a b (b.R c) := by
  intro h; unfold Right at h ⊢
  conv in (b.R (b.R c)) => rw [double_reflect b c]
  exact h.symm

-- Satz 8.5
theorem right_abb {G : Geom} {a b : Point} : Right a b b := by
  unfold Right; rw [R_self b]; exact E_refl

theorem right_aab {G : Geom} {a b : Point} : Right a a b := (right_abb).symm

-- Satt 8.6
/- This is saying, more or less, that if you drop a perpendicular from a point
c to the line a a', then it has a unique foot b-/
theorem eq_of_Rabc_Ra'bc_aca' {G : Geom} {a a' b c : Point} :
Right a b c → Right a' b c → B a c a' → b = c := by
  intro hr1 hr2 hb1; unfold Right at hr1 hr2
  have heq : c = b.R c := eq_of_btwn_E hb1 hr1 hr2
  symm at heq ⊢; rwa [← R_eq_self_iff]

-- Satz 8.7
theorem eq_of_Rabc_Racb {G : Geom} {a b c : Point} :
Right a b c → Right a c b → b = c := by
  intro hr1 hr2; generalize hc' : b.R c = c'; generalize ha' : c.R a = a'
  have hcol1 : Col b c c' := by rw [aRp_q_iff_Mpaq] at hc'; exact hc'.1.col.xy
  apply Classical.byContradiction; intro hbc
  have hr3 : Right a c c' := right_symm <| right_extend (hr2.symm) (hbc) hcol1
  have he1 : E a c a' c := by rw [aRp_q_iff_Mpaq] at ha'; exact ha'.2.lr
  have he2 : E a c' a' c' := by rw [←ha']; apply E_flip_both; exact hr3.symm
  have he3 : E a c a c' := by rwa [←hc']
  have hr4 : Right a' b c := by
    unfold Right; rw [hc']; exact E_trans he1.symm <| E_trans he3 he2
  have hb1 : B a c a' := by rw [aRp_q_iff_Mpaq] at ha'; exact ha'.1
  exact hbc <| eq_of_Rabc_Ra'bc_aca' hr1 hr4 hb1

-- Satz 8.8
theorem eq_of_Raba {G : Geom} {a b : Point} : Right a b a → a = b :=
  fun h ↦ (eq_of_Rabc_Racb h right_abb.symm).symm

-- Satz 8.9
theorem eq_or_eq_of_right_col {G : Geom} {a b c : Point} :
Right a b c → Col a b c → a = b ∨ c = b := by
  intro hr hc; rw [Classical.or_iff_not_imp_left]; intro hab
  have hr2 : Right c b c := right_extend hr hab hc
  exact eq_of_Raba hr2

-- Satz 8.10 -- basically side side side but only for right triangles
theorem right_of_right_E3 {G : Geom} {a b c a' b' c' : Point} :
Right a b c → E3 a b c a' b' c' → Right a' b' c' := by
  intro hr1 ⟨he1, he2, he3⟩; by_cases hbc : b = c
  · subst hbc; have hbc' : b' = c' := E_id he2.symm; subst hbc'
    exact right_abb
  have hbc' : b' ≠ c' := E_id_mt hbc he2.symm; change b ≠ c at hbc
  generalize hd : b.R c = d; generalize hd' : b'.R c' = d'
  rw [aRp_q_iff_Mpaq] at hd hd'
  have he4 := E_trans (E_trans hd.2.symm he2) hd'.2
  have hafs := outer_five_sgmt hbc.symm hd.1 hd'.1 he2.lr he4 he3.lr he1.lr
  rw [← aRp_q_iff_Mpaq] at hd hd'; unfold Right at hr1 ⊢
  subst hd hd'; exact E_trans (E_trans he3.symm hr1) hafs.lr

-- Def 8.11
def PSet.perp_at_x {G : Geom} (A A' : PSet G) (x : Point) :=
IsLine A ∧ IsLine A' ∧ x ∈ A ∧ x ∈ A' ∧ ∀ u v : Point, (u ∈ A → v ∈ A' → Right u x v)

notation:80 A " ⟂[" x "] " B => PSet.perp_at_x A B x

example {G : Geom} (A B : PSet G) (x : Point) :
  (A ⟂[x] B) ↔ A.perp_at_x B x := by rfl

def PSet.perp {G : Geom} (A A' : PSet G) := ∃ x : Point, A.perp_at_x A' x

infix:80 "⟂" => PSet.perp
/- SST has another notation ab ⟂ cd for Line ab ⟂ Line cd but i'll just
write Line ab and Line cd
-/

-- Satz 8.12
theorem perp_at_x_symm {G : Geom} {A B : PSet G} {x : Point} : (A ⟂[x] B) → (B ⟂[x] A) :=
  fun ⟨hA, hB, hxA, hxB, hxR⟩ ↦ ⟨hB, hA, hxB, hxA, fun u v hu hv ↦ (hxR v u hv hu).symm⟩

theorem PSet.perp_at_x.symm {G : Geom} {A B : PSet G} {x : Point} (h : A ⟂[x] B) :
  B ⟂[x] A := perp_at_x_symm h

theorem perp_symm {G : Geom} {A B : PSet G} : A ⟂ B → B ⟂ A :=
fun ⟨x, hx⟩ ↦ ⟨x, hx.symm⟩

theorem perp.symm {G : Geom} {A B : PSet G} (h : A ⟂ B) : B ⟂ A := perp_symm h

-- Satz 8.13 : perpendicular lines form nontrivial right angles

-- lemma i need

theorem nontriv_right_of_perp_at_x {G : Geom} {A B : PSet G} {x : Point} : (A ⟂[x] B) →
  IsLine A ∧ IsLine B ∧ x ∈ A ∧ x ∈ B ∧ (∃ u v : Point,
  u ∈ A ∧ v ∈ B ∧ u ≠ x ∧ v ≠ x ∧ Right u x v) := by
  intro ⟨hA, hB, hxA, hxB, hxR⟩; refine ⟨hA, hB, hxA, hxB, ?_⟩
  have ⟨a1, a2, ha1a2, hA'⟩ := hA
  have ⟨u, hux, huA⟩ := another_pt_on_line hA hxA
  have ⟨v, hvx, hvB⟩ := another_pt_on_line hB hxB
  refine ⟨u, v, huA, hvB, hux, hvx, hxR u v huA hvB⟩

theorem perp_at_x_of_nontriv_right {G : Geom} {A B : PSet G} {x : Point} :
IsLine A → IsLine B → x ∈ A → x ∈ B → (∃ u v : Point,
  u ∈ A ∧ v ∈ B ∧ u ≠ x ∧ v ≠ x ∧ Right u x v) → (A ⟂[x] B) := by
  intro hA hB hxA hxB ⟨u, v, huA, hvB, hux, hvx, hR⟩
  refine ⟨hA, hB, hxA, hxB, ?_⟩; intro u' v' hu'A hv'B
  have h' : Right u' x v := right_extend hR hux <|
  col_iff_on_same_line.mpr ⟨A, hA, huA, hxA, hu'A⟩; symm at h' ⊢
  exact right_extend h' hvx <| col_iff_on_same_line.mpr ⟨B, hB, hvB, hxB, hv'B⟩


end Geom
end Ch8
