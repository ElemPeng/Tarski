import Tarski.Ch6

section Ch7
namespace Geom

-- Def 7.1
/- m is the midpoint of the segment ab if m lies on segment ab and ma ≡ mb
-/
def M {G : Geom} (a m b : Point) := B a m b ∧ E m a m b

-- Satz 7.2

@[symm] theorem midpt_symm {G : Geom} {a m b : Point} : M a m b → M b m a :=
  fun ⟨hb, he⟩ ↦ ⟨hb.symm, he.symm⟩

theorem M.symm {G : Geom} {a m b : Point} (h : M a m b) : M b m a := midpt_symm h

-- Satz 7.3

theorem midpt_triv {G : Geom} {a m : Point} : M a m a ↔ m = a := by
  constructor
  · exact fun ⟨h, _⟩ ↦ (btwn_id h).symm
  · intro h; subst h; exact ⟨btwn_refl, E_refl⟩

-- Satz 7.4
theorem refl_thru_pt {G : Geom} (a : Point) : ∀ p, ∃ p', M p a p' := by
  intro p; by_cases hap : a = p
  · subst hap; exact ⟨a, midpt_triv.mpr rfl⟩
  · have ⟨p', hb, he⟩ := sgmt_const p a a p; exact ⟨p', hb, he.symm⟩

theorem unique_refl_thru_pt {G : Geom} {a : Point} : ∀ p q1 q2, M p a q1 → M p a q2 → q1 = q2 := by
  intro p q1 q2 ⟨hb1, he1⟩ ⟨hb2, he2⟩; by_cases hap : a = p
  · subst hap; exact (E_id he2.symm.l) ▸ (E_id he1.symm.l)
  · exact unique_sgmt_const (Ne.symm hap) hb1 he1.symm hb2 he2.symm

-- Satz 7.5 : definition of the reflection of p through a
noncomputable def Point.R {G : Geom} (a : Point) : Point → Point := fun p ↦
  Exists.choose (refl_thru_pt a p)

-- Satz 7.6
theorem eq_aRp_of_pt_reflect {G : Geom} {a p q: Point} : M p a q → a.R p = q := by
  intro h; unfold Point.R; let P := refl_thru_pt a p; symm
  apply unique_refl_thru_pt p q (Exists.choose P) h (Exists.choose_spec P)

theorem pt_reflect_of_eq_aRp {G : Geom} {a p q: Point} : a.R p = q → M p a q := by
  intro h; unfold Point.R at h; rw [←h]; exact Exists.choose_spec (refl_thru_pt a p)

theorem eq_aRp_iff_pt_reflect {G : Geom} {a p q: Point} : a.R p = q ↔ M p a q :=
  Iff.intro pt_reflect_of_eq_aRp eq_aRp_of_pt_reflect

-- Satz 7.7
theorem double_reflect {G : Geom} {a p : Point} : a.R (a.R p) = p := by
  rw [eq_aRp_iff_pt_reflect]; symm; unfold Point.R
  exact Exists.choose_spec (refl_thru_pt a p)

-- Satz 7.something
theorem R_involution {G : Geom} {a : Point} : a.R ∘ a.R = id := by
  funext q; exact double_reflect

end Geom
end Ch7
