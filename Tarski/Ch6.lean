import Tarski.Ch5
section Ch6
namespace Geom

-- x.sameside y z means ray x y = ray x z ≡ and neither y nor z = x
-- for each x this is an equivalence relation on all the points other than x

def Point.sameside {G : Geom} (x y z : Point) := y ≠ x ∧ z ≠ x ∧ (B x y z ∨ B x z y)

-- Satz 6.2;
theorem ssxy_of_xaz_yaz {G : Geom} {x y z a : Point} : x ≠ a → y ≠ a → z ≠ a →
    B x a z → B y a z → a.sameside x y := by
    intro h1 h2 h3 hb1 hb2; unfold Point.sameside
    rw [btwn_symm_iff] at hb1 hb2
    exact ⟨h1, h2, (yzw_or_ywz_of_ne_xyz_xyw h3 hb1 hb2)⟩

theorem yaz_of_xaz_ssxy {G : Geom} {x y z a : Point} :
    B x a z → a.sameside x y → B y a z := by
    intro hb1 ⟨h1, _, hss1⟩; rcases hss1 with h | h
    ·   exact xzw_of_xyz_yzw_ne h.symm hb1 h1
    ·   exact yzw_of_xyz_xzw h.symm hb1

theorem ssxy_iff_yaz_of_xaz {G : Geom} {x y z a : Point} :
    x ≠ a → y ≠ a → z ≠ a → B x a z → (a.sameside x y ↔ B y a z) := by
    intro h1 h2 h3 hb1; constructor
    ·   exact yaz_of_xaz_ssxy hb1
    ·   exact ssxy_of_xaz_yaz h1 h2 h3 hb1

-- Satz 6.3
theorem exists_os_of_ss {G : Geom} {x y a : Point} :
    a.sameside x y → (∃ z, z ≠ a ∧ B x a z ∧ B y a z) := by
    intro ⟨h1, h2, hb1⟩; have ⟨z, hz1, hz2⟩ := sgmt_const' x a
    rcases hb1 with h | h
    ·   exact ⟨z, hz2.symm, hz1, xzw_of_xyz_yzw_ne h.symm hz1 h1⟩
    ·   exact ⟨z, hz2.symm, hz1, yzw_of_xyz_xzw h.symm hz1⟩

theorem ss_of_exists_os {G : Geom} {x y a : Point} : x ≠ a → y ≠ a →
    (∃ z, z ≠ a ∧ B x a z ∧ B y a z) → a.sameside x y := by
    intro h1 h2 ⟨z, h3, hb1, hb2⟩; refine ⟨h1, h2, ?_⟩
    exact yzw_or_ywz_of_ne_xyz_xyw h3 hb1.symm hb2.symm

theorem exists_os_iff_ss {G : Geom} {x y a : Point} :
    (x ≠ a ∧ y ≠ a ∧ (∃ z, z ≠ a ∧ B x a z ∧ B y a z) ↔ a.sameside x y) := by
    constructor
    · exact fun ⟨h1, h2, h3⟩ ↦ ss_of_exists_os h1 h2 h3
    · exact fun h ↦ ⟨h.1, h.2.1, exists_os_of_ss h⟩

-- Satz 6.4
theorem col_and_not_os_of_ss {G : Geom} {x y a : Point} :
    a.sameside x y → Col x a y ∧ ¬ (B x a y) := by
    intro h; have ⟨hxa, hya, z, hza, hxaz, hyaz⟩ := exists_os_iff_ss.mpr h
    rw [btwn_symm_iff] at hxaz hyaz
    have hxya_or_yxa : B a y x ∨ B a x y :=
        yzw_or_ywz_of_ne_xyz_xyw hza hyaz hxaz
    refine ⟨?_, ?_⟩
    ·   rcases hxya_or_yxa with h' | h'
        ·   exact h'.col.r
        ·   exact h'.col.xy
    ·   intro hxay; simp [btwn_symm_iff] at hxya_or_yxa
        rcases hxya_or_yxa with h' | h'
        ·   exact hya (eq_of_xyz_xzy h' hxay)
        ·   exact hxa (eq_of_xyz_xzy h' hxay.symm)

theorem ss_of_col_of_not_os {G : Geom} {x y a : Point} :
    Col x a y → ¬ (B x a y) → a.sameside x y := by
    intro hcol hxay; have ⟨hax, hya⟩ := dist_of_not_btwn hxay
    refine ⟨hax, hya.symm, ?_⟩; unfold Col at hcol
    rw [Or.comm, btwn_symm_iff (y := x)]; exact Or.resolve_left hcol hxay

theorem ss_iff_col_and_not_os {G : Geom} {x y a : Point} :
    a.sameside x y ↔ Col x a y ∧ ¬ (B x a y) :=
    Iff.intro col_and_not_os_of_ss <| fun ⟨h1, h2⟩ ↦ ss_of_col_of_not_os h1 h2

-- Satz 6.5
theorem ss_refl {G : Geom} {a x : Point} : x ≠ a → a.sameside x x :=
    fun h ↦ ⟨h, h, Or.inl btwn_refl'⟩

-- Satz 6.6
theorem ss_symm {G : Geom} {a x y : Point} : a.sameside x y → a.sameside y x :=
    fun ⟨hx, hy, h⟩ ↦ ⟨hy, hx, h.symm⟩

-- Satz 6.7
theorem ss_trans {G : Geom} {a x y z : Point} :
    a.sameside x y → a.sameside y z → a.sameside x z := by
    intro ⟨hx, hy, hxy⟩ ⟨_, hz, hyz⟩; refine ⟨hx, hz, ?_⟩
    rcases hxy with h1 | h1 <;> rcases hyz with h2 | h2
    ·   exact Or.inl (xyw_of_xyz_xzw h1 h2)
    ·   exact xyz_or_xzy_of_xyw_xzw h1 h2
    ·   exact xzw_or_xwz_of_ne_xyz_xyw (hy.symm) h1 h2
    ·   exact Or.inr (xyw_of_xyz_xzw h2 h1)


end Geom
end Ch6
