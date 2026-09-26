import Tarski.Satz5_1

section Ch5
namespace Geom
-- Satz 5.2
theorem yzw_or_ywz_of_ne_xyz_xyw {G : Geom} {x y z w : Point} :
x ≠ y → B x y z → B x y w → (B y z w ∨ B y w z) := by
    intro hne hb1 hb2; rcases (xzw_or_xwz_of_ne_xyz_xyw hne hb1 hb2) with h | h
    ·   exact Or.inl (yzw_of_xyz_xzw hb1 h)
    ·   exact Or.inr (yzw_of_xyz_xzw hb2 h)

-- Satz 5.3
theorem xyz_or_xzy_of_xyw_xzw {G : Geom} {x y z w : Point} :
B x y w → B x z w → (B x y z ∨ B x z y) := by
    intro hb1 hb2; have ⟨u, hu1, hu2⟩ := sgmt_const' x w
    have hywu : B y w u := yzw_of_xyz_xzw hb1 hu1
    have hzwu : B z w u := yzw_of_xyz_xzw hb2 hu1
    have h1 : B w z y ∨ B w y z := yzw_or_ywz_of_ne_xyz_xyw hu2.symm hzwu.symm hywu.symm
    rw [btwn_symm_iff] at hb1 hb2; rcases h1 with h | h
    ·   exact Or.inl (yzw_of_xyz_xzw h hb1).symm
    ·   exact Or.inr (yzw_of_xyz_xzw h hb2).symm

-- Def 5.4: less than or equal to

def le {G : Geom} (x y z w : Point) := ∃ a, (B z a w ∧ E x y z a)

-- Satz 5.5
theorem sgmt_of_le {G : Geom} {x y z w : Point} :
    le x y z w → ∃ a, B x y a ∧ E x a z w := by
    intro ⟨b, hb1, he1⟩; have ⟨a, hb2, he2⟩ := sgmt_const x y b w
    exact ⟨a, hb2, sgmt_add hb2 hb1 he1 he2⟩

theorem le_of_sgmt {G : Geom} {x y z w : Point} :
    (∃ a, B x y a ∧ E x a z w) → le x y z w := by
    intro ⟨b, hb1, he1⟩; have ⟨a, hb2, he2, he3⟩ := sgmt_split hb1 he1
    exact ⟨a, hb2, he2⟩

theorem le_iff {G : Geom} {x y z w : Point} : le x y z w ↔ (∃ a, B x y a ∧ E x a z w) :=
    Iff.intro sgmt_of_le le_of_sgmt

-- Satz 5.6
theorem le_of_le_E {G : Geom} {x y z w x' y' z' w': Point} :
    le x y z w → E x y x' y' → E z w z' w' → le x' y' z' w' := by
    intro ⟨a, ha1, ha2⟩ he1 he2; have ⟨a', ha'1, ha'2, _⟩ := sgmt_split ha1 he2
    refine ⟨a', ha'1, E_trans (E_trans he1.symm ha2) ha'2⟩

theorem le.l {G : Geom} {x y z w : Point} (h : le x y z w) : le y x z w :=
    le_of_le_E h E_comm E_refl

theorem le.r {G : Geom} {x y z w : Point} (h : le x y z w) : le x y w z :=
    le_of_le_E h E_refl E_comm

theorem le.lr {G : Geom} {x y z w : Point} (h : le x y z w) : le y x w z := h.l.r

-- Satz 5.7
theorem le_refl {G : Geom} {x y : Point} : le x y x y := ⟨y, btwn_refl', E_refl⟩

-- Satz 5.8
theorem le_trans {G : Geom} {x y z w u v : Point} : le x y z w → le z w u v → le x y u v := by
    intro ⟨a, ha1, ha2⟩ ⟨b, hb1, hb2⟩; have ⟨c, hc1, hc2, hc3⟩ := sgmt_split ha1 hb2
    exact ⟨c, xyw_of_xyz_xzw hc1 hb1, E_trans ha2 hc2⟩

-- narboux's lemma
theorem narboux_lemma {G : Geom} {x y z : Point} : B x y z → E x y x z → y = z := by
    intro hb1 he1; by_cases h : x = y
    ·   subst h; exact E_id he1.symm
    have ⟨w, hw1, hw2⟩ := sgmt_const' y x; rw [btwn_symm_iff] at hw1
    have hw3 : B w x z := xyw_of_xyz_yzw_ne hw1 hb1 h
    apply unique_sgmt_const hw2.symm hw1 he1 hw3 E_refl

-- Satz 5.9
theorem le_antisymm {G : Geom} {x y z w : Point} : le x y z w → le z w x y → E x y z w := by
    intro ⟨a, ha1, ha2⟩ ⟨b, hb1, hb2⟩; have ⟨c, hc1, hc2, hc3⟩ := sgmt_split ha1 hb2
    have he1 : E x y x c := E_trans ha2 hc2
    have hb3 : B x c y := xyw_of_xyz_xzw hc1 hb1
    have heq1 : c = y := narboux_lemma hb3 he1.symm
    subst heq1; have heq2 : c = b := eq_of_xyz_xzy hc1 hb1
    subst heq2; exact hb2.symm

-- Satz 5.10
theorem le_total {G : Geom} {x y z w : Point} : le x y z w ∨ le z w x y := by
    have ⟨b, ha1, ha2⟩ := sgmt_const' w z; rw [btwn_symm_iff] at ha1
    have ⟨a, hb1, hb2⟩ := sgmt_const b z x y
    have h := yzw_or_ywz_of_ne_xyz_xyw ha2.symm ha1 hb1
    rcases h with h' | h'
    ·   apply Or.inr; rw [le_iff]; exact ⟨a, h', hb2⟩
    ·   apply Or.inl; exact ⟨a, h', hb2.symm⟩

-- Satz 5.11
theorem nonneg {G : Geom} {x y z : Point} : le z z x y := ⟨x, btwn_refl, degen_sgmts⟩

-- Satz 5.12
theorem le_of_btwn_left {G : Geom} {x y z : Point} : B x y z → le x y x z := by
    intro hb1; exact ⟨y, hb1, E_refl⟩

theorem le_of_btwn_right {G : Geom} {x y z : Point} : B x y z → le y z x z := by
    intro hb1; unfold le; rw [btwn_symm_iff] at hb1;
    have ⟨a, ha1, ha2, ha3⟩ := sgmt_split hb1 E_comm; exact ⟨a, ha1, ha2.l⟩

theorem btwn_of_col_le {G : Geom} {x y z : Point} :
    Col x y z → le x y x z → le y z x z → B x y z := by
    intro hcol hle1 hle2; rcases hcol with h | h | h
    ·   exact h
    ·   have hle3 : le x z x y := (le_of_btwn_right h).lr; rw [btwn_symm_iff] at h
        have heq1 : E x y x z := le_antisymm hle1 hle3
        have heq2 : z = y := narboux_lemma h <| heq1.symm
        subst heq2; exact btwn_refl'
    ·   have hle3 : le x z y z := (le_of_btwn_left h).lr; rw [btwn_symm_iff] at h
        have heq1 : E y z x z := le_antisymm hle2 hle3
        have heq2 : x = y := narboux_lemma h.symm heq1.lr.symm
        subst heq2; exact btwn_refl

theorem xyz_iff_xy_le_and_yz_le_of_col {G : Geom} {x y z : Point} :
    Col x y z → (B x y z ↔ (le x y x z ∧ le y z x z)) := fun hcol ↦ Iff.intro
        (fun hb ↦ ⟨le_of_btwn_left hb, le_of_btwn_right hb⟩)
        (fun ⟨hl1, hl2⟩ ↦ btwn_of_col_le hcol hl1 hl2)

end Geom
end Ch5
