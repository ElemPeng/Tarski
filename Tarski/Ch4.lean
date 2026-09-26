import Tarski.Ch23

section Ch4
namespace Geom
/-
    Notes about Chapter 4: There is a function called insert: What it is doing is
    given a ray a'c', constructing a point b' on it so that ab ≡ a'b'.
    further (a, b, c) ≃ (a', b', c') or E3 (a, b, c, a', b', c') is shorthand for
    ab ≡ a'b' ∧ bc ≡ b'c' ∧ ac ≡ a'c'.

    AFS is shorthand for "the premises of the five segment axiom"
    IFS is shorthand for "the premises of the inner five segment theorem (Satz 4.1)"

-/

-- Satz 4.2; this is basically SSS to five_sgmt's SAS
/- This is actually very clever so I feel the need to explain it: The way it works is
we know xz = x'z', xu=x'u' and zu = z'u' so we construct w and w' so that B xzw and
B x'z'w', use five_sgmt to get wu = w'u', and then use it again backwards on the
triangles w y u and w' y' u' to get yu = y'u'.-/
theorem inner_five_sgmt {G : Geom} {x y z u x' y' z' u' : Point} : B x y z → B x' y' z' →
    E x y x' y' → E y z y' z' → E x u x' u' → E z u z' u' → E y u y' u' := by
    intro hb1 hb'1 he1 he2 he3 he4
    by_cases heq : x = z
    ·   subst heq; rw [btwn_id hb1] at he1 he3; rwa [E_id he1.symm] at he3
    have ⟨w, hw1, heq2⟩ := sgmt_const' x z
    have ⟨w', hw'1, he6⟩ := sgmt_const x' z' z w
    have he5 : E x z x' z' := sgmt_add hb1 hb'1 he1 he2
    have he7 : E w u w' u' := five_sgmt heq hw1 hw'1 he5 he6.symm he3 he4
    have hb2 : B w z y := (yzw_of_xyz_xzw hb1 hw1).symm
    have hb'2 : B w' z' y' := (yzw_of_xyz_xzw hb'1 hw'1).symm
    apply five_sgmt heq2.symm hb2 hb'2 he6.lr.symm he2.lr he7 he4

-- Satz 4.3: segment subtraction
/-  Same trick as above; if y = z we're done, so assume y ≠ z and extend ray yz
    and ray y'z' to w and w', then use five_sgmt with w z y x and w' z' y' x' -/

theorem sgmt_sub {G : Geom} {x y z x' y' z' : Point} : B x y z → B x' y' z' →
    E x z x' z' → E y z y' z' → E x y x' y' := by
    intro hb1 hb'1 he1 he2; by_cases heq : y = z
    · subst heq; exact (E_id he2.symm) ▸ he1
    have heq' : y' ≠ z' := E_id_mt heq he2.symm
    have ⟨w, hb2, heq2⟩ := sgmt_const' y z
    have ⟨w', hb'2, he3⟩ := sgmt_const y' z' z w
    rw [E_symm_iff] at he3
    have hb3 : B x z w := xzw_of_xyz_yzw_ne hb1 hb2 heq
    have hb'3 : B x' z' w' := xzw_of_xyz_yzw_ne hb'1 hb'2 heq'
    have he4 : E x w x' w' := sgmt_add hb3 hb'3 he1 he3
    rw [btwn_symm_iff] at hb2 hb'2
    rw [E_flip_both_iff] at he1 he2 he3 he4 ⊢
    apply five_sgmt heq2.symm hb2 hb'2 he3 he2 he4 he1


-- this is definition 4.3 in Beeson (basically side side side premises?)
def E3 {G : Geom} (x y z a b c : Point) := E x y a b ∧ E y z b c ∧ E x z a c

-- Satz 4.5
/-  if ac ≡ a'c' and B a b c there is some b' so that B a' b' c'
    and ab ≡ a'b' and bc ≡ b'c'; 4.6 shows that you don't need to know what c is
    to construct b' but this is not interesting to me; Beeson uses a function
    E3 here to capture all the congruences but I think this way is easier in
    Lean-/
theorem sgmt_split {G : Geom} {a b c a' c' : Point} : B a b c → E a c a' c' →
    (∃ b', B a' b' c' ∧ E a b a' b' ∧ E b c b' c') := by
        intro hb1 he1; have ⟨w', hb'2, heq2⟩ := sgmt_const' c' a'
        have ⟨w, hb2, he2⟩ := sgmt_const c a a' w'
        have ⟨b', hb'3, he3⟩ := sgmt_const w' a' a b
        have ⟨c'', hb'4, he4⟩ := sgmt_const w' b' b c
        have hb'5 : B a' b' c'' := yzw_of_xyz_xzw hb'3 hb'4
        have he5 : E a c a' c'' := sgmt_add hb1 hb'5 he3.symm he4.symm
        have he6 : E a' c' a' c'' := E_eucl he1 he5
        have hb'6 : B w' a' c'' := xyw_of_xyz_xzw hb'3 hb'4
        have heq3 : c' = c'' :=
            unique_sgmt_const heq2.symm hb'2.symm (E_refl) hb'6 he6.symm
        subst heq3; exact ⟨b', hb'5, he3.symm, he4.symm⟩

-- Satz 4.6; basically a uniqueness result for Satz 4.5 (misstated on the website)
theorem btwn_of_btwn_e3 {G : Geom} {x y z x' y' z' : Point} :
    B x y z → E3 x y z x' y' z' → B x' y' z' := by
    intro hb ⟨he1, he2, he3⟩; have ⟨z'', hz'1, hz'2⟩ := sgmt_const x' y' y z
    by_cases h : x' = y'
    · subst h; exact btwn_refl
    have h' : E z'' z' z z := five_sgmt h hz'1 hb he1.symm hz'2 he3.symm he2.symm
    exact (E_id h')▸ hz'1

-- this is definition 4.10 in Beeson
def Col {G : Geom} (x y z : Point) := B x y z ∨ B y z x ∨ B z x y

-- Satz 4.11 : Collinear is symmetric in all of its inputs
theorem Col.xy {G : Geom} {x y z : Point} (h : Col x y z) : Col y x z := by
    unfold Col at h ⊢; rcases h with h' | h' | h'
    ·   exact Or.inr <| Or.inr h'.symm
    ·   exact Or.inr <| Or.inl h'.symm
    ·   exact Or.inl h'.symm

theorem Col.xz {G : Geom} {x y z : Point} (h : Col x y z) : Col z y x := by
    unfold Col at h ⊢; rcases h with h' | h' | h'
    ·   exact Or.inl h'.symm
    ·   exact Or.inr <| Or.inr h'.symm
    ·   exact Or.inr <| Or.inl h'.symm

theorem Col.yz {G : Geom} {x y z : Point} (h : Col x y z) : Col x z y := h.xz.xy.xz

theorem Col.l {G : Geom} {x y z : Point} {h : Col x y z} : Col y z x := h.xy.yz

theorem Col.r {G : Geom} {x y z : Point} {h : Col x y z} : Col z x y := h.xz.yz

theorem col_xy_iff {G : Geom} {x y z : Point} : Col x y z ↔ Col y x z := by
    constructor; all_goals exact fun x ↦ x.xy

theorem col_xz_iff {G : Geom} {x y z : Point} : Col x y z ↔ Col z y x := by
    constructor; all_goals exact fun x ↦ x.xz

theorem col_yz_iff {G : Geom} {x y z : Point} : Col x y z ↔ Col x z y := by
    constructor; all_goals exact fun x ↦ x.yz

theorem col_shift_iff {G : Geom} {x y z : Point} : Col x y z ↔ Col y z x := by
    constructor; exact fun x ↦ x.l; exact fun x ↦ x.r

-- Satz 4.12ab
theorem col_triv_xxy {G : Geom} {x y : Point} : Col x x y := by
    unfold Col; exact Or.inl (btwn_refl)

theorem col_triv_xyx {G : Geom} {x y : Point} : Col x y x := by
    unfold Col; exact Or.inr (Or.inr btwn_refl)

-- Satz 4.14
theorem col_of_col_e3 {G : Geom} {x y z x' y' z' : Point} :
    Col x y z → E3 x y z x' y' z' → Col x' y' z' := by
    intro hcol ⟨he1, he2, he3⟩; rcases hcol with h' | h' | h'
    ·   apply Or.inl; exact btwn_of_btwn_e3 h' ⟨he1, he2, he3⟩
    ·   apply Or.inr; apply Or.inl; exact btwn_of_btwn_e3 h' ⟨he2, he3.lr, he1.lr⟩
    ·   apply Or.inr; apply Or.inr; exact btwn_of_btwn_e3 h' ⟨he3.lr, he1, he2.lr⟩

-- Satz 4.15
theorem e3_of_col_eq {G : Geom} {x y z x' y' : Point} : Col x y z → E x y x' y' →
    ∃ z', E3 x y z x' y' z' := by
    intro hcol he1; rcases hcol with h' | h' | h'
    ·   have ⟨z', hb'1, he2⟩ := sgmt_const x' y' y z; rw [E_symm_iff] at he2
        have he3 : E x z x' z' := sgmt_add h' hb'1 he1 he2
        exact ⟨z', he1, he2, he3⟩
    ·   have ⟨z', hb'1, he2, he3⟩ := sgmt_split h' he1.lr
        exact ⟨z', he1, he2, he3.lr⟩
    ·   have ⟨z', hb'1, he2⟩ := sgmt_const y' x' x z
        have he3 := sgmt_add h' hb'1.symm he2.lr.symm he1
        exact ⟨z', he1, he3.lr, he2.symm⟩

-- Satz 4.16 (I thought this was pretty straightforward)
theorem sgmt_extend {G : Geom} {x y z w x' y' z' w' : Point} :
x ≠ y → Col x y z → E3 x y z x' y' z' → E x w x' w' → E y w y' w' → E z w z' w' := by
    intro hne1 hcol ⟨he1, he2, he3⟩ he4 he5
    rcases hcol with hb1 | hb1 | hb1
    ·   have hb'1 := btwn_of_btwn_e3 hb1 ⟨he1, he2, he3⟩
        exact five_sgmt hne1 hb1 hb'1 he1 he2 he4 he5
    ·   have hb'1 := btwn_of_btwn_e3 hb1 ⟨he2, he3.lr, he1.lr⟩
        exact inner_five_sgmt hb1 hb'1 he2 he3.lr he5 he4
    ·   have hb'1 := btwn_of_btwn_e3 hb1 ⟨he3.lr, he1, he2.lr⟩
        exact five_sgmt hne1.symm hb1.symm hb'1.symm he1.lr he3 he5 he4

theorem e3_triv {G : Geom} (x y z : Point) : E3 x y z x y z := ⟨E_refl, E_refl, E_refl⟩

-- Satz 4.17; a converse of hi_dim
theorem E_of_ne_col_E {G : Geom} {x y z u v : Point} : x ≠ y → Col x y z →
    E x u x v → E y u y v → E z u z v :=
    fun hne1 hcol he1 he2 ↦ sgmt_extend hne1 hcol (e3_triv x y z) he1 he2

-- Satz 4.18
theorem eq_of_ne_col_E {G : Geom} {x y z z' : Point} : x ≠ y →
Col x y z → E x z x z' → E y z y z' → z = z' :=
    fun hne hcol he1 he2 ↦ E_id (E_of_ne_col_E hne hcol he1 he2).symm

-- Satz 4.19
theorem eq_of_btwn_E {G : Geom} {x y z z' : Point} : B x z y → E x z x z' →
E y z y z' → z = z' := by
    intro hb he1 he2; by_cases heq : x = y
    ·   subst heq; have heq2 : x = z := btwn_id hb
        subst heq2; exact E_id he2.symm
    ·   have hcol : Col x y z := Or.inr <| Or.inl hb.symm
        exact eq_of_ne_col_E heq hcol he1 he2

end Geom
end Ch4
