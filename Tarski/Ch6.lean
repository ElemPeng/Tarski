import Tarski.Ch5
section Ch6
namespace Geom

-- sameside x y z means ray x y = ray x z and neither y nor z = x
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

theorem exists_os_iff_ss {G : Geom} {x y a : Point} : x ≠ a → y ≠ a →
    ((∃ z, z ≠ a ∧ B x a z ∧ B y a z) ↔ a.sameside x y) := by
    intro h1 h2; constructor
    · exact ss_of_exists_os h1 h2
    · exact exists_os_of_ss
-- Satz 6.4

end Geom
end Ch6
