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

theorem Point.sameside.col {G : Geom} {a x y : Point} (h : a.sameside x y) : Col x a y :=
    (col_and_not_os_of_ss h).1

theorem ss_of_col_of_not_os {G : Geom} {x y a : Point} :
    Col x a y → ¬ (B x a y) → a.sameside x y := by
    intro hcol hxay; have ⟨hax, hya⟩ := dist_of_not_btwn hxay
    refine ⟨hax, hya.symm, ?_⟩; unfold Col at hcol
    rw [Or.comm, btwn_symm_iff (y := x)]; exact Or.resolve_left hcol hxay

theorem ss_iff_col_and_not_os {G : Geom} {x y a : Point} :
    a.sameside x y ↔ Col x a y ∧ ¬ (B x a y) :=
    Iff.intro col_and_not_os_of_ss <| fun ⟨h1, h2⟩ ↦ ss_of_col_of_not_os h1 h2

-- Satz 6.5 Reflexivitat
theorem ss_refl {G : Geom} {a x : Point} : x ≠ a → a.sameside x x :=
    fun h ↦ ⟨h, h, Or.inl btwn_refl'⟩

-- Satz 6.6 Symmetrie
theorem ss_symm {G : Geom} {a x y : Point} : a.sameside x y → a.sameside y x :=
    fun ⟨hx, hy, h⟩ ↦ ⟨hy, hx, h.symm⟩

theorem Point.sameside.symm {G : Geom} {a x y : Point} (h : a.sameside x y) :
    a.sameside y x := ss_symm h

-- Satz 6.7 Transitivitat
theorem ss_trans {G : Geom} {a x y z : Point} :
    a.sameside x y → a.sameside y z → a.sameside x z := by
    intro ⟨hx, hy, hxy⟩ ⟨_, hz, hyz⟩; refine ⟨hx, hz, ?_⟩
    rcases hxy with h1 | h1 <;> rcases hyz with h2 | h2
    ·   exact Or.inl (xyw_of_xyz_xzw h1 h2)
    ·   exact xyz_or_xzy_of_xyw_xzw h1 h2
    ·   exact xzw_or_xwz_of_ne_xyz_xyw (hy.symm) h1 h2
    ·   exact Or.inr (xyw_of_xyz_xzw h2 h1)

-- Def 6.8
/- the relation fun x ↦ a.sameside p x is an equivalence relation on the points
different from a; Ray defines its equivalence classes which are halflines
(or Rays)
-/

def Ray {G : Geom} (a p : Point) : PSet G := a.sameside p
-- note : a.sameside p x enforces p ≠ a and x ≠ a
-- IsRay needs to enforce a ≠ p otherwise the empty set is a ray
def IsRay {G : Geom} (K : Point → Prop) : Prop := ∃ a p, a ≠ p ∧ K = Ray a p

-- Def 6.9. Halflines H(ap) H(aq) originating from a are called
-- opposites if B p a q (here Ray a p and Ray a q are opposite rays)

def opprays {G : Geom} {p a q : Point} := a ≠ p ∧ a ≠ q ∧ B p a q

def opprays' {G : Geom} {R1 R2 : PSet G} :=
    ∃ p a q, R1 = Ray a p ∧ R2 = Ray a q ∧ B p a q

/- Satz 6.11 : for every Ray a r and distinct points b and c, there is a unique
   point x on Ray a r so that ax ≡ bc -/

theorem narboux_lemma_ss {G : Geom} {a x y : Point} :
    a.sameside x y → E a x a y → x = y := by
    intro ⟨_, _, hb⟩ he; rcases hb with h | h
    ·   exact narboux_lemma h he
    ·   exact (narboux_lemma h he.symm).symm

theorem ray_sgmt_const {G : Geom} (a r b c : Point) : a ≠ r → b ≠ c →
    ∃ x, x ∈ (Ray a r) ∧ E a x b c := by
    intro har hbc; have ⟨z, hz1, hz2⟩ := sgmt_const' r a
    have ⟨x, hx1, hx2⟩ := sgmt_const z a b c; refine ⟨x, ?_, hx2⟩
    refine ⟨har.symm, (E_id_mt hbc hx2).symm, ?_⟩
    exact yzw_or_ywz_of_ne_xyz_xyw hz2.symm hz1.symm hx1

theorem unique_ray_sgmt_const {G : Geom} {a r b c x y : Point} :
    x ∈ Ray a r → E a x b c → a.sameside r y → E a y b c → x = y := by
    intro hssrx haxbc hssry haybc; have haxay := E_trans haxbc haybc.symm
    have hssxy : a.sameside x y := ss_trans hssrx.symm hssry
    exact narboux_lemma_ss hssxy haxay
/-  Def 6.12 : If z is this point, we also say that z is obtained by laying
    off the segment bc from a in the direction of r—or, more precisely,
    along the ray defined by r (i.e., on H(ar)). (thanks google translate)-/

-- Satz 6.13

theorem baxy_of_ss_le {G : Geom} {a x y : Point} : a.sameside x y → le a x a y → B a x y := by
    intro hss ⟨x', hx'1, hx'2⟩; have hss2 : a.sameside x' y :=
    ⟨E_id_mt hss.1.symm hx'2.symm.l, hss.2.1, Or.inl hx'1⟩
    have hxx' : x = x' := unique_ray_sgmt_const (hss.symm) E_refl hss2.symm hx'2.symm
    exact hxx' ▸ hx'1

theorem le_of_ss_baxy {G : Geom} {a x y : Point} : a.sameside x y → B a x y → le a x a y :=
    fun _ hb ↦ le_of_btwn_left hb

theorem baxy_iff_le_of_ss {G : Geom} {a x y : Point} : a.sameside x y →
    (le a x a y ↔ B a x y) := fun hss ↦ Iff.intro (baxy_of_ss_le hss) (le_of_ss_baxy hss)

/- Def 6.14 : for distinct points p and q define the line pq to be
    the set L(pq) := {x : Col x p q}; with this definition, Line p q = ∅ if p = q
-/

def Line {G : Geom} (p q : Point) : PSet G := fun x ↦ p ≠ q ∧ Col p q x

def IsLine {G : Geom} (L : Point → Prop) : Prop := ∃ p q : Point, p ≠ q ∧ L = Line p q

-- Satz 6.15. The Line pq is the union of the rays formed by p and q from some point a
-- along with the point a itself

theorem ssxy_of_axy_ne {G : Geom} {a x y : Point} : a ≠ x → B a x y → a.sameside x y := by
    intro hax haxy; unfold Point.sameside; refine ⟨hax.symm, ?_, Or.inl haxy⟩
    intro hya; subst hya; exact hax <| btwn_id haxy

theorem ne_of_btwn_ne {G : Geom} {a b c : Point} : a ≠ b → B a b c → a ≠ c :=
    fun h1 h2 h3 ↦ h1 (btwn_id (h3 ▸ h2))

theorem sgmt_mem_trichotomy {G : Geom} {p q x a : Point} :
    p ≠ q → B p a q → B p x q → (a.sameside p x ∨ x = a ∨ a.sameside q x) := by
        intro hpq hpaq hpxq; by_cases hxa : x = a; exact Or.inr <| Or.inl hxa
        simp only [hxa, false_or]; rcases xyz_or_xzy_of_xyw_xzw hpaq hpxq with h | h
        ·   have haxq : B a x q := yzw_of_xyz_xzw h hpxq; apply Or.inr
            have hqa : q ≠ a := (ne_of_btwn_ne (Ne.symm hxa) haxq).symm
            exact ⟨hqa, hxa, Or.inr haxq⟩
        ·   rw [btwn_symm_iff] at h; apply Or.inl
            have hpa : p ≠ a := (ne_of_btwn_ne (Ne.symm hxa) h).symm
            exact ⟨hpa, hxa, Or.inr h⟩

theorem line_of_rays {G : Geom} {a p q : Point} : a ≠ p → a ≠ q → B p a q →
    ∀ x, x ∈ Line p q ↔ ((x ∈ Ray a p) ∨ (x = a) ∨ (x ∈ Ray a q)) := by
    intro hap haq hpaq x; unfold Line Ray; constructor
    ·   intro ⟨hpq, hcol⟩; rcases hcol with h | h | h
        ·   apply Or.inr ∘ Or.inr; have haqx : B a q x := yzw_of_xyz_xzw hpaq h
            exact ssxy_of_axy_ne haq haqx
        ·   exact sgmt_mem_trichotomy hpq hpaq h.symm
        ·   apply Or.inl; have hapx : B a p x := yzw_of_xyz_xzw hpaq.symm h.symm
            exact ssxy_of_axy_ne hap hapx
    ·   intro h; have hpq : p ≠ q := ne_of_btwn_ne hap.symm hpaq
        refine ⟨hpq, ?_⟩; rcases h with ⟨h1, h2, h3⟩ | h1 | ⟨h1, h2, h3⟩
        ·   rcases h3 with h' | h'
            ·   exact (xzw_of_xyz_yzw_ne hpaq.symm h' hap).col.xy
            ·   exact (xyw_of_xyz_xzw h'.symm hpaq).col.yz
        ·   subst h1; exact (hpaq).col.yz
        ·   rcases h3 with h' | h'
            ·   exact (xzw_of_xyz_yzw_ne hpaq h' haq).col
            ·   exact (xzw_of_xyw_yzw hpaq h').col.yz

-- Satz 6.16
/- this is miserable; there has to be a cleaner way to do this lol-/
theorem line_eq {G : Geom} {p q s : Point} :
    s ≠ p → s ∈ Line p q → (Line p q = Line p s) := by
    intro hsp ⟨hpq, hcol1⟩; unfold Line; funext z
    simp only [ne_eq, hpq, not_false_eq_true, true_and, hsp.symm, eq_iff_iff]
    unfold Col at hcol1 ⊢; constructor
    ·   intro hcol2; rcases hcol1 with h1 | h1 | h1 <;> rcases hcol2 with h2 | h2 | h2
        ·   rw [← or_assoc]; apply Or.inl; simp [btwn_symm_iff]
            exact xzw_or_xwz_of_ne_xyz_xyw hpq h1 h2
        ·   symm at h2; apply Or.inr ∘ Or.inl; symm
            exact xyw_of_xyz_xzw h2 h1
        ·   apply Or.inr ∘ Or.inr; exact xyw_of_xyz_yzw_ne h2 h1 hpq
        ·   apply Or.inl; exact xyw_of_xyz_xzw h1.symm h2
        ·   rw [←or_assoc]; apply Or.inl; simp [btwn_symm_iff]
            exact xyz_or_xzy_of_xyw_xzw h1.symm h2.symm
        ·   apply Or.inr ∘ Or.inr; exact xyz_of_xyw_yzw h2 h1.symm
        ·   apply Or.inr ∘ Or.inr; symm
            exact xyw_of_xyz_yzw_ne h1 h2 hpq
        ·   apply Or.inr ∘ Or.inr; symm
            exact xyz_of_xyw_yzw h1 h2.symm
        ·   rw [←or_assoc]; apply Or.inl; simp [btwn_symm_iff]
            exact yzw_or_ywz_of_ne_xyz_xyw hpq.symm h1.symm h2.symm
    ·   intro hcol2; rcases hcol1 with h1 | h1 | h1 <;> rcases hcol2 with h2 | h2 | h2
        ·   apply Or.inl; exact xyw_of_xyz_xzw h1 h2
        ·   rw [←or_assoc]; apply Or.inl; simp [btwn_symm_iff]
            exact xyz_or_xzy_of_xyw_xzw h1 h2.symm
        ·   apply Or.inr ∘ Or.inr; exact xyz_of_xyw_yzw h2 h1
        ·   rw [←or_assoc]; apply Or.inl; simp [btwn_symm_iff]
            exact xzw_or_xwz_of_ne_xyz_xyw hsp.symm h1.symm h2
        ·   apply Or.inr ∘ Or.inl; exact xzw_of_xyw_yzw h1 h2
        ·   apply Or.inr ∘ Or.inr; exact (xzw_of_xyz_yzw_ne h1 h2.symm hsp).symm
        ·   apply Or.inr ∘ Or.inr; symm at h2
            exact xzw_of_xyz_yzw_ne h2 h1 hsp
        ·   apply Or.inr ∘ Or.inr; exact yzw_of_xyz_xzw h2 h1
        ·   symm at h2; rw [←or_assoc]; apply Or.inl; simp [btwn_symm_iff]
            exact yzw_or_ywz_of_ne_xyz_xyw hsp h1 h2

-- Satz 6.17

theorem line_gen_pt_mem {G : Geom} {p q : Point} :
    p ≠ q → p ∈ Line p q ∧ q ∈ Line p q := by
    intro hpq; refine ⟨?_, ?_⟩
    ·   exact ⟨hpq, col_triv_xyx⟩
    ·   exact ⟨hpq, col_triv_xyy⟩

theorem line_symm {G : Geom} {p q : Point} :
    p ≠ q → Line p q = Line q p := by
    intro hpq; unfold Line; simp [hpq, hpq.symm, col_xy_iff]; rfl

@[symm] theorem mem_line_symm {G : Geom} {x p q : Point} : x ∈ Line p q → x ∈ Line q p := by
    intro h; rwa [← (line_symm h.1)]

theorem mem_line_symm_iff {G : Geom} {x p q : Point} : x ∈ Line p q ↔ x ∈ Line q p :=
    Iff.intro (mem_line_symm) (mem_line_symm)

-- Satz 6.18
theorem line_pq_ext {G : Geom} {L : PSet G} {p q : Point} :
    IsLine L → p ≠ q → p ∈ L → q ∈ L → L = Line p q := by
    intro ⟨p', q', _, hL'⟩ hpq hpL hqL; subst hL'
    by_cases hp'p : p' = p
    ·   subst hp'p; exact line_eq (hpq.symm) hqL
    by_cases hq'q : q' = q
    ·   rw [hq'q] at hpL ⊢; rw [(line_symm hpq), (line_symm hpL.1)]
        apply line_eq hpq (mem_line_symm hpL)
    by_cases hq'p : q' = p
    ·   rw [← hq'p] at hp'p ⊢; rw [(line_symm hp'p)]
        apply line_eq (Ne.symm hq'q) (mem_line_symm hqL)
    by_cases hqp' : q = p'
    ·   rw [hqp'] at ⊢; rw [←(line_symm hp'p)]
        exact line_eq (Ne.symm hp'p) hpL
    have h : Line p' q' = Line p' q := line_eq hqp' hqL
    rw [h, (line_symm (Ne.symm hqp')), (line_symm hpq)]
    rw [h, mem_line_symm_iff] at hpL
    exact line_eq hpq hpL

-- Satz 6.19
theorem line_incid {G : Geom} {p q : Point} : p ≠ q →
    ∃ L : PSet G, IsLine L ∧ p ∈ L ∧ q ∈ L :=
    fun hpq ↦ ⟨Line p q, ⟨p, q, hpq, rfl⟩ , line_gen_pt_mem hpq⟩

theorem line_incid_unique {G : Geom} {p q : Point} : p ≠ q → ∀ A B : PSet G,
IsLine A → IsLine B → p ∈ A → p ∈ B → q ∈ A → q ∈ B → A = B :=
    fun hpq _ _ hA hB hpA hpB hqA hqB ↦
        (line_pq_ext hB hpq hpB hqB) ▸ (line_pq_ext hA hpq hpA hqA)





end Geom
end Ch6
