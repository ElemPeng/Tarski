import Tarski.Ch4
section Satz_5_1
namespace Geom

-- Satz 5.1, due to Gupta (1965); this one is a mess.
theorem xzw_or_xwz_of_ne_xyz_xyw {G : Geom} {x y z w : Point} :
x ≠ y → B x y z → B x y w → (B x z w ∨ B x w z) := by
    intro hxy hxyz hxyw
-- first rule out dumb cases where y = z or w
    by_cases hyz : y = z
    · subst hyz; exact Or.inl hxyw
    by_cases hyw : y = w
    · subst hyw; exact Or.inr hxyz
-- next construct a few segments
    have ⟨z', hz'1, hz'2⟩ := sgmt_const x w z w
    have ⟨w', hw'1, hw'2⟩ := sgmt_const x z z w
    by_cases hzw' : z = w'
    · subst hzw'; have h : z = w := E_id hw'2.symm
      subst h; exact Or.inl (btwn_refl')
    have ⟨y', hy'1, hy'2⟩ := sgmt_const x z' z y
    have ⟨y'', hy''1, hy''2⟩ := sgmt_const x w' w y
-- we now have x y w z' y' and x y z w' y''. Our next goal is to show
-- that because of sgmt_add, yy' ≡ yy'' and hence y' = y''
-- show that yz' ≡ y''z
    have hywz' : B y w z' := yzw_of_xyz_xzw hxyw hz'1
    have hy''w'z : B y'' w' z := (yzw_of_xyz_xzw hw'1 hy''1).symm
    have he1 : E y z' y'' z := sgmt_add hywz' hy''w'z hy''2.lr.symm (E_trans hz'2 hw'2.symm.r)
-- show that yy' ≡ y''y
    have hyz'y' : B y z' y' := yzw_of_xyz_xzw (xyw_of_xyz_yzw_ne hxyw hywz' hyw) hy'1
    have hy''zy : B y'' z y :=
      xzw_of_xyz_yzw_ne hy''w'z (xyz_of_xyw_yzw hw'1.symm hxyz.symm) (Ne.symm hzw')
    have he2 : E y y' y'' y := sgmt_add hyz'y' hy''zy he1 hy'2
-- show that y'' = y'
    have hxyw' : B x y w' := xyw_of_xyz_xzw hxyz hw'1
    have hxyy'' : B x y y'' := xyw_of_xyz_xzw hxyw' hy''1
    have hxyz' : B x y z' := xyw_of_xyz_xzw hxyw hz'1
    have hxyy' : B x y y' := xyw_of_xyz_xzw hxyz' hy'1
    have heq1 : y' = y'' := (unique_sgmt_const hxy hxyy' he2 hxyy'' E_comm)
    subst heq1
-- apply five_sgmt to y z w' z' and  y' z' w z; show w'z' ≡ wz
    have hyzw' : B y z w' := yzw_of_xyz_xzw hxyz hw'1
    have hwz'y' : B w z' y' := yzw_of_xyz_xzw hz'1 hy'1
    have he3 : E w' z' w z :=
      five_sgmt hyz hyzw' hwz'y'.symm hy'2.lr.symm (E_trans hw'2 hz'2.symm.r) he1 E_comm
-- use inner pasch
    have ⟨e, hzez', hwew'⟩ := inner_pasch hyzw'.symm hywz'.symm
-- use inner_five_sgmt to get E e z e z' with w e w' z w e w' z'
    have hezez' : E e z e z' :=
      inner_five_sgmt hwew' hwew' E_refl E_refl hz'2.symm.l (E_trans hw'2.l he3.symm.l)
-- use inner_five_sgmt to get E e w e w' with  z e z' w z e z' w'
    have hewew' : E e w e w' :=
      inner_five_sgmt hzez' hzez' E_refl E_refl hw'2.symm (E_trans hz'2.l he3.symm.lr)
-- if z = z' we're done so assume z ≠ z'. Our goal is now to show w = w'
    by_cases hzz' : z = z'
    · subst hzz'; exact Or.inr hz'1
    suffices hww' : w = w' by (subst hww'; exact Or.inl hw'1)
-- we now construct a triangle zpq congruent to zww' so that
-- r is the midpoint of pq and prq ≡ wew'; it then suffices that p = q
    have ⟨p, hz'zp, he4⟩ := sgmt_const z' z z w'
    have ⟨r, hw'zr, he5⟩ := sgmt_const w' z z e
    have ⟨q, hprq, he6⟩ := sgmt_const p r r p
-- use five_sgmt with B w' z r p and p z e w' to get E r p e w'
    have hrpew' : E r p e w' :=
      five_sgmt (Ne.symm hzw') hw'zr (xyz_of_xyw_yzw hz'zp.symm hzez') he4.lr.symm he5 E_comm he4
    have hrqew : E r q e w := E_trans (E_trans he6 hrpew') hewew'.symm
-- get E w w' p q; then it suffices that p = q
    have hww'pq : E w w' q p := sgmt_add hwew' hprq.symm hrqew.symm.lr hrpew'.symm
    suffices hpq : p = q by (subst hpq; exact E_id hww'pq)
-- rule out w' = e then use five_sgmt with  w' e w z and p r q z
    by_cases hw'e : w' = e
    · subst hw'e; have hpr : p = r := E_id hrpew'.l; subst hpr
      exact E_id he6
    have hwzqz : E w z q z :=
      five_sgmt (hw'e) hwew'.symm hprq hrpew'.symm.lr hrqew.symm he4.symm.lr he5.lr.symm
-- get E z p z q
    have hzpzq : E z p z q := E_trans (E_trans he4 hw'2) hwzqz.lr
-- show r ≠ z
    by_cases hrz : r = z
    · subst hrz; have hre : r = e := E_id he5.symm; subst hre
      have hrz' : r = z' := E_id hezez'.symm; subst hrz'
      exact absurd (rfl) hzz'
-- get E w' p w' q and E y p y q
    have hw'pw'q : E w' p w' q := E_of_ne_col_E hrz (hw'zr).col.xz he6.symm hzpzq
    have hypyq : E y p y q := E_of_ne_col_E hzw' (hyzw').col.l hzpzq hw'pw'q
-- get E y' p y' q, deal with the case y = y', and show E z' p z' q
    have hy'py'q : E y' p y' q := E_of_ne_col_E hzw' (hy''w'z).col.xz hzpzq hw'pw'q
    by_cases hyy' : y = y'
    · subst hyy'; exact absurd (btwn_id hy''zy) hyz
    have hz'pz'q : E z' p z' q := E_of_ne_col_E hyy' (hyz'y').col.yz  hypyq hy'py'q
    have hpppq : E p p p q := E_of_ne_col_E hzz' (hz'zp).col.xy hzpzq hz'pz'q
    exact E_id hpppq.symm

end Geom
end Satz_5_1
