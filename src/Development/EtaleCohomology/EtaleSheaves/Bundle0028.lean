module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0016
public import Development.EtaleCohomology.EtaleSheaves.Bundle0010
public import Development.EtaleCohomology.EtaleSheaves.Bundle0018
public import Development.EtaleCohomology.EtaleSheaves.Bundle0019

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairGPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf LateralTheory.E.LeafUnitPairPf

def IsAct (q : ℕ) (i : ℤ) (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) : Prop :=
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.res g (L U t a b) = L V t (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.map ((res _ (tw q i)).d t (t + 1)) (L U t a b) = L U (t + 1) a (Sec.map ((res _ (tw q i)).d t (t + 1)) b)

def LeafUnitAct : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ L, IsAct q i L ∧
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U), L U t (twGen 0 ζ) b = b

def LeafPairExt : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) L, IsAct q i L →
  ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      ν.mul U 0 t t (zero_add t) (Sec.map (resι _ (tw q 0)) a) b = L U t a b

theorem LeafUnitPairG_of (hact : LeafUnitAct) (hext : LeafPairExt) : LeafUnitPairG := by
  intro q _ i
  obtain ⟨L, hL, hLζ⟩ := hact q i
  obtain ⟨ν, hν⟩ := hext q i L hL
  refine ⟨ν, fun U t ζ b => ?_⟩
  exact (hν U t (twGen 0 ζ) b).trans (hLζ U t ζ b)

end LateralTheory.E.LeafUnitPairGPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfB
section
namespace LateralTheory.E.E4

theorem mem_range_of_isIntegral {k B : Type} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] {x : B} (hx : IsIntegral k x) : x ∈ Set.range (algebraMap k B) := by
  have h : (minpoly k x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx)
  have hm : Polynomial.aeval x (minpoly k x) = 0 := minpoly.aeval k x
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic hx
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h, hq, Polynomial.C_1, one_mul, map_add (f := _),
    Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at hm
  exact ⟨-(minpoly k x).coeff 0, by rw [map_neg]; exact hm.symm⟩

theorem fg_subgroup_mult (n : ℕ) (H : Subgroup (Multiplicative (Fin n → ℤ))) : Group.FG H := by
  have : IsNoetherian ℤ (Additive (Multiplicative (Fin n → ℤ))) :=
    isNoetherian_of_linearEquiv (AddEquiv.additiveMultiplicative (Fin n → ℤ)).symm.toIntLinearEquiv
  rw [Group.fg_iff_subgroup_fg, Subgroup.fg_iff_add_fg]
  have := IsNoetherian.noetherian (R := ℤ) H.toAddSubgroup.toIntSubmodule
  exact (Submodule.fg_iff_addSubgroup_fg _).1 this

def LeafUnitsOrd : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B],
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsFG_of (h : LeafUnitsOrd) : LeafUnitsFG := by
  intro k B _ _ _ _ _ _
  obtain ⟨n, φ, hφ⟩ := h k B
  have hker : φ.ker ≤ (Units.map (algebraMap k B).toMonoidHom).range := by
    intro u hu
    obtain ⟨a, ha⟩ := mem_range_of_isIntegral (hφ u hu)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact u.ne_zero ha.symm
    exact ⟨Units.mk0 a ha0, Units.ext (by simpa using ha)⟩
  have : Group.FG φ.range := fg_subgroup_mult n _
  have : Group.FG (Bˣ ⧸ φ.ker) :=
    Group.fg_of_surjective (f := ((QuotientGroup.quotientKerEquivRange φ).symm : φ.range →* Bˣ ⧸ φ.ker))
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map φ.ker (Units.map (algebraMap k B).toMonoidHom).range (MonoidHom.id _) hker) ?_
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk u, rfl⟩

def LeafUnitsOrdCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem isIntegral_of_isField {k B : Type} [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (hB : IsField B) (x : B) : IsIntegral k x := by
  let _ := hB.toField
  have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  exact Algebra.IsIntegral.isIntegral x

theorem LeafUnitsOrd_of (h : LeafUnitsOrdCurve) : LeafUnitsOrd := by
  intro k B _ _ _ _ _ _
  by_cases hB : IsField B
  · exact ⟨0, 1, fun u _ => isIntegral_of_isField hB _⟩
  · exact h k B hB

theorem LeafUnitsFG_of_curve (h : LeafUnitsOrdCurve) : LeafUnitsFG := LeafUnitsFG_of (LeafUnitsOrd_of h)

def LeafNoetherCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ g : Polynomial k →ₐ[k] B, Function.Injective g ∧ g.Finite

def LeafOrdAtInfinity : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsOrdCurve_of (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsOrdCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨g, hg, hf⟩ := hN k B hB
  exact hV k B g hg hf

theorem LeafUnitsFG_of_leaves (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_curve (LeafUnitsOrdCurve_of hN hV)

end LateralTheory.E.E4
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocEtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.GlobalPf

namespace LateralTheory.E.LocEtPf

lemma et_res {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    Et (X.presheaf.map (homOfLE h).op) := by
  have := (𝟙 X : X ⟶ X).etale_appLE hU hV h
  show (X.presheaf.map (homOfLE h).op).hom.Etale
  convert this using 2
  rfl

theorem LocEt_of : LocEt := by
  intro T X p _ x
  obtain ⟨_, _, V0, hV0, hx0, -, -⟩ := Smooth.exists_isStandardSmooth p x
  have hf : (p.appLE ⊤ V0 (by simp)).hom.Smooth := p.smooth_appLE (isAffineOpen_top _) hV0 _
  have hloc := (RingHom.Smooth.locally_isStandardSmooth hf).span_eq_top
  have hcov := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top V0 _ hloc
  have hx1 : x ∈ (⨆ i ∈ {g : Γ(X, V0) | ((algebraMap Γ(X, V0) (Localization.Away g)).comp
      (p.appLE ⊤ V0 (by simp)).hom).IsStandardSmooth}, X.basicOpen i) := by rw [hcov]; exact hx0
  simp only [TopologicalSpace.Opens.mem_iSup] at hx1
  obtain ⟨t, ht, hxt⟩ := hx1
  have hB := hV0.basicOpen t
  let := hV0.isLocalization_basicOpen t
  let e : Localization.Away t ≃ₐ[Γ(X, V0)] Γ(X, X.basicOpen t) :=
    IsLocalization.algEquiv (Submonoid.powers t) _ _
  have hs : (gam p (X.basicOpen t)).hom.IsStandardSmooth := by
    have h1 := (RingHom.isStandardSmooth_respectsIso.1 _ e.toRingEquiv ht)
    have h2 := RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso T).commRingCatIsoToRingEquiv.symm h1
    have hgam : gam p (X.basicOpen t) = (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V0 (by simp) ≫
        X.presheaf.map (homOfLE (X.basicOpen_le t)).op := by
      simp only [gam]
      congr 1
      exact (Scheme.Hom.appLE_map ..).symm
    have halg : algebraMap Γ(X, V0) Γ(X, X.basicOpen t) = (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom := rfl
    rw [hgam]
    convert h2 using 1
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, halg]
    rfl
  obtain ⟨n, g, hgC, hg⟩ := hs.exists_etale_mvPolynomial
  refine ⟨X.basicOpen t, n, hxt, fun V hV hVU => ?_⟩
  refine ⟨CommRingCat.ofHom g ≫ X.presheaf.map (homOfLE hVU).op, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _ hg (et_res hB hV hVU)
  · ext1
    rw [← Category.assoc]
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [hgC]
    simp only [gam, Scheme.Hom.appLE, ← CommRingCat.hom_comp, Category.assoc, ← Functor.map_comp]
    rfl

end LateralTheory.E.LocEtPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocTensorPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.LocTensorPf

theorem isLocalRing_of_maximal_over_and_power_in_range (Z X B : Type) [CommRing Z] [CommRing X] [CommRing B] [IsLocalRing X] [IsLocalRing B] [Nontrivial Z]
    (u : X →+* Z) (v : B →+* Z)
    (hM : ∀ M : Ideal Z, M.IsMaximal → IsLocalRing.maximalIdeal X ≤ M.comap u ∧ IsLocalRing.maximalIdeal B ≤ M.comap v)
    (hF : ∀ z : Z, ∃ N : ℕ, 0 < N ∧ ∃ y : X,
      z ^ N - u y ∈ Ideal.map u (IsLocalRing.maximalIdeal X) ⊔ Ideal.map v (IsLocalRing.maximalIdeal B)) :
    IsLocalRing Z := by
  have hJ : ∀ M : Ideal Z, M.IsMaximal →
      Ideal.map u (IsLocalRing.maximalIdeal X) ⊔ Ideal.map v (IsLocalRing.maximalIdeal B) ≤ M := by
    intro M hMm
    obtain ⟨h1, h2⟩ := hM M hMm
    exact sup_le (Ideal.map_le_iff_le_comap.mpr h1) (Ideal.map_le_iff_le_comap.mpr h2)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨N, hN, y, hy⟩ := hF z
  by_cases hyu : IsUnit y
  · left
    by_contra hz
    obtain ⟨M, hMm, hzM⟩ := Ideal.exists_le_maximal (Ideal.span {z}) (by
      rwa [Ne, Ideal.span_singleton_eq_top])
    have hzM' : z ∈ M := hzM (Ideal.mem_span_singleton_self z)
    have h1 : z ^ N - u y ∈ M := hJ M hMm hy
    have h2 : z ^ N ∈ M := M.pow_mem_of_mem hzM' N hN
    have h3 : u y ∈ M := by
      have := M.sub_mem h2 h1; simpa using this
    exact hMm.ne_top (M.eq_top_of_isUnit_mem h3 (hyu.map u))
  · right
    by_contra hz
    obtain ⟨M, hMm, hzM⟩ := Ideal.exists_le_maximal (Ideal.span {1 - z}) (by
      rwa [Ne, Ideal.span_singleton_eq_top])
    have hzM' : 1 - z ∈ M := hzM (Ideal.mem_span_singleton_self _)
    have hyM : u y ∈ M := by
      have : y ∈ IsLocalRing.maximalIdeal X := hyu
      exact (hM M hMm).1 this
    have h2 : z ^ N ∈ M := by
      have := M.add_mem (hJ M hMm hy) hyM; simpa using this
    have hz' : z ∈ M := hMm.isPrime.mem_of_pow_mem N h2
    exact hMm.ne_top ((Ideal.eq_top_iff_one M).mpr (by simpa using M.add_mem hzM' hz'))

open IsLocalRing in
theorem maxOver {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z) (hp : IsPushout x b u v)
    [IsLocalRing A] [IsLocalRing X] [IsLocalRing B] (hx : IsLocalHom x.hom) (hb : b.hom.IsIntegral)
    (M : Ideal Z) (hM : M.IsMaximal) :
    maximalIdeal X ≤ M.comap u.hom ∧ maximalIdeal B ≤ M.comap v.hom := by
  have hu : u.hom.IsIntegral := LateralTheory.E.SHTensorPf.intPush hp hb
  have hX : (M.comap u.hom).IsMaximal := by
    let _ := u.hom.toAlgebra
    have : Algebra.IsIntegral X Z := ⟨hu⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal u.hom hu M
  have hXe : M.comap u.hom = maximalIdeal X := IsLocalRing.eq_maximalIdeal hX
  have hw : u.hom.comp x.hom = v.hom.comp b.hom := by
    have := congrArg CommRingCat.Hom.hom hp.w; simpa using this
  have hA : ((M.comap v.hom).comap b.hom) = maximalIdeal A := by
    rw [Ideal.comap_comap, ← hw, ← Ideal.comap_comap, hXe]
    ext a
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff x.hom a)
  have hB : (M.comap v.hom).IsMaximal := by
    let _ := b.hom.toAlgebra
    have : Algebra.IsIntegral A B := ⟨hb⟩
    have : (M.comap v.hom).IsPrime := Ideal.comap_isPrime v.hom M
    have hA' : ((M.comap v.hom).comap (algebraMap A B)).IsMaximal := by
      change ((M.comap v.hom).comap b.hom).IsMaximal
      rw [hA]; exact IsLocalRing.maximalIdeal.isMaximal A
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap b.hom hb (M.comap v.hom) hA'
  exact ⟨hXe.symm.le, (IsLocalRing.eq_maximalIdeal hB).symm.le⟩

open IsLocalRing in
theorem locHom_of_int {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (b : A →+* B)
    (hb : b.IsIntegral) : IsLocalHom b := by
  have hm : ((maximalIdeal B).comap b).IsMaximal := by
    let _ := b.toAlgebra
    have : Algebra.IsIntegral A B := ⟨hb⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal b hb (maximalIdeal B)
  have he := IsLocalRing.eq_maximalIdeal hm
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have : a ∈ (maximalIdeal B).comap b := by rw [he]; exact hna
  exact (IsLocalRing.mem_maximalIdeal _).mp this ha

open IsLocalRing in
theorem resInt {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (b : A →+* B)
    (hb : b.IsIntegral) [IsLocalHom b] : (ResidueField.map b).IsIntegral := by
  intro y
  obtain ⟨y0, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨p, hpm, hp⟩ := hb y0
  have hc : (ResidueField.map b).comp (residue A) = (residue B).comp b := by
    ext a; simp [ResidueField.map_residue]
  refine ⟨p.map (residue A), hpm.map _, ?_⟩
  rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hp, map_zero]

open IsLocalRing in
theorem nontriv {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z) (hp : IsPushout x b u v)
    [IsLocalRing A] [IsLocalRing X] [IsLocalRing B] (hx : IsLocalHom x.hom) (hb : b.hom.IsIntegral) : Nontrivial Z := by
  have : IsLocalHom b.hom := locHom_of_int b.hom hb
  let K := AlgebraicClosure (ResidueField X)
  let e : ResidueField A →+* K := (algebraMap (ResidueField X) K).comp (ResidueField.map x.hom)
  let _ : Algebra (ResidueField A) K := e.toAlgebra
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map b.hom).toAlgebra
  have : Algebra.IsIntegral (ResidueField A) (ResidueField B) := ⟨resInt b.hom hb⟩
  have : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := inferInstance
  let l : ResidueField B →ₐ[ResidueField A] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f : X →+* K := (algebraMap (ResidueField X) K).comp (residue X)
  let g : B →+* K := l.toRingHom.comp (residue B)
  have hw : x ≫ CommRingCat.ofHom f = b ≫ CommRingCat.ofHom g := by
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, f, g]
    rw [← ResidueField.map_residue x.hom, ← ResidueField.map_residue b.hom]
    have := l.commutes (residue A a)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show (ResidueField.map b.hom) (residue A a) = algebraMap (ResidueField A) (ResidueField B) (residue A a) from rfl, this]
    rfl
  let d : Z ⟶ CommRingCat.of K := hp.desc (CommRingCat.ofHom f) (CommRingCat.ofHom g) hw
  exact d.hom.domain_nontrivial

theorem frobAdd {R : Type} [CommRing R] (q n : ℕ) (hq : q = 1 ∨ (q.Prime ∧ (q : R) = 0)) (a b : R) :
    (a + b) ^ (q ^ n) = a ^ (q ^ n) + b ^ (q ^ n) := by
  rcases hq with rfl | ⟨hpr, h0⟩
  · simp
  · rcases subsingleton_or_nontrivial R with hs | hs
    · exact Subsingleton.elim _ _
    · have : Fact q.Prime := ⟨hpr⟩
      have : CharP R q := (CharP.charP_iff_prime_eq_zero hpr).mpr h0
      exact add_pow_char_pow a b q n

theorem gen {A X B Z : CommRingCat.{0}} {x : A ⟶ X} {b : A ⟶ B} {u : X ⟶ Z} {v : B ⟶ Z} (hp : IsPushout x b u v)
    (z : Z) : z ∈ Subring.closure (Set.range u.hom ∪ Set.range v.hom) := by
  set T := Subring.closure (Set.range u.hom ∪ Set.range v.hom)
  let u' : X ⟶ CommRingCat.of T := CommRingCat.ofHom (u.hom.codRestrict T
    (fun y => Subring.subset_closure (Or.inl ⟨y, rfl⟩)))
  let v' : B ⟶ CommRingCat.of T := CommRingCat.ofHom (v.hom.codRestrict T
    (fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)))
  let ι : CommRingCat.of T ⟶ Z := CommRingCat.ofHom T.subtype
  have hw : x ≫ u' = b ≫ v' := by
    ext a
    have := congrArg (fun f => f.hom a) hp.w
    simpa [u', v'] using this
  let s := hp.desc u' v' hw
  have hs : s ≫ ι = 𝟙 Z := by
    apply hp.hom_ext
    · rw [← Category.assoc, hp.inl_desc]; ext y; rfl
    · rw [← Category.assoc, hp.inr_desc]; ext y; rfl
  have : z = ι.hom (s.hom z) := by
    have := congrArg (fun f => f.hom z) hs; simpa using this.symm
  rw [this]; exact (s.hom z).2

open IsLocalRing in
theorem frob {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z) (hp : IsPushout x b u v)
    [IsLocalRing A] [IsLocalRing X] [IsLocalRing B] [IsSepClosed (ResidueField A)]
    (hx : IsLocalHom x.hom) (hb : b.hom.IsIntegral) (z : Z) : ∃ N : ℕ, 0 < N ∧ ∃ y : X,
      z ^ N - u.hom y ∈ Ideal.map u.hom (maximalIdeal X) ⊔ Ideal.map v.hom (maximalIdeal B) := by
  have : IsLocalHom b.hom := locHom_of_int b.hom hb
  set J := Ideal.map u.hom (maximalIdeal X) ⊔ Ideal.map v.hom (maximalIdeal B) with hJ
  have hw : u.hom.comp x.hom = v.hom.comp b.hom := by
    have := congrArg CommRingCat.Hom.hom hp.w; simpa using this
  have hwa : ∀ a, u.hom (x.hom a) = v.hom (b.hom a) := fun a => by
    have := congrArg (fun f => f a) hw; simpa using this
  have huJ : ∀ y ∈ maximalIdeal X, u.hom y ∈ J := fun y hy =>
    Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hy)
  have hvJ : ∀ y ∈ maximalIdeal B, v.hom y ∈ J := fun y hy =>
    Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hy)
  set q := ringExpChar (ResidueField A) with hqdef
  have hexp : ExpChar (ResidueField A) q := ringExpChar.expChar _
  have key : ∀ r : ℕ, ExpChar (ResidueField A) r → r = 1 ∨ (r.Prime ∧ ((r : ℕ) : Z ⧸ J) = 0) := by
    intro q hexp
    rcases hexp with _ | ⟨hpr⟩
    · left; rfl
    · right; refine ⟨hpr, ?_⟩
      have h1 : ((q : A)) ∈ maximalIdeal A := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ q
      have h2 : x.hom (q : A) ∈ maximalIdeal X := map_nonunit x.hom _ h1
      have h3 := huJ _ h2
      rw [map_natCast, map_natCast] at h3
      rw [← map_natCast (Ideal.Quotient.mk J)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have hq := key q hexp
  have hq1 : 0 < q := by rcases hq with h | ⟨h, _⟩; · omega
                         · exact h.pos
  let mk := Ideal.Quotient.mk J
  let P : Z → Prop := fun z => ∃ n : ℕ, ∃ y : X, mk (z ^ (q ^ n)) = mk (u.hom y)
  have lift : ∀ z n k y, mk (z ^ (q ^ n)) = mk (u.hom y) → mk (z ^ (q ^ (n + k))) = mk (u.hom (y ^ (q ^ k))) := by
    intro z n k y h
    rw [pow_add, pow_mul, map_pow, h, ← map_pow, ← map_pow]
  have hadd : ∀ z w, P z → P w → P (z + w) := by
    rintro z w ⟨n, y, hy⟩ ⟨m, y', hy'⟩
    refine ⟨n + m, y ^ (q ^ m) + y' ^ (q ^ n), ?_⟩
    rw [map_pow, map_add (f := _), frobAdd q _ hq, ← map_pow, ← map_pow, lift z n m y hy, add_comm n m,
      lift w m n y' hy', map_add, map_add]
  have hmul : ∀ z w, P z → P w → P (z * w) := by
    rintro z w ⟨n, y, hy⟩ ⟨m, y', hy'⟩
    refine ⟨n + m, y ^ (q ^ m) * y' ^ (q ^ n), ?_⟩
    rw [mul_pow, map_mul, lift z n m y hy, add_comm n m, lift w m n y' hy', map_mul, map_mul]
  have hu : ∀ y, P (u.hom y) := fun y => ⟨0, y, by simp⟩
  have hv : ∀ y, P (v.hom y) := by
    intro y
    let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map b.hom).toAlgebra
    have : Algebra.IsIntegral (ResidueField A) (ResidueField B) := ⟨resInt b.hom hb⟩
    have : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := inferInstance
    have : IsPurelyInseparable (ResidueField A) (ResidueField B) :=
      Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem (ResidueField A) q (residue B y)
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨n, x.hom a, ?_⟩
    have h1 : y ^ (q ^ n) - b.hom a ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ← hc]
      change ResidueField.map b.hom (residue A a) - _ = 0
      rw [ResidueField.map_residue, sub_self]
    have h2 := hvJ _ h1
    rw [map_sub, map_pow, ← hwa] at h2
    exact Ideal.Quotient.eq.mpr h2
  have hz : P z := by
    have hg := gen hp z
    induction hg using Subring.closure_induction with
    | mem w hw' => rcases hw' with ⟨y, rfl⟩ | ⟨y, rfl⟩; exacts [hu y, hv y]
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add _ _ _ _ h1 h2 => exact hadd _ _ h1 h2
    | neg w _ h =>
      have : -w = u.hom (-1) * w := by simp
      rw [this]; exact hmul _ _ (hu _) h
    | mul _ _ _ _ h1 h2 => exact hmul _ _ h1 h2
  obtain ⟨n, y, hy⟩ := hz
  exact ⟨q ^ n, pow_pos hq1 n, y, Ideal.Quotient.eq.mp hy⟩

theorem LocTensor_of : LateralTheory.E.SHTensorPf.LocTensor := by
  intro A X B Z x b u v hp hA hX hx hb hB
  obtain ⟨hAh, hAs⟩ := hA
  obtain ⟨hXh, _⟩ := hX
  have := nontriv x b u v hp hx hb
  exact isLocalRing_of_maximal_over_and_power_in_range Z X B u.hom v.hom (fun M hM => maxOver x b u v hp hx hb M hM) (frob x b u v hp hx hb)

end LateralTheory.E.LocTensorPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocalDescent
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescLocPf

def LocPts (q : ℕ) (i : ℤ) {A Y D : CommRingCat.{0}} (φ : A ⟶ Y) (d : A ⟶ D) : Prop :=
  ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)

def CokLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)

def KerLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → LocPts q i φ c →
    ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
    ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  Function.Injective (pull _ (sch.map (Spec.map φ')) (tw q i) n)

theorem DescLoc_of (hC : CokLoc) (hK : KerLoc) : LateralTheory.E.StalkCut.DescLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD hpts Y' w φ' hpo
  exact ⟨hC hH q i n φ hq P hpush het hlow D d hD hpts Y' w φ' hpo,
    hK hH q i n φ hq P hpush het hlow (fun C c hC' hpC => hC hH q i n φ hq P hpush het hlow C c hC' hpC) D d hD hpts Y' w φ' hpo⟩

end LateralTheory.E.DescLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RelNormPfGlue
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

def ClosedAt {X T : Scheme.{0}} (c : X ⟶ T) (W : T.Opens) : Prop :=
  ∀ b : Γ(X, c ⁻¹ᵁ W), (c.app W).hom.IsIntegralElem b → ∃ a, c.app W a = b

def NormClosed : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], IsIntegral Z →
  ∀ V : g.normalization.Opens, IsAffineOpen V → ∀ b : Γ(Z, g.toNormalization ⁻¹ᵁ V),
    (g.toNormalization.app V).hom.IsIntegralElem b → ∃ a, g.toNormalization.app V a = b

theorem RelNorm_of_closed (hN : NormClosed) : LateralTheory.E.SteinPf.RelNorm := by
  intro Z S g _ _ hZ
  haveI : IsIntegral Z := hZ.1
  refine ⟨g.normalization, g.toNormalization, g.fromNormalization, inferInstance, inferInstance, inferInstance,
    g.toNormalization_fromNormalization, fun V hV hne => ⟨?_, ?_, hN g hZ.1 V hV⟩⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨z, hz⟩ := g.toNormalization.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
    exact ⟨z, hz⟩
  · haveI : IsSchemeTheoreticallyDominant g.toNormalization := .of_isDominant _
    exact g.toNormalization.app_injective V

end LateralTheory.E.RelNormPf
end
end

