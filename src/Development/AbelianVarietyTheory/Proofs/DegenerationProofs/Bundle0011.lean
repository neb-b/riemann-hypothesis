module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionApplyEqOfIsAlgClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma exists_retraction_of_flat_quasiFinite (V K : Type) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [IsAlgClosed K] [Algebra V K] [IsFractionRing V K] {B : Type}
    [CommRing B] (φ : V →+* B) (hflat : φ.Flat) (hqf : φ.QuasiFinite) (q : Ideal B) [q.IsPrime]
    (hq : q.comap φ = IsLocalRing.maximalIdeal V) :
    ∃ ψ : B →+* V, ψ.comp φ = RingHom.id V ∧ (IsLocalRing.maximalIdeal V).comap ψ = q := by
  letI : Algebra V B := φ.toAlgebra
  haveI : Module.Flat V B := hflat
  haveI : Algebra.QuasiFinite V B := hqf.toAlgebra
  haveI : q.LiesOver (IsLocalRing.maximalIdeal V) := ⟨hq.symm⟩
  obtain ⟨P, hPq, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal V))
    (q := IsLocalRing.maximalIdeal V) q bot_le
  have hPV : P.comap φ = ⊥ := hPl.over.symm
  set κ := P.ResidueField
  have hinj : Function.Injective (algebraMap V κ) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    rw [IsScalarTower.algebraMap_apply V B κ, Ideal.algebraMap_residueField_eq_zero] at hv
    have : v ∈ P.comap φ := hv
    rwa [hPV, Ideal.mem_bot] at this
  letI : Algebra K κ := (IsFractionRing.lift (K := K) hinj).toAlgebra
  haveI : IsScalarTower V K κ := IsScalarTower.of_algebraMap_eq
    (fun v => (IsFractionRing.lift_algebraMap (K := K) hinj v).symm)
  haveI : Algebra.QuasiFinite K κ := Algebra.QuasiFinite.of_restrictScalars V K κ
  haveI : Module.Finite K κ := Module.Finite.of_quasiFinite
  let e : K ≃+* κ := RingEquiv.ofBijective (algebraMap K κ)
    ⟨(algebraMap K κ).injective, IsSepClosed.algebraMap_surjective K κ⟩
  let χ : B →+* K := e.symm.toRingHom.comp (algebraMap B κ)
  have hχφ : ∀ v, χ (φ v) = algebraMap V K v := by
    intro v
    apply e.injective
    simp only [χ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    change algebraMap B κ (algebraMap V B v) = algebraMap K κ (algebraMap V K v)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hχ0 : ∀ b, χ b = 0 → b ∈ q := by
    intro b hb
    apply hPq
    rw [← Ideal.algebraMap_residueField_eq_zero]
    have : e (χ b) = algebraMap B κ b := by simp [χ]
    rw [← this, hb, map_zero]
  have hφq : ∀ v ∈ IsLocalRing.maximalIdeal V, φ v ∈ q := by
    intro v hv
    rw [← hq] at hv
    exact hv
  have hmem : ∀ b, χ b ∈ (algebraMap V K).range := by
    intro b
    rcases ValuationRing.isInteger_or_isInteger V (χ b) with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨v, hv⟩
    by_cases hb0 : χ b = 0
    · exact ⟨0, by rw [hb0, map_zero]⟩
    by_cases hvu : IsUnit v
    · obtain ⟨u, rfl⟩ := hvu
      refine ⟨↑u⁻¹, ?_⟩
      rw [← inv_inv (χ b), ← hv]
      exact map_units_inv (algebraMap V K : V →* K) u
    · exfalso
      have hvm : v ∈ IsLocalRing.maximalIdeal V := hvu
      have h1 : χ (b * φ v - 1) = 0 := by
        rw [map_sub, map_mul, map_one, hχφ, hv, mul_inv_cancel₀ hb0, sub_self]
      have h2 := hχ0 _ h1
      have h3 : b * φ v ∈ q := q.mul_mem_left b (hφq v hvm)
      have h4 := q.sub_mem h3 h2
      rw [sub_sub_cancel] at h4
      exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).mpr h4)
  let j := algebraMap V K
  have hj : Function.Injective j := IsFractionRing.injective V K
  let e₂ : V ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let ψ : B →+* V := e₂.symm.toRingHom.comp (χ.codRestrict j.range hmem)
  have hψ : ∀ b, j (ψ b) = χ b := by
    intro b
    have : e₂ (ψ b) = χ.codRestrict j.range hmem b := by simp [ψ]
    exact congrArg Subtype.val this
  refine ⟨ψ, ?_, ?_⟩
  · ext v
    apply hj
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [hψ, hχφ]
  · ext b
    rw [Ideal.mem_comap]
    constructor
    · intro hb
      have h1 : χ (b - φ (ψ b)) = 0 := by rw [map_sub, hχφ, hψ, sub_self]
      have h2 := hχ0 _ h1
      have h3 := hφq _ hb
      simpa using q.add_mem h2 h3
    · intro hb
      by_contra hn
      have hu : IsUnit (ψ b) := by
        by_contra h
        exact hn h
      obtain ⟨u, hu⟩ := hu
      have h1 : χ (b * φ ↑u⁻¹ - 1) = 0 := by
        rw [map_sub, map_mul, map_one, hχφ, ← hψ, ← hu, ← map_mul, Units.mul_inv, map_one, sub_self]
      have h2 := hχ0 _ h1
      have h3 : b * φ ↑u⁻¹ ∈ q := q.mul_mem_right _ hb
      have h4 := q.sub_mem h3 h2
      rw [sub_sub_cancel] at h4
      exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).mpr h4)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma exists_section_through_closed_fiber_point (V K : Type) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [IsAlgClosed K] [Algebra V K] [IsFractionRing V K]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) [LocallyQuasiFinite f] [Flat f] (x : X)
    (hx : f x = IsLocalRing.closedPoint V) :
    ∃ s : Spec (CommRingCat.of V) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint V) = x := by
  obtain ⟨_, ⟨U, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU₀
  have hg : Spec.map (Spec.preimage (hU.fromSpec ≫ f)) = hU.fromSpec ≫ f := Spec.map_preimage _
  set φ := Spec.preimage (hU.fromSpec ≫ f)
  haveI : Flat hU.fromSpec := inferInstance
  haveI : LocallyQuasiFinite hU.fromSpec := inferInstance
  haveI : Flat (hU.fromSpec ≫ f) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  haveI : LocallyQuasiFinite (hU.fromSpec ≫ f) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  have hflat : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp (hg ▸ inferInstance)
  have hqf : φ.hom.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp (hg ▸ inferInstance)
  have hqx : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf _
  set q := hU.primeIdealOf ⟨x, hxU⟩
  have hq : q.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal V := by
    have h1 : (Spec.map φ) q = IsLocalRing.closedPoint V := by
      rw [hg]
      exact (congrArg f hqx).trans hx
    exact congrArg PrimeSpectrum.asIdeal h1
  obtain ⟨ψ, hψ, hψq⟩ := exists_retraction_of_flat_quasiFinite V K φ.hom hflat hqf q.asIdeal hq
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← Spec.map_comp]
    have : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by ext1; exact hψ
    rw [this, Spec.map_id]
  · have : (Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint V) = q :=
      PrimeSpectrum.ext hψq
    exact (congrArg hU.fromSpec this).trans hqx


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.exists_section_of_quasiFinite_flat :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [IsAlgClosed K]
      [Algebra V K] [IsFractionRing V K] (X : Scheme.{0}) (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [IsSeparated f]
      [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Flat f] (x : X),
      f x = IsLocalRing.closedPoint V →
        ∃ s : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint V) = x := by
  intro V K _ _ _ _ _ _ _ X f _ _ _ _ _ x hx
  exact exists_section_through_closed_fiber_point V K X f x hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueCombOfIndependentSpecialFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SaturatedSections

theorem exists_comb {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    {J : Type} {A : J → Type} [∀ j, CommRing (A j)] (φ : ∀ j, W →+* A j) {ϖ : W}
    (hϖ : Irreducible ϖ) (reg : ∀ j (x : A j), φ j ϖ * x = 0 → x = 0)
    {r : ℕ} (s : Fin r → ∀ j, A j)
    (ind : ∀ (c : Fin r → W) (y : ∀ j, A j), (∀ j, φ j ϖ * y j = ∑ i, φ j (c i) * s i j) →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal W) (n : ℕ) :
    ∀ (t : ∀ j, A j) (c : Fin r → W), (∀ j, φ j (ϖ ^ n) * t j = ∑ i, φ j (c i) * s i j) →
      ∃ d : Fin r → W, (∀ i, c i = ϖ ^ n * d i) ∧ ∀ j, t j = ∑ i, φ j (d i) * s i j := by
  induction n with
  | zero =>
    intro t c h
    exact ⟨c, fun i => by simp, fun j => by simpa using h j⟩
  | succ n ih =>
    intro t c h
    have hc := ind c (fun j => φ j (ϖ ^ n) * t j) (fun j => by
      rw [← h j, pow_succ', map_mul, _root_.mul_assoc])
    rw [hϖ.maximalIdeal_eq] at hc
    choose c' hc' using fun i => Ideal.mem_span_singleton'.1 (hc i)
    obtain ⟨d, hd, hd'⟩ := ih t c' (fun j => by
      rw [← sub_eq_zero]
      apply reg j
      rw [mul_sub, ← _root_.mul_assoc, ← map_mul, ← pow_succ', h j, Finset.mul_sum, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc' i, map_mul]; ring)
    exact ⟨d, fun i => by rw [← hc' i, hd i]; ring, hd'⟩

theorem existsUnique_comb {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    {J : Type} {A : J → Type} [∀ j, CommRing (A j)] (φ : ∀ j, W →+* A j) {ϖ : W}
    (hϖ : Irreducible ϖ) (reg : ∀ j (x : A j), φ j ϖ * x = 0 → x = 0)
    {r : ℕ} (s : Fin r → ∀ j, A j)
    (ind : ∀ (c : Fin r → W) (y : ∀ j, A j), (∀ j, φ j ϖ * y j = ∑ i, φ j (c i) * s i j) →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal W) (t : ∀ j, A j) (a : W) (c : Fin r → W) (ha : a ≠ 0)
    (h : ∀ j, φ j a * t j = ∑ i, φ j (c i) * s i j) :
    ∃! d : Fin r → W, ∀ j, t j = ∑ i, φ j (d i) * s i j := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨d, -, hd⟩ := exists_comb φ hϖ reg s ind n t (fun i => (u⁻¹ : Wˣ) * c i) (fun j => by
    simp only [map_mul, _root_.mul_assoc, ← Finset.mul_sum, ← h j]
    rw [← _root_.mul_assoc (φ j (u⁻¹ : Wˣ)), ← map_mul, Units.inv_mul, map_one,
      _root_.one_mul])
  refine ⟨d, hd, fun d' hd' => ?_⟩
  funext i
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  obtain ⟨e, he, -⟩ := exists_comb φ hϖ reg s ind (m + 1) (fun _ => 0) (fun i => d' i - d i)
    (fun j => by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← hd j, ← hd' j, sub_self,
        MulZeroClass.mul_zero])
  have h1 : ϖ ^ m * (v : W) = ϖ ^ m * (ϖ * e i) := by
    have := he i
    rw [hv] at this
    linear_combination this
  have h2 := mul_left_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ v.isUnit))

noncomputable def cst {W : Type} [CommRing W] {H : Scheme.{0}} (p : H ⟶ Sp W) (U : H.Opens) :
    W →+* Γ(H, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom

theorem cst_eq {W : Type} [CommRing W] {H : Scheme.{0}} (p : H ⟶ Sp W) (U : H.Opens) (a : W) :
    Out.resTop U (Out.scal p a) = cst p U a := rfl


set_option backward.isDefEq.respectTransparency false in
theorem eq_zero_of_cst_mul {W : Type} [CommRing W] [IsDomain W] {H : Scheme.{0}} (p : H ⟶ Sp W)
    [Flat p] (V : H.Opens) {r : W} (hr : r ≠ 0) (a : Γ(H, V)) (h : cst p V r * a = 0) :
    a = 0 := by
  have hr' : (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r ∈ nonZeroDivisors Γ(Sp W, ⊤) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv
    have : IsDomain Γ(Sp W, ⊤) := e.symm.toMulEquiv.isDomain
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hr (e.injective ?_)
    rw [map_zero]; exact h0
  refine H.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV, hVV : V' ≤ V⟩ :=
    H.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  refine ⟨V', hVV, hxV, ?_⟩
  have hf : (p.appLE ⊤ V' le_top).hom.Flat := p.flat_appLE (isAffineOpen_top _) hV' le_top
  letI := (p.appLE ⊤ V' le_top).hom.toAlgebra
  have : Module.Flat Γ(Sp W, ⊤) Γ(H, V') := hf
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(H, V')) hr'
  have h' := congrArg (H.presheaf.map (homOfLE hVV).op) h
  rw [map_mul, map_zero, cst, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map] at h'
  simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h'

theorem not_mem_basicOpen_cst {W : Type} [CommRing W] [IsLocalRing W] {H : Scheme.{0}}
    (p : H ⟶ Sp W) (V : H.Opens) {r : W} (hr : r ∈ IsLocalRing.maximalIdeal W) (x : H)
    (hx : p x = IsLocalRing.closedPoint W) : x ∉ H.basicOpen (cst p V r) := by
  rw [← cst_eq, Out.resTop, Scheme.basicOpen_res, Out.scal, ← Scheme.preimage_basicOpen_top,
    basicOpen_eq_of_affine]
  rintro ⟨-, h⟩
  have h' : p x ∈ PrimeSpectrum.basicOpen r := h
  rw [hx] at h'
  exact h' hr

end GlobalTheory.SaturatedSections


open GlobalTheory.SaturatedSections in
theorem GlobalTheory.existsUnique_comb_of_independent_special_fibre : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (H : Scheme.{0}) (p : H ⟶ Sp W) [Flat p] (M : LB H), M.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec M), (∀ c : Fin r → W, (∀ (j : M.ι) (x : H), x ∈ M.U j → p x = IsLocalRing.closedPoint W → x ∉ H.basicOpen (∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j)) → ∀ i, c i ∈ IsLocalRing.maximalIdeal W) → ∀ t : LB.Sec M, (∃ (a : W) (c : Fin r → W), a ≠ 0 ∧ ∀ j, Out.resTop _ (Out.scal p a) * t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j) → ∃! c : Fin r → W, ∀ j, t.f j = ∑ i, Out.resTop _ (Out.scal p (c i)) * (s i).f j := by
  intro W _ _ _ H p _ M _ r s ind t ⟨a, c, ha, h⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  simp only [cst_eq] at ind h ⊢
  refine existsUnique_comb (A := fun j => Γ(H, M.U j)) (fun j => cst p (M.U j)) hϖ
    (fun j x hx => eq_zero_of_cst_mul p _ hϖ.ne_zero x hx) (fun i j => (s i).f j)
    (fun c y hy => ind c fun j x _ hx => ?_) t.f a c ha h
  rw [← hy j, Scheme.basicOpen_mul]
  exact fun h => not_mem_basicOpen_cst p _ hϖ.not_isUnit x hx h.1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

universe u


open TensorProduct in
theorem ringHom_formallyUnramified_of_comp_faithfullyFlat {A B C : Type*} [CommRing A]
    [CommRing B] [CommRing C] {φ : A →+* B} {β : B →+* C} (hβ : β.FaithfullyFlat)
    (hs : β.FormallySmooth) (hu : β.FormallyUnramified) (h : (β.comp φ).FormallyUnramified) :
    φ.FormallyUnramified := by
  algebraize [φ, β, β.comp φ]
  have : Algebra.FormallyEtale B C :=
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have h1 : Subsingleton (C ⊗[B] Ω[B⁄A]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B C).subsingleton
  exact ⟨(Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right B C).mp h1⟩

theorem faithfullyFlat_stalkMap_of_flat {W X : Scheme.{u}} (g : W ⟶ X) [Flat g] (w : W) :
    (g.stalkMap w).hom.FaithfullyFlat := by
  have h := Flat.stalkMap g w
  algebraize [(g.stalkMap w).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g w)) (W.presheaf.stalk w)) :=
    inferInstanceAs <| IsLocalHom (g.stalkMap w).hom
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem flat_of_comp_of_flat_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X) (u : X ⟶ Y)
    [Flat g] [Surjective g] [Flat (g ≫ u)] : Flat u := by
  refine Flat.of_stalkMap u fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := Flat.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact ringHom_flat_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w) h

theorem formallyUnramified_of_comp_of_etale_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [FormallyUnramified (g ≫ u)] :
    FormallyUnramified u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  refine HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime fun x => ?_
  obtain ⟨w, rfl⟩ := g.surjective x
  have h := FormallyUnramified.stalkMap (g ≫ u) w
  rw [Scheme.Hom.stalkMap_comp] at h
  have hs : (g.stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (g.smoothLocus_eq_top.ge (Set.mem_univ w))
  exact ringHom_formallyUnramified_of_comp_faithfullyFlat (faithfullyFlat_stalkMap_of_flat g w)
    hs (FormallyUnramified.stalkMap g w) h

theorem etale_of_comp_of_etale_of_surjective {W X Y : Scheme.{u}} (g : W ⟶ X)
    (u : X ⟶ Y) [Etale g] [Surjective g] [Etale (g ≫ u)] [LocallyOfFinitePresentation u] :
    Etale u := by
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  have : Flat (g ≫ u) := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale (g ≫ u)›).1
  have := flat_of_comp_of_flat_of_surjective g u
  have := formallyUnramified_of_comp_of_etale_of_surjective g u
  exact Etale.of_formallyUnramified_of_flat u

theorem exists_opens_range_etale_of_comp :
    ∀ (W X Y : Scheme.{0}) (g : W ⟶ X) (u : X ⟶ Y) [Etale g] [Etale (g ≫ u)]
      [LocallyOfFinitePresentation u],
      ∃ V : X.Opens, (V : Set X) = Set.range g ∧ Etale (V.ι ≫ u) := by
  intro W X Y g u _ _ _
  have : Flat g := (Etale.iff_flat_and_formallyUnramified.mp ‹Etale g›).1
  let V : X.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  refine ⟨V, rfl, ?_⟩
  have hr : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; exact subset_rfl
  let g' : W ⟶ V := IsOpenImmersion.lift V.ι g hr
  have hg' : g' ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : Etale (g' ≫ V.ι) := by rw [hg']; infer_instance
  have : Etale g' := Etale.of_comp g' V.ι
  have : Surjective g' := by
    refine ⟨fun v => ?_⟩
    obtain ⟨w, hw⟩ : V.ι v ∈ Set.range g := v.2
    refine ⟨w, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg', hw]
  have : Etale (g' ≫ V.ι ≫ u) := by rw [← Category.assoc, hg']; infer_instance
  exact etale_of_comp_of_etale_of_surjective g' (V.ι ≫ u)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsDominantHomOfVectorOfQuasiFiniteAt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension {R B : Type} [CommRing R]
    [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B] {g : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension g R B] (ψ : MvPolynomial (Fin g) R →ₐ[R] B)
    (hψ : ψ.toRingHom.QuasiFinite) : Function.Injective ψ := by
  have key : FaithfulSMul R B ∧ Algebra.trdeg R B = g := by
    obtain ⟨e, he⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial g R B
    letI : Algebra (MvPolynomial (Fin g) R) B := e.toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin g) R) B := he
    haveI : IsScalarTower R (MvPolynomial (Fin g) R) B :=
      IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
    obtain ⟨_, _⟩ :=
      AffinePoints.faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin g) R) B
    refine ⟨FaithfulSMul.trans R (MvPolynomial (Fin g) R) B, ?_⟩
    rw [trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin g) R) B, MvPolynomial.trdeg_of_isDomain]
    simp
  obtain ⟨_, htr⟩ := key
  let x : Fin g → B := fun i => ψ (MvPolynomial.X i)
  have hx : ψ = MvPolynomial.aeval x := MvPolynomial.aeval_unique ψ
  have hr : ψ.range = Algebra.adjoin R (Set.range x) := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hx]
  have h1 : (algebraMap ψ.range B).QuasiFinite :=
    RingHom.QuasiFinite.of_comp (f := algebraMap ψ.range B) (g := ψ.rangeRestrict.toRingHom) hψ
  rw [RingHom.quasiFinite_algebraMap] at h1
  have h2 : Algebra.IsAlgebraic ψ.range B := isAlgebraic_of_quasiFiniteAt ψ.range B ⊥
  rw [hr] at h2
  have h3 := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite R x (by simp [htr])
  rw [hx]
  exact h3.1

theorem isDominant_of_locallyQuasiFinite_affineSpace {Z : Scheme.{0}} [IsIntegral Z]
    {R B : CommRingCat.{0}} [IsDomain R] [IsDomain B] {g : ℕ} (φ : R ⟶ B)
    (hφ : φ.hom.IsStandardSmoothOfRelativeDimension g) (i : Spec R ⟶ Z) [IsOpenImmersion i]
    (f : Spec B ⟶ 𝔸(Fin g; Z)) [LocallyQuasiFinite f]
    (hf : f ≫ 𝔸(Fin g; Z) ↘ Z = Spec.map φ ≫ i) : IsDominant f := by
  have hp := AffineSpace.isPullback_map (n := Fin g) i
  have : IsOpenImmersion (AffineSpace.map (Fin g) i) :=
    MorphismProperty.of_isPullback hp.flip ‹_›
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    (hp.lift f (Spec.map φ) hf ≫ (AffineSpace.SpecIso (Fin g) R).hom)
  have e : f = Spec.map ψ ≫ (AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i := by
    rw [hψ]; simp
  have e2 : CommRingCat.ofHom MvPolynomial.C ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← AffineSpace.SpecIso_inv_over, Category.assoc, Iso.hom_inv_id_assoc,
      IsPullback.lift_snd]
  have hq : LocallyQuasiFinite (Spec.map ψ) := by
    rw [e] at ‹LocallyQuasiFinite f›
    exact .of_comp _ ((AffineSpace.SpecIso (Fin g) R).inv ≫ AffineSpace.map (Fin g) i)
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at hq
  letI : Algebra R B := φ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  have hinj := injective_of_quasiFinite_of_isStandardSmoothOfRelativeDimension
    (R := R) (B := B) (g := g) { ψ.hom with commutes' := fun r => congr($e2 r) } hq
  have : IsDominant (Spec.map ψ) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (by rw [(RingHom.injective_iff_ker_eq_bot ψ.hom).1 hinj]; exact bot_le)⟩
  have : IsDominant (AffineSpace.map (Fin g) i) :=
    ⟨(AffineSpace.map (Fin g) i).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  rw [e]
  infer_instance

theorem isDominant_homOfVector_of_quasiFiniteAt :
    ∀ (X Z : Scheme.{0}) [IsIntegral X] [IsIntegral Z] (t : X ⟶ Z) [LocallyOfFiniteType t] (g : ℕ) (U : X.Opens), (U : Set X).Nonempty → SmoothOfRelativeDimension g (U.ι ≫ t) → ∀ (u : Fin g → Γ(X, ⊤)) (w : X), (AffineSpace.homOfVector t u).QuasiFiniteAt w → IsDominant (AffineSpace.homOfVector t u) := by
  intro X Z _ _ t _ g U hU hs u w hw
  have hf := AffineSpace.homOfVector_over t u
  generalize AffineSpace.homOfVector t u = f at hf hw
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ 𝔸(Fin g; Z) ↘ Z) := by rw [hf]; infer_instance
    exact locallyOfFiniteType_of_comp f (𝔸(Fin g; Z) ↘ Z)
  obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.isOpen f.quasiFiniteLocus.isOpen hU
    ⟨w, hw⟩
  let W : X.Opens := U ⊓ f.quasiFiniteLocus
  have h1 : SmoothOfRelativeDimension (0 + g) (X.homOfLE (inf_le_left : W ≤ U) ≫ U.ι ≫ t) :=
    inferInstance
  have h2 : LocallyQuasiFinite (X.homOfLE (inf_le_right : W ≤ f.quasiFiniteLocus) ≫
    f.quasiFiniteLocus.ι ≫ f) := inferInstance
  rw [Scheme.homOfLE_ι_assoc] at h1 h2
  rw [zero_add] at h1
  obtain ⟨Z', hZ', V, hV, hx, e, hsm⟩ := h1.exists_isStandardSmoothOfRelativeDimension ⟨x, hxU, hxV⟩
  have : Nonempty W := ⟨⟨x, hxU, hxV⟩⟩
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  have : Nonempty Z' := ⟨⟨_, e hx⟩⟩
  have : IsDominant (hV.fromSpec ≫ W.ι ≫ f) :=
    isDominant_of_locallyQuasiFinite_affineSpace _ hsm hZ'.fromSpec _ (by
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ hZ' hV e]; simp [hf, W])
  have : IsDominant (W.ι ≫ f) := .of_comp hV.fromSpec _
  exact .of_comp W.ι _

end GlobalTheory
end

