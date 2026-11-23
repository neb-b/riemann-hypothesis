module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstOfSqMulTendstoZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj ComplexOrder in
theorem _root_.GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f φ → ∀ T : Over S', ∃ Φ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (Φ x).left = x.left ≫ φ := by
  intro S S' f G G' _ _ φ hφ T
  obtain ⟨hpb, hmul⟩ := hφ
  let toFun : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w])
  let invFun : (Over.mk (T.hom ≫ f) ⟶ G) → (T ⟶ G') := fun y =>
    Over.homMk (hpb.lift y.left T.hom (by simpa using Over.w y)) (hpb.lift_snd _ _ _)
  have hto : ∀ x, (toFun x).left = x.left ≫ φ := fun x => rfl
  refine ⟨{ toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_, map_mul' := ?_ }, hto⟩
  · intro x
    ext1
    refine hpb.hom_ext ?_ ?_
    · exact hpb.lift_fst _ _ _
    · exact (hpb.lift_snd _ _ _).trans (Over.w x).symm
  · intro y
    ext1
    exact hpb.lift_fst _ _ _
  · intro x y
    ext1
    exact (hmul T x y (toFun x) (toFun y) (hto x) (hto y)).symm

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem exists_normalised_polarisation : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : Out.PolAV (Sp R)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A →
    LamEq P.L w (𝟙 P.A) P.L (𝟙 P.A) w' →
    ∃ L' : LB P.A.left, L'.IsLB ∧ Out.Rigidified P.A L' ∧ Out.Sym P.A L' ∧ Out.RelAmple P.A L' ∧ Out.KTriv P.A L' ∧
      LamEq L' (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) ∧ LBIso L' (cubeLB P.A ![𝟙 P.A, w] L') := by
  intro laws R _ _ P w w' hw hw' hs ha
  have : IsCommMonObj P.A := P.isAb.comm
  have hM := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := laws.cube _ P ⟨P.L, rig, hM, hrig⟩ rfl
  have hT : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨c.t, c.isGen⟩
  have ha' : LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] P.L)
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] P.L) := by
    simpa only [LamEq, Category.comp_id] using ha
  obtain ⟨Q, -, e, -, iso⟩ := exists_normalised_bundle laws.globalFns P.isAb hM hT w w' hs ha'
  have hc := fun T : Over (Sp R) => diff₃_ptCls (T := T) hM hT
  have hQ := Q.isLB
  have lam : LamEq Q.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) := iso _ _ _
  refine ⟨Q.L, hQ, ⟨Q.rig, Q.rigGen⟩, fun s => ⟨⊤, trivial, ?_⟩, ?_, kTriv_of_lamEq _ _ _ _ hM hQ lam P.ktriv, lam, ?_⟩
  · have h : HasGen Q.L (K := Fin 2) ![(GrpObj.inv (X := P.A)).left, 𝟙 _] ![1, -1] := by
      rw [e]
      refine hasGen_nested hM _ _ _ _ ?_
      rw [Fin.prod_univ_two]
      show normCls P.L w (GrpObj.inv (X := P.A)).left ^ (1 : ℤ) *
        normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ (-1 : ℤ) = 1
      have e : GrpObj.inv (X := P.A) = (𝟙 P.A)⁻¹ := by simp [Hom.inv_def]
      have e' : (𝟙 P.A)⁻¹ ≫ w = (𝟙 P.A ≫ w)⁻¹ := map_inv (postHom w P.A) _
      rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc P.A), zpow_neg, zpow_one, mul_inv_cancel]
    have h' := h.pull (P.A.hom ⁻¹ᵁ ⊤).ι
    have e₁ : (fun k => (P.A.hom ⁻¹ᵁ ⊤).ι ≫ (![(GrpObj.inv (X := P.A)).left, 𝟙 _] : Fin 2 → _) k) =
        ![(P.A.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : P.A ⟶ P.A).left, (P.A.hom ⁻¹ᵁ ⊤).ι] := by
      funext k
      fin_cases k
      exacts [rfl, Category.comp_id _]
    rw [e₁] at h'
    exact h'
  · have one : ptCls P.L P.A 1 = 1 := by
      have h := (hasGen_iff hM _ _).1 (HasGen.pull (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1)
        ⟨rig, hrig⟩ (toUnit P.A).left)
      rw [Fintype.prod_unique, zpow_one] at h
      exact h
    have two : ptCls P.L P.A (𝟙 P.A * 𝟙 P.A) = ptCls P.L P.A (𝟙 P.A) ^ (4 : ℤ) := by
      have h := (hasGen_iff hM _ _).1 (laws.mulPull _ P 2)
      rw [Fin.prod_univ_two] at h
      have h' : ptCls P.L P.A (𝟙 P.A) ^ (((2 : ℕ) : ℤ) ^ 2) * ptCls P.L P.A (𝟙 P.A ^ 2) ^ (-1 : ℤ) = 1 := h
      rw [zpow_neg, zpow_one, mul_inv_eq_one, pow_two (𝟙 P.A)] at h'
      exact h'.symm
    have sq : LBIso (lbPow Q.L 2) (lbPow P.L 2) := by
      rw [e]
      refine lbIso_nested hM _ _ _ _ _ _ ?_
      refine (Fintype.prod_unique _).trans (Eq.trans ?_ (Fintype.prod_unique _).symm)
      show normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ ((2 : ℕ) : ℤ) = ptCls P.L P.A (𝟙 P.A) ^ ((2 : ℕ) : ℤ)
      rw [normCls_left, zpow_natCast, zpow_natCast, pow_two, Category.id_comp]
      have adj := diff₂_ptCls_adj hM ha' (𝟙 P.A) (𝟙 P.A)
      rw [Category.id_comp, Category.id_comp, diff₂_comm w] at adj
      nth_rewrite 2 [adj]
      rw [← diff₂_mul_right (hc P.A), hs, diff₂, one, two]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one, ofMul_zpow, ofMul_pow]
      abel
    have A₁ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb hM
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₂ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) Q.L 2 two_pos P.isAb P.isAb hQ
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₃ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos P.isAb P.isAb
      (DVR.linComb_isLB _ hM _ _) (show IsFinite (𝟙 P.A.left) from inferInstance)
    exact A₂.2.1.1 (A₃.2.2.2 _ (DVR.linComb_isLB _ hQ _ _) sq.symm (A₁.2.1.2 P.ample))
  · have := (iso P.A (𝟙 P.A) w).symm
    rwa [← e] at this

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldPointOfCountable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_numberField_factor (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    {k₀ A : Type} [Field k₀] [CommRing A] (j : k₀ →+* k) (α : k₀ →+* A) (hα : α.FiniteType)
    (ψ : A →+* ℂ) (hψ : ∀ a, ψ (α a) = (j a : ℂ)) (halg : ∀ c, IsAlgebraic k (ψ c)) :
    ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (ψ₁ : A →+* K₁), FiniteDimensional ℚ K₁ ∧
      ψ₁.comp α = (IntermediateField.inclusion hk).toRingHom.comp j ∧
      (algebraMap K₁ ℂ).comp ψ₁ = ψ := by
  letI := α.toAlgebra
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (self := hα)
  haveI : Finite (ψ '' (t : Set A)) := (t.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (ψ '' (t : Set A))) := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨x, -, rfl⟩
    exact ((halg x).restrictScalars ℚ).isIntegral
  let K₁ : IntermediateField ℚ ℂ := k ⊔ IntermediateField.adjoin ℚ (ψ '' (t : Set A))
  have hk : k ≤ K₁ := le_sup_left
  have hmem : ∀ x, ψ x ∈ K₁ := by
    intro x
    have hx : x ∈ Algebra.adjoin k₀ (t : Set A) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact (le_sup_right : _ ≤ K₁) (IntermediateField.subset_adjoin ℚ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      change ψ (α r) ∈ K₁
      rw [hψ]; exact hk (j r).2
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨K₁, hk, ψ.codRestrict K₁ hmem, IntermediateField.finiteDimensional_sup _ _, ?_, ?_⟩
  · ext a
    exact hψ a
  · rfl

theorem exists_fg_le_range_subset {k : Type} [Field k] [Algebra k ℂ] (R : Subalgebra k ℂ) (hR : R.FG)
    {X : Scheme.{0}} (y : Sp R ⟶ X) (U : X.Opens)
    (hU : (spMap R.val.toRingHom ≫ y) (IsLocalRing.closedPoint ℂ) ∈ U) :
    ∃ (R' : Subalgebra k ℂ) (h : R ≤ R'), R'.FG ∧
      Set.range (spMap (Subalgebra.inclusion h).toRingHom ≫ y) ⊆ (U : Set X) := by
  classical
  let p : PrimeSpectrum R := PrimeSpectrum.comap R.val.toRingHom (IsLocalRing.closedPoint ℂ)
  have hp : p ∈ ((y ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) := hU
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((y ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R))) hp (y ⁻¹ᵁ U).2
  have hr0 : (r : ℂ) ≠ 0 := by
    intro h
    have : r = 0 := Subtype.ext h
    subst this
    exact hr (Ideal.zero_mem _)
  obtain ⟨t, ht⟩ := hR
  have hle : R ≤ Algebra.adjoin k (↑(insert (r : ℂ)⁻¹ t) : Set ℂ) := by
    conv_lhs => rw [← ht]
    exact Algebra.adjoin_mono (by simp)
  refine ⟨_, hle, ⟨_, rfl⟩, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hq : PrimeSpectrum.comap (Subalgebra.inclusion hle).toRingHom q ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    intro h
    have h' : Subalgebra.inclusion hle r ∈ q.asIdeal := h
    have hu : (r : ℂ)⁻¹ ∈ Algebra.adjoin k (↑(insert (r : ℂ)⁻¹ t) : Set ℂ) :=
      Algebra.subset_adjoin (by simp)
    have h1 : Subalgebra.inclusion hle r * ⟨_, hu⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hr0)
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ Ideal.mul_mem_right _ _ h'))
  exact hsub hq

theorem exists_numberField_point_of_countable :
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ), R.FG → ∀ (k₀ : Type) [Field k₀] (j : k₀ →+* k) (X : Scheme.{0}) (s : X ⟶ Sp k₀) [LocallyOfFiniteType s] (y : Sp R ⟶ X), y ≫ s = spMap ((algebraMap k R).comp j) → Set.Countable (Set.range fun ρ : R →ₐ[k] ℂ => spMap ρ.toRingHom ≫ y) →
  ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (y₁ : Sp K₁ ⟶ X), FiniteDimensional ℚ K₁ ∧ y₁ ≫ s = spMap ((IntermediateField.inclusion hk).toRingHom.comp j) ∧ spMap (algebraMap K₁ ℂ) ≫ y₁ = spMap R.val.toRingHom ≫ y := by
  intro k _ R hR k₀ _ j X s _ y hy hc
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => (Spec.map_comp _ _).symm
  have hinj : ∀ {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}, spMap f = spMap g → f = g :=
    fun h => congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((spMap R.val.toRingHom ≫ y) (IsLocalRing.closedPoint ℂ))) isOpen_univ
  obtain ⟨R', hle, hR', hsub⟩ := exists_fg_le_range_subset R hR y U hxU
  have hU' : IsAffineOpen U := hU
  let A : Type := Γ(X, U)
  let i : Sp A ⟶ X := hU'.fromSpec
  haveI : IsOpenImmersion i := hU'.isOpenImmersion_fromSpec
  have hsub' : Set.range (spMap (Subalgebra.inclusion hle).toRingHom ≫ y) ⊆ Set.range i :=
    hsub.trans hU'.range_fromSpec.ge
  obtain ⟨φ, hφ⟩ : ∃ φ : A →+* R', spMap φ ≫ i = spMap (Subalgebra.inclusion hle).toRingHom ≫ y := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i _ hsub')
    exact ⟨φ.hom, (congrArg (· ≫ i) hφ).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨α, hα⟩ : ∃ α : k₀ →+* A, spMap α = i ≫ s := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (i ≫ s)
    exact ⟨α.hom, hα⟩
  have hft : α.FiniteType := by
    have : LocallyOfFiniteType (spMap α) := by rw [hα]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφα : φ.comp α = (Subalgebra.inclusion hle).toRingHom.comp ((algebraMap k R).comp j) := by
    apply hinj
    rw [← hcomp, hα, ← Category.assoc, hφ, Category.assoc, hy, hcomp]
  have hcnt : Set.Countable ((fun ψ : A →+* ℂ => spMap ψ ≫ i) ⁻¹'
      (Set.range fun ρ : R →ₐ[k] ℂ => spMap ρ.toRingHom ≫ y)) :=
    hc.preimage_of_injOn fun a _ b _ h => hinj ((cancel_mono i).1 h)
  have halg : ∀ c, IsAlgebraic k ((R'.val.toRingHom.comp φ) c) := by
    intro c
    refine IsAlgebraic.algHom R'.val (a := φ c) ?_
    refine (specialisation_numberField_and_countable_values k R' hR' (φ c) 1 one_ne_zero).2
      _ (hcnt.image fun ψ => ψ c) fun ρ => ⟨ρ.toRingHom.comp φ, ⟨ρ.comp (Subalgebra.inclusion hle), ?_⟩, rfl⟩
    change spMap (ρ.toRingHom.comp (Subalgebra.inclusion hle).toRingHom) ≫ y = spMap (ρ.toRingHom.comp φ) ≫ i
    rw [← hcomp, ← hcomp, Category.assoc, Category.assoc, hφ]
  obtain ⟨K₁, hk, ψ₁, hfd, h1, h2⟩ := exists_numberField_factor k j α hft (R'.val.toRingHom.comp φ)
    (fun a => congrArg Subtype.val (RingHom.congr_fun hφα a)) halg
  refine ⟨K₁, hk, spMap ψ₁ ≫ i, hfd, ?_, ?_⟩
  · rw [Category.assoc, ← hα, hcomp, h1]
  · rw [← Category.assoc, hcomp, h2, ← hcomp, Category.assoc, hφ, ← Category.assoc, hcomp]
    rfl

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldTorsionPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.TorsionField

theorem exists_field_alg (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (B : Type) [CommRing B] [Algebra k B]
    [Module.Finite k B] : ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (φ : B →ₐ[k] ℂ) (b : B), φ b ∈ k₁ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := B)
  let S : Set ℂ := ⋃ b ∈ s, (minpoly k b).rootSet ℂ
  have hS : S.Finite := s.finite_toSet.biUnion fun b _ => Polynomial.rootSet_finite _ _
  have hint : ∀ b : B, _root_.IsIntegral k b := fun b => Algebra.IsIntegral.isIntegral b
  have hI : ∀ x ∈ S, _root_.IsIntegral k x := fun x hx => by
    simp only [S, Set.mem_iUnion] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ⟨minpoly k b, minpoly.monic (hint b), (Polynomial.mem_rootSet.1 hb).2⟩
  have : Finite S := hS
  have hfd : FiniteDimensional k (IntermediateField.adjoin k S) := IntermediateField.finiteDimensional_adjoin hI
  have hfd' : FiniteDimensional ℚ (IntermediateField.adjoin k S) := Module.Finite.trans k _
  refine ⟨(IntermediateField.adjoin k S).restrictScalars ℚ, hfd', fun x hx => ?_, fun φ b => ?_⟩
  · exact (IntermediateField.adjoin k S).algebraMap_mem ⟨x, hx⟩
  · change φ b ∈ IntermediateField.adjoin k S
    have hb : b ∈ Submodule.span k (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine IntermediateField.subset_adjoin _ _ ?_
      simp only [S, Set.mem_iUnion]
      refine ⟨b, hb, Polynomial.mem_rootSet.2 ⟨minpoly.ne_zero (hint b), ?_⟩⟩
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact IntermediateField.smul_mem _ ha

theorem exists_field_finite (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (Z : Over (Sp k)) [IsFinite Z.hom] :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧
      ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ y : Over.mk (spMap (algebraMap k ℂ)) ⟶ Z,
        ∃ y₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ Z,
          spMap (algebraMap k₂ ℂ) ≫ y₂.left = y.left := by
  have : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let φ : CommRingCat.of k ⟶ Γ(Z.left, ⊤) := Spec.preimage (Z.left.isoSpec.inv ≫ Z.hom)
  have hφ : Spec.map φ = Z.left.isoSpec.inv ≫ Z.hom := Spec.map_preimage _
  have h₁ : φ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  let := φ.hom.toAlgebra
  have : Module.Finite k Γ(Z.left, ⊤) := h₁
  obtain ⟨k₁, hfd, hk, H⟩ := exists_field_alg k Γ(Z.left, ⊤)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ y => ?_⟩
  let y' : Sp ℂ ⟶ Z.left := y.left
  have hy : y' ≫ Z.hom = spMap (algebraMap k ℂ) := Over.w y
  let ψ : Γ(Z.left, ⊤) ⟶ CommRingCat.of ℂ := Spec.preimage (y' ≫ Z.left.isoSpec.hom)
  have hψ : Spec.map ψ = y' ≫ Z.left.isoSpec.hom := Spec.map_preimage _
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap k ℂ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hy]
  have hc' : ∀ c : k, ψ.hom (φ.hom c) = (c : ℂ) := fun c => congrArg (fun f => f.hom c) hc
  let ψa : Γ(Z.left, ⊤) →ₐ[k] ℂ := { ψ.hom with commutes' := hc' }
  let ψ₂ : Γ(Z.left, ⊤) →+* k₂ := ψ.hom.codRestrict k₂ fun b => h₁₂ (H ψa b)
  refine ⟨Over.homMk (spMap ψ₂ ≫ Z.left.isoSpec.inv) ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv) ≫ Z.hom =
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h₂).toRingHom)
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext c
    exact hc' c
  · change Spec.map (CommRingCat.ofHom (algebraMap k₂ ℂ)) ≫ Spec.map (CommRingCat.ofHom ψ₂) ≫ Z.left.isoSpec.inv = y'
    rw [← Category.assoc, ← Spec.map_comp, Iso.comp_inv_eq, ← hψ]
    rfl

end GlobalTheory.TorsionField

namespace GlobalTheory

theorem exists_numberField_torsion_points : Out.Laws → ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (P : Out.PolAV (Sp k)) (n : ℕ), 0 < n → ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ x : Over.mk (spMap (algebraMap k ℂ)) ⟶ P.A, x ^ n = 1 → ∃! x₂ : Over.mk (spMap (IntermediateField.inclusion h₂).toRingHom) ⟶ P.A, spMap (algebraMap k₂ ℂ) ≫ x₂.left = x.left := by
  intro _ k _ P n hn
  have hu : IsUnit (n : Γ(Sp k, ⊤)) := by
    have h : IsUnit (n : k) := (Nat.cast_ne_zero.2 hn.ne').isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨-, hfin, -⟩ := GrpTangent.finiteEtale_mulN_torsion P.A (hG := P.isAb) hu
  obtain ⟨k₁, hfd, hk, H⟩ := TorsionField.exists_field_finite k (torsion P.A n)
  refine ⟨k₁, hfd, hk, fun k₂ h₂ h₁₂ x hx => ?_⟩
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion P.A n x hx
  obtain ⟨y₂, hy₂⟩ := H k₂ h₂ h₁₂ y
  have : Flat (spMap (algebraMap k₂ ℂ)) := inferInstance
  have : Surjective (spMap (algebraMap k₂ ℂ)) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi (spMap (algebraMap k₂ ℂ)) := Flat.epi_of_flat_of_surjective _
  refine existsUnique_of_exists_of_unique ⟨y₂ ≫ torsion.ι P.A n, ?_⟩ fun a b ha hb => ?_
  · rw [← hy, Over.comp_left, Over.comp_left, ← hy₂]
    exact (Category.assoc _ _ _).symm
  · exact Over.OverMorphism.ext ((cancel_epi (spMap (algebraMap k₂ ℂ))).1 (ha.trans hb.symm))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

noncomputable section

namespace GlobalTheory.WeierstrassCurve

theorem fibre_over_scheme {R R' : Type} [CommRing R] [CommRing R'] (W : WeierstrassCurve R) (f : R →+* R')
    {A : Over (Sp R)} {A' : Over (Sp R')} [GrpObj A] [GrpObj A'] {ψ : A.left ⟶ scheme W} [IsIso ψ]
    (hψ : ψ ≫ toSpec W = A.hom) (he : eSec A ≫ ψ = zero W) {v : epsR R ⟶ A}
    {h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h)
    {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap f) φ) {v' : epsR R' ⟶ A'} (hv' : IsVecOver f φ v v') :
    ∃ h' : IsUnimodularSol (W.map ((algebraMap R' (DualNumber R')).comp f)) ![DualNumber.eps, -1, 0],
      IsPullback (φ ≫ ψ) A'.hom (toSpec W) (spMap f) ∧ eSec A' ≫ φ ≫ ψ = spMap f ≫ zero W ∧
      v'.left ≫ φ ≫ ψ = ptHom W ((algebraMap R' (DualNumber R')).comp f) ![DualNumber.eps, -1, 0] h' := by
  have hρ : (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have hP : (Chart.dualMapR f ∘ ![DualNumber.eps, -1, 0]) = ![DualNumber.eps, -1, 0] := by
    ext1 j; fin_cases j
    · ext <;> simp [Chart.dualMapR]
    · simp
    · simp
  have h₁ := h.map_comp (Chart.dualMapR f)
  rw [hρ, hP] at h₁
  refine ⟨h₁, ?_, ?_, ?_⟩
  · exact hφ.1.of_iso (Iso.refl _) (asIso ψ) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [hψ]) (by simp)
  · rw [← Category.assoc, PolBaseChange.eSec_comm hφ, Category.assoc, he]
  · rw [← Category.assoc, hv', Category.assoc, hv]
    exact (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ hρ hP _)

theorem exists_polAV_invariants : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A), P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ (∀ (s' : R →+* ℂ) (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∃ L : PeriodPair, (∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) ∧ s' W.c₄ = 12 * L.g₂ ∧ s' W.c₆ = 216 * L.g₃ ∧ s' W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  intro R _ W hΔ
  obtain ⟨P, ψ, v, hg, hiso, hψ, he, ⟨h, hv⟩, hb⟩ := GlobalTheory.WeierstrassCurve.exists_polAV R W hΔ
  refine ⟨P, v, hg, hb, fun R' _ f P' φ v' hP hv' => ?_, fun s P' φ v' u w hP hv' hd => ?_⟩
  · obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ he hv hP.2.1 hv'
    exact OriginTangent.isLieBasis_eps R W R' f P'.A (φ ≫ ψ) v' h' h1 h2 h3
  · obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W s hψ he hv hP.2.1 hv'
    obtain ⟨hw, x, y, t, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
      _root_.GlobalTheory.UnifCoord.exists_coord_on_line R W s P'.A (φ ≫ ψ) v' h' h1 h2 h3 P'.L P'.g u w hd
    obtain ⟨L, hL⟩ := GlobalTheory.exists_periodPair_of_lattice_in_line P'.g u.Λ w (hP.1.trans hg) hw u.discrete u.full
    have hset : (L.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL
    have key := GlobalTheory.invariants_eq_of_periodic_solution L (W.map s) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
      (fun l hl => hper l ((hL l).1 hl)) (fun z hz => heq z fun e => hz ((hL z).2 e)) ht ht0 ht1 hty hlim
    simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_Δ] at key
    exact ⟨hw, L, hL, key⟩

end GlobalTheory.WeierstrassCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF.KeyArch

theorem pos_of_isArchNorm (hU : ThetaUnifAV) (x : KeyIn ℂ) {nth nη : ℝ} (h : KeyPow.IsArchNorm x nth nη) :
    0 < nth ∧ 0 < nη := by
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  obtain ⟨u', τ, M, a, b, c, -, -, -, -, -, -, -, -, -, -, e⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have p₁ : 0 ≤ nth :=
    h₆ ▸ div_nonneg (MeasureTheory.integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg
  have p₂ : 0 ≤ nη := h₇ ▸ by positivity
  have hne : ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 ≠ 0 := by
    rw [e]; have := Real.pi_pos; positivity
  have q₁ := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have q₂ := right_ne_zero_of_mul hne
  exact ⟨p₁.lt_of_ne' fun h0 => q₁ (by rw [h0]; norm_num), p₂.lt_of_ne' fun h0 => q₂ (by rw [h0]; norm_num)⟩

theorem exists_pos_keyArchAt : ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (σ : K →+* ℂ), ∃ t n : ℝ, 0 < t ∧ 0 < n ∧ ∀ T abelian₂ : MLine K, T.n σ = t → abelian₂.n σ = n → KeyArchAt x T abelian₂ σ := by
  intro hU K _ _ x σ
  obtain ⟨x', hx⟩ := KeyPow.exists_keyPB x σ
  obtain ⟨nth, nη, h⟩ := KeyPow.exists_isArchNorm hU x'
  obtain ⟨p₁, p₂⟩ := pos_of_isArchNorm hU x' h
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨Real.sqrt nth, Real.sqrt nη⁻¹, Real.sqrt_pos.2 p₁, Real.sqrt_pos.2 (inv_pos.2 p₂), fun T abelian₂ hT hL =>
    ⟨x', u, Hm, W, χ, θ, Fd, hx, h₁, h₂, h₃, h₄, h₅, ?_, ?_⟩⟩
  · rw [hT, Real.sq_sqrt p₁.le, h₆]
  · rw [hL, Real.sq_sqrt (inv_pos.2 p₂).le, h₇, inv_div]

end GlobalTheory.LamF.KeyArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomExtDvrOfCardTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem homExtDvr_of_card_torsion : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → HomExtDvr := by
  intro h
  exact homExtDvr_iff.2 (GlobalTheory.existsUnique_hom_extension_semiAbelian_dvr
    (GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion h))

end GlobalTheory.CM
end

