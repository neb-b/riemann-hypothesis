module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceIsPrimeOfOfHeightOneNormalLocalModel
section
open GlobalTheory GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem exists_place_isPrimeOf_of_height_eq_one {K : Type} [Field K] (cK : ℂ →+* K)
    (R : Subring K) (hR : IsLocModel cK R) (hic : IsIntegrallyClosed R) (p : Ideal R)
    (hpp : p.IsPrime) (hp : p.height = 1) :
    ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ g ∉ p) := by
  classical
  letI : Algebra ℂ R := (cK.codRestrict R hR.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  set S := primeLocalSubalgebra K p with hS
  have hmem : ∀ x : K, x ∈ S ↔ ∃ s : R, s ∉ p ∧ ∃ a : R, (a : K) = s * x := by
    intro x
    rw [hS, mem_primeLocalSubalgebra_iff]
    rfl
  have hne : ∀ s : R, s ∉ p → (s : K) ≠ 0 := fun s hs h =>
    hs ((Subtype.ext h : s = 0) ▸ p.zero_mem)
  have h1p : (1 : R) ∉ p := (Ideal.ne_top_iff_one p).mp hpp.ne_top
  have hRS : ∀ r : R, (r : K) ∈ S := fun r =>
    (hmem _).2 ⟨1, h1p, r, by simp⟩
  have hinv : ∀ s : R, s ∉ p → (s : K)⁻¹ ∈ S := fun s hs =>
    (hmem _).2 ⟨s, hs, 1, by simp [mul_inv_cancel₀ (hne s hs)]⟩
  have hor : ∀ x : K, x ∈ S ∨ x⁻¹ ∈ S := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ S.zero_mem)
    rw [mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp hx,
      mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp (inv_ne_zero hx),
      heightOneOrd_vw_inv]
    omega
  let V : ValuationSubring K := { S.toSubring with mem_or_inv_mem' := hor }
  have hV : ∀ x : K, x ∈ V ↔ x ∈ S := fun _ => Iff.rfl
  let ι : R →+* V :=
    { toFun := fun r => ⟨r, hRS r⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra R V := ι.toAlgebra
  have hunit : ∀ s : R, s ∉ p → IsUnit (algebraMap R V s) := fun s hs =>
    isUnit_iff_exists_inv.mpr ⟨⟨(s : K)⁻¹, hinv s hs⟩, Subtype.ext (mul_inv_cancel₀ (hne s hs))⟩
  haveI hloc : IsLocalization.AtPrime V p := by
    refine ⟨fun y => hunit y y.2, fun z => ?_, fun {x y} h => ?_⟩
    · obtain ⟨s, hs, a, e⟩ := (hmem z).1 z.2
      refine ⟨(a, ⟨s, hs⟩), Subtype.ext ?_⟩
      show (z : K) * s = a
      rw [e, mul_comm]
    · refine ⟨1, ?_⟩
      have hxy : (x : K) = y := congrArg (fun z : V => (z : K)) h
      have : x = y := Subtype.ext hxy
      rw [this]
  haveI : IsDiscreteValuationRing V := isDiscreteValuationRing_of_height_eq_one p hp V
  have hc : ∀ a, cK a ∈ V := fun a => hRS ⟨cK a, hR.const_mem a⟩
  have hess : (cK.codRestrict V hc).EssFiniteType := by
    have h0 : (cK.codRestrict R hR.const_mem).EssFiniteType := hR.essFiniteType
    have h1 : (algebraMap R V).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization V p.primeCompl)
    convert h0.comp h1 using 1
    exact RingHom.ext fun _ => rfl
  let P0 : Place cK := ⟨V, hc, inferInstance, hess⟩
  refine ⟨P0, ⟨fun f hf => hRS ⟨f, hf⟩, fun f hf => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨s, hs, a, e⟩ := (hmem f).1 hf
    refine ⟨a, a.2, s, s.2, hne s hs, P0.ord_eq_zero (u := algebraMap R V s) (hunit s hs), ?_⟩
    rw [e, mul_comm]
  · have hg0 : (g : K) ≠ 0 := fun h => hg (Subtype.ext h)
    constructor
    · intro h hgp
      have h' : 0 ≤ P0.ord (g : K)⁻¹ := by rw [P0.ord_inv, h]; rfl
      obtain ⟨s, hs, a, e⟩ := (hmem _).1 ((P0.ord_nonneg_iff (inv_ne_zero hg0)).1 h')
      have : s = a * g := Subtype.ext (by
        show (s : K) = a * g
        rw [e, mul_assoc, inv_mul_cancel₀ hg0, mul_one])
      exact hs (this ▸ p.mul_mem_left a hgp)
    · intro hgp
      exact P0.ord_eq_zero (u := algebraMap R V g) (hunit g hgp)

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMongeAmpereMassAddZsmul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.MongeAmperePoly

variable {X : Type} [TopologicalSpace X]

theorem update_comp_swap {e : ℕ} (Φ : Fin (e + 1) → LocPot X) (i : Fin (e + 1)) (P : LocPot X) :
    Function.update Φ i P ∘ Equiv.swap 0 i =
      (Fin.cons P (fun k => Φ (Equiv.swap 0 i k.succ)) : Fin (e + 1) → LocPot X) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · have h : Equiv.swap 0 i k.succ ≠ i := by
      intro h
      have h2 : Equiv.swap 0 i k.succ = Equiv.swap 0 i 0 := by rw [h, Equiv.swap_apply_left]
      exact Fin.succ_ne_zero k ((Equiv.swap 0 i).injective h2)
    simp [Function.update_of_ne h]

theorem mInt_update_add_zsmul [CompactSpace X] [T2Space X] {e : ℕ} (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (i : Fin e) (P Q : LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (m : ℤ) :
    mInt A (Function.update Φ i (P + Q.zsmul m)) (fun _ => 1) =
      mInt A (Function.update Φ i P) (fun _ => 1) +
        m * mInt A (Function.update Φ i Q) (fun _ => 1) := by
  cases e with
  | zero => exact i.elim0
  | succ e =>
    have key : ∀ R : LocPot X, mInt A (Function.update Φ i R) (fun _ => 1) =
        mInt A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1) := by
      intro R
      rw [← update_comp_swap, mIntSymm]
    have hT : ∀ k : Fin e, IsPotential A (Φ (Equiv.swap 0 i k.succ)) := fun k => hΦ _
    have hI : ∀ R : LocPot X, IsPotential A R →
        MIntegrable A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1) := by
      intro R hR
      refine mIntegrableCont A _ (fun k => ?_) _ continuous_const
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hR
      · simpa using hT k
    have hQm := isPotentialZsmul A m Q hQ
    rw [key, key, key, mIntAdd A P _ _ hP hQm hT _ (hI _ hP) (hI _ hQm),
      mIntZsmul A m Q _ hQ hT]

theorem exists_poly_finset [CompactSpace X] [T2Space X] {e : ℕ} (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Finset (Fin e)) :
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ,
      mInt A (fun i => if i ∈ S then Φ i + (Ψ i).zsmul m else Φ i) (fun _ => 1) =
        P.eval (m : ℝ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro Φ _
    exact ⟨Polynomial.C (mInt A Φ (fun _ => 1)), fun m => by simp⟩
  | insert a S ha ih =>
    intro Φ hΦ
    have hΦ' : ∀ i, IsPotential A (Function.update Φ a (Ψ a) i) := by
      intro i
      by_cases h : i = a
      · subst h; simpa using hΨ i
      · simpa [Function.update_of_ne h] using hΦ i
    obtain ⟨P₁, h₁⟩ := ih Φ hΦ
    obtain ⟨P₂, h₂⟩ := ih _ hΦ'
    refine ⟨P₁ + Polynomial.X * P₂, fun m => ?_⟩
    set F : Fin e → LocPot X := fun i => if i ∈ S then Φ i + (Ψ i).zsmul m else Φ i with hF
    have hFp : ∀ i, IsPotential A (F i) := by
      intro i
      by_cases h : i ∈ S
      · simpa [hF, h] using isPotentialAdd A _ _ (hΦ i) (isPotentialZsmul A m _ (hΨ i))
      · simpa [hF, h] using hΦ i
    have e0 : (fun i => if i ∈ insert a S then Φ i + (Ψ i).zsmul m else Φ i) =
        Function.update F a (Φ a + (Ψ a).zsmul m) := by
      funext i
      by_cases h : i = a
      · subst h; simp
      · simp [hF, Function.update_of_ne h, h]
    have e1 : Function.update F a (Φ a) = F := by
      funext i
      by_cases h : i = a
      · subst h; simp [hF, ha]
      · simp [Function.update_of_ne h]
    have e2 : Function.update F a (Ψ a) = fun i => if i ∈ S then
        Function.update Φ a (Ψ a) i + (Ψ i).zsmul m else Function.update Φ a (Ψ a) i := by
      funext i
      by_cases h : i = a
      · subst h; simp [ha]
      · simp [hF, Function.update_of_ne h]
    rw [e0, mInt_update_add_zsmul A F hFp a _ _ (hΦ a) (hΨ a), e1, e2, h₂ m]
    have := h₁ m
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    rw [← this]

theorem mInt_add_zsmul_poly : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    (∀ i, IsPotential A (Ψ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ,
      mInt A (fun i => Φ i + (Ψ i).zsmul m) (fun _ => 1) = P.eval (m : ℝ) := by
  intro e X _ _ _ A Φ Ψ hΦ hΨ
  obtain ⟨P, hP⟩ := exists_poly_finset A Ψ hΨ Finset.univ Φ hΦ
  exact ⟨P, fun m => by simpa using hP m⟩

end GlobalTheory.MongeAmperePoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMultilinear
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.SelfInterPoly

theorem exists_polynomial_multilinear {A : Type*} {ι : Type} [AddCommGroup A] [Fintype ι]
    (f : (ι → A) →ₘₗ[ℤ] ℤ) (a b : A) :
    ∃ P : Polynomial ℝ, ∀ m : ℕ, (f (fun _ => a + m • b) : ℝ) = P.eval (m : ℝ) := by
  classical
  refine ⟨∑ S : Finset ι, Polynomial.C (f (S.piecewise (fun _ => b) (fun _ => a)) : ℝ) *
    Polynomial.X ^ S.card, fun m => ?_⟩
  have e : (fun _ : ι => a + m • b) = (fun _ : ι => (m : ℤ) • b) + (fun _ : ι => a) := by
    funext i
    simp [add_comm]
  rw [e, f.map_add_univ, Polynomial.eval_finsetSum, Int.cast_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have e₂ : S.piecewise (fun _ : ι => (m : ℤ) • b) (fun _ : ι => a) =
      S.piecewise (fun i => (fun _ : ι => (m : ℤ)) i • S.piecewise (fun _ => b) (fun _ => a) i)
        (S.piecewise (fun _ => b) (fun _ => a)) := by
    funext i
    by_cases h : i ∈ S <;> simp [h]
  rw [e₂, f.map_piecewise_smul]
  simp [mul_comm]

theorem exists_polynomial_topSelf : ∀ (Y : Var ℂ) (L H : LB Y.X), L.IsLB → H.IsLB → ∃ P : Polynomial ℝ, P.eval 0 = (topSelfIntersection ℂ L Y.dim : ℝ) ∧ ∀ m : ℕ, (topSelfIntersection ℂ (CechPic.tens L (lbPow H m)) Y.dim : ℝ) = P.eval (m : ℝ) := by
  intro Y L H hL hH
  have hv := diffVanish_chiPic_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver
    (d := Y.dim) (by rw [QCoh.suppDim_structureModule, Y.topologicalKrullDim_eq])
  have key : ∀ (M : LB Y.X) (hM : M.IsLB), topSelfIntersection ℂ M Y.dim = hv.form fun _ => cls M hM :=
    fun M hM => (interNum_eq_multiDiff ℂ _ fun _ => hM).trans (hv.form_apply _ 0).symm
  obtain ⟨P, hP⟩ := exists_polynomial_multilinear hv.form (cls L hL) (cls H hH)
  refine ⟨P, ?_, fun m => ?_⟩
  · have h0 := hP 0
    rw [zero_nsmul, add_zero, Nat.cast_zero] at h0
    rw [key L hL, h0]
  · rw [key _ (isLB_tens hL (isLB_lbPow hH m)), cls_tens hL (isLB_lbPow hH m), cls_lbPow hH, hP]

end GlobalTheory.SelfInterPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionMatrixEqOfUnitaryDetOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.PlaneSU

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem tensor_decomp (b : Module.Basis (Fin 2) F E) (hb0 : b 0 = 1) (z : R ⊗[F] E) :
    ∃ r₀ r₁ : R, z = algebraMap R (R ⊗[F] E) r₀ + algebraMap R (R ⊗[F] E) r₁ * ((1 : R) ⊗ₜ[F] b 1) := by
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have hz := B.sum_repr z
  rw [Fin.sum_univ_two, hB, hB, hb0, Algebra.smul_def, Algebra.smul_def, ← Algebra.TensorProduct.one_def,
    mul_one] at hz
  exact ⟨B.repr z 0, B.repr z 1, hz.symm⟩

theorem sigR_algebraMap (σ : E →ₐ[F] E) (r : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  show sigR R σ (r ⊗ₜ[F] 1) = r ⊗ₜ[F] 1
  simp [sigR]

theorem sigR_theta (σ : E →ₐ[F] E) (e : E) (he : σ e = -e) :
    sigR R σ ((1 : R) ⊗ₜ[F] e) = -((1 : R) ⊗ₜ[F] e) := by
  simp [sigR, he, TensorProduct.tmul_neg]

theorem cT_mul_eq_mul_adjugate {A : Type} [CommRing A] (c : A →+* A) (H X : Matrix (Fin 2) (Fin 2) A)
    (hX : Formalism.UG.cT c X * H * X = H) (hd : X.det = 1) : Formalism.UG.cT c X * H = H * X.adjugate := by
  calc Formalism.UG.cT c X * H = Formalism.UG.cT c X * H * (X * X.adjugate) := by
        rw [Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one]
    _ = H * X.adjugate := by rw [← Matrix.mul_assoc, hX]

end Form
end GlobalTheory.PlaneSU

theorem GlobalTheory.PlaneSU.exists_qm_eq_of_unitary : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (X : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)), Formalism.UG.cT (sigR R σ) X * Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] * X = Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] → X.det = 1 → ∃ x : ℍ[R, algebraMap F R δ, algebraMap F R (-(f₂ / f₁))], qm (algebraMap R (R ⊗[F] E)) ((1 : R) ⊗ₜ[F] b 1) x = X := by
  intro F E _ _ _ σ δ b hb0 hσ _ f₁ f₂ hf₁ _ R _ _ X hX hd
  set ι := algebraMap R (R ⊗[F] E) with hιdef
  set θ : R ⊗[F] E := (1 : R) ⊗ₜ[F] b 1 with hθdef
  set c := sigR R σ with hcdef
  set h₁ := algebraMap F (R ⊗[F] E) f₁ with hh₁
  set h₂ := algebraMap F (R ⊗[F] E) f₂ with hh₂
  set u := algebraMap F (R ⊗[F] E) f₁⁻¹ with hudef
  have key := GlobalTheory.PlaneSU.cT_mul_eq_mul_adjugate c _ X hX hd
  have k00 : c (X 0 0) * h₁ = h₁ * X 1 1 := by
    have := congrFun (congrFun key 0) 0
    simpa [Formalism.UG.cT, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have k01 : c (X 1 0) * h₂ = -(h₁ * X 0 1) := by
    have := congrFun (congrFun key 0) 1
    simpa [Formalism.UG.cT, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hcθ : c θ = -θ := GlobalTheory.PlaneSU.sigR_theta σ (b 1) hσ
  have hcι : ∀ r, c (ι r) = ι r := GlobalTheory.PlaneSU.sigR_algebraMap σ
  have hu : h₁ * u = 1 := by
    rw [hh₁, hudef, ← map_mul, mul_inv_cancel₀ hf₁, map_one]
  have hb : ι (algebraMap F R (-(f₂ / f₁))) = -(h₂ * u) := by
    rw [hιdef, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv, map_neg, map_mul]
  obtain ⟨r₀, r₁, hα⟩ := GlobalTheory.PlaneSU.tensor_decomp (R := R) b hb0 (X 0 0)
  obtain ⟨s₀, s₁, hβ⟩ := GlobalTheory.PlaneSU.tensor_decomp (R := R) b hb0 (X 1 0)
  have hcα : c (X 0 0) = ι r₀ - ι r₁ * θ := by rw [hα, map_add (f := _), map_mul, hcι, hcι, hcθ]; ring
  have hcβ : c (X 1 0) = ι s₀ - ι s₁ * θ := by rw [hβ, map_add (f := _), map_mul, hcι, hcι, hcθ]; ring
  have e00 : ι r₀ + ι r₁ * θ = X 0 0 := hα.symm
  have e10 : ι s₀ - ι (-s₁) * θ = X 1 0 := by rw [hβ, map_neg]; ring
  have e11 : ι r₀ - ι r₁ * θ = X 1 1 := by
    linear_combination (-1 : R ⊗[F] E) * hcα + u * k00 + (X 1 1 - c (X 0 0)) * hu
  have e01 : ι (algebraMap F R (-(f₂ / f₁))) * (ι s₀ + ι (-s₁) * θ) = X 0 1 := by
    rw [hb, map_neg]
    linear_combination (-u) * k01 + X 0 1 * hu + h₂ * u * hcβ
  refine ⟨⟨r₀, r₁, s₀, -s₁⟩, ?_⟩
  show !![ι r₀ + ι r₁ * θ, ι (algebraMap F R (-(f₂ / f₁))) * (ι s₀ + ι (-s₁) * θ);
    ι s₀ - ι (-s₁) * θ, ι r₀ - ι r₁ * θ] = X
  rw [e00, e01, e10, e11]
  exact (Matrix.eta_fin_two X).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothPartitionOfUnityComplexPoints
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}

theorem cInfAt_inv_of_ne_zero {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ} (h : CInfAt f y)
    (h0 : f y ≠ 0) : CInfAt (fun z => (f z)⁻¹) y := by
  obtain ⟨W, ι, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, fun v => (G v)⁻¹, O ∩ G ⁻¹' {0}ᶜ, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_compl_singleton, ⟨h₃, ?_⟩,
    (h₄.mono Set.inter_subset_left).inv fun _ hv => hv.2, ?_⟩
  · exact fun e => h0 (h₅.eq_of_nhds.trans e)
  · filter_upwards [h₅] with z e
    rw [e]

theorem cInfAt_finset_sum {ι : Type} (s : Finset ι) {f : ι → CxPts X.str σ → ℝ}
    {y : CxPts X.str σ} (h : ∀ i, CInfAt (f i) y) : CInfAt (fun z => ∑ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const 0 y
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

theorem exists_cInf_bump (y : CxPts X.str σ) {U : Set (CxPts X.str σ)} (hU : U ∈ 𝓝 y) :
    ∃ χ : CxPts X.str σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧ tsupport χ ⊆ U := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := X.dim) y
  obtain ⟨K, hKy, hKc, hKV⟩ :=
    exists_mem_nhds_isClosed_subset (inter_mem hU (c.e.open_source.mem_nhds hc))
  have hn : c.e.symm ⁻¹' K ∈ 𝓝 (c.e y) :=
    c.e.continuousAt_symm (c.e.map_source hc) (by rwa [c.e.left_inv hc])
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.1 hn
  let b : ContDiffBump (c.e y) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hsupp : ∀ z ∈ c.e.source, b (c.e z) ≠ 0 → z ∈ K := by
    intro z hz h
    have h₁ : c.e z ∈ Metric.ball (c.e y) r := by
      have : c.e z ∈ Function.support b := h
      rwa [b.support_eq] at this
    have h₂ : c.e.symm (c.e z) ∈ K := hrO h₁
    rwa [c.e.left_inv hz] at h₂
  refine ⟨fun z => if z ∈ c.e.source then b (c.e z) else 0, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · by_cases hz : z ∈ c.e.source
    · refine cInfAt_of_chart isOpen_univ c ?_ hz trivial
      refine (b.contDiff (n := ⊤)).contDiffOn.congr fun v hv => ?_
      simp only [Function.comp_apply, if_pos (c.e.map_target hv.1), c.e.right_inv hv.1]
    · have hzK : z ∉ K := fun h => hz (hKV h).2
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hKc.isOpen_compl.mem_nhds hzK] with w hw
      by_cases hwS : w ∈ c.e.source
      · simp only [if_pos hwS]
        by_contra h
        exact hw (hsupp w hwS h)
      · simp only [if_neg hwS]
  · dsimp only
    split_ifs
    · exact b.nonneg
    · exact le_rfl
  · simp only [if_pos hc]
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_pos
  · refine (closure_minimal (fun z hz => ?_) hKc).trans fun z hz => (hKV hz).1
    by_cases hzS : z ∈ c.e.source
    · exact hsupp z hzS (by simpa only [Function.mem_support, if_pos hzS] using hz)
    · simp only [Function.mem_support, if_neg hzS, ne_eq, not_true_eq_false] at hz

theorem exists_cInf_partition : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (W : CxPts X.str σ → Set (CxPts X.str σ)), (∀ y, W y ∈ 𝓝 y) → ∃ (s : Finset (CxPts X.str σ)) (ρ : s → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) ∧ (∀ i, tsupport (ρ i) ⊆ W i) ∧ ∀ y, ∑ i, ρ i y = 1 := by
  intro F _ σ X W hW
  haveI := CxPts.compactSpace σ X.isProjOver
  choose χ hχ h0 hpos hs using fun y => exists_cInf_bump y (hW y)
  obtain ⟨s, hcov⟩ := CompactSpace.elim_nhds_subcover (fun y => {z | 0 < χ y z})
    fun y => (hχ y y).continuousAt.eventually (lt_mem_nhds (hpos y))
  have hT (z) : ∑ i : s, χ i z ≠ 0 := by
    have hz : z ∈ ⋃ y ∈ s, {z | 0 < χ y z} := hcov ▸ Set.mem_univ z
    obtain ⟨y, hy, hz⟩ := Set.mem_iUnion₂.1 hz
    exact (Finset.sum_pos' (f := fun i : s => χ i z) (fun i _ => h0 i z)
      ⟨⟨y, hy⟩, Finset.mem_univ _, hz⟩).ne'
  refine ⟨s, fun i z => χ i z * (∑ j : s, χ j z)⁻¹, fun i y => ?_,
    fun i => (tsupport_mul_subset_left).trans (hs i), fun y => ?_⟩
  · exact (hχ i y).comp₂ (cInfAt_inv_of_ne_zero
      (cInfAt_finset_sum Finset.univ fun j : s => hχ j y) (hT y))
      (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)
  · rw [← Finset.sum_mul, mul_inv_cancel₀ (hT y)]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleCohomologyGenericFibreHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) n i) := by
  first | (exact @GlobalTheory.EtC.GenFibreLine.genericFibre_subsingleton) | (exact GlobalTheory.EtC.GenFibreLine.genericFibre_subsingleton) | (intros; apply GlobalTheory.EtC.GenFibreLine.genericFibre_subsingleton  <;> assumption)
end

