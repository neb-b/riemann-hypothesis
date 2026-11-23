module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsBounds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem eval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {w : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : f ∈ mCoordIdeal w) : eval w (map (Int.castRingHom ℂ) f) = 0 := by
  have h : (mConeMap w : MRing ι →+* MvPolynomial K ℂ) f = 0 := RingHom.mem_ker.mp hf
  have key : ((MvPolynomial.eval (fun _ : K => (1 : ℂ))).comp (mConeMap w : MRing ι →+* MvPolynomial K ℂ) : MRing ι →+* ℂ)
      = (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMap]
    · intro p
      simp [mConeMap]
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at this
  rw [← this, h, map_zero]

theorem bvec_good : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt (BM.F l) (mCoordIdeal (FC.bvec BM l b)) ∧ (∀ k, FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1) ∧ SameOrbit (FC.bvec BM l b) (BM.Rb.lift b b) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift b b)) := BM.good l b hb
  have hne : ∀ k, BM.Rb.lift b b ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k =>
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.chart_ne (hgood.1 k)
  have hbv : ∀ q, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b q
      = (BM.Rb.lift b b ⟨q.1, (BM.F l).c q.1⟩)⁻¹ * BM.Rb.lift b b q := fun q => by
    simp only [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec, div_eq_inv_mul]
  have horb : SameOrbit (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) (BM.Rb.lift b b) := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit
    exact ⟨fun k => (BM.Rb.lift b b ⟨k, (BM.F l).c k⟩)⁻¹, fun k => inv_ne_zero (hne k), funext hbv⟩
  have hideal : mCoordIdeal (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b) = mCoordIdeal (BM.Rb.lift b b) :=
    GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit horb
  have hone : ∀ k, GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hbv]; exact inv_mul_cancel₀ (hne k)
  have hmem : BM.Rb.lift b b ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem b b (BM.Rb.mem_U b)
  have hpt : GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec BM l b ∈ mcPts (mCoordIdeal M.x) := by
    simp only [mcPts, Set.mem_ofPred_eq]
    refine ⟨fun k => ⟨(BM.F l).c k, by rw [hone k]; exact one_ne_zero⟩, fun f hf => ?_⟩
    apply eval_eq_zero_of_mem_mCoordIdeal
    rw [hideal]
    exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hmem hf
  refine ⟨hpt, ?_, hone, horb⟩
  rw [hideal]
  exact hgood

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockGBlockDiagPosDef
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem blockG_isBlockDiag_posDef :
    ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef →
      IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef :=
  PositivityTheory.Xgp.t_c_bm_exists_blockpos

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivialization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem exists_analytic_param {A B E : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Φ : E → A} {G : A → B} {e₀ : E}
    (hΦ : AnalyticAt ℂ Φ e₀) (hG : AnalyticAt ℂ G (Φ e₀))
    (hinj : ∀ e, fderiv ℂ Φ e₀ e = 0 → e = 0)
    (hker : ∀ w, fderiv ℂ G (Φ e₀) w = 0 → ∃ e, w = fderiv ℂ Φ e₀ e)
    (hzero : ∀ᶠ e in 𝓝 e₀, G (Φ e) = 0) {U : Set E} (hU : U ∈ 𝓝 e₀) :
    ∃ (V : Set A) (S : A → E), IsOpen V ∧ Φ e₀ ∈ V ∧ AnalyticOnNhd ℂ S V ∧ S (Φ e₀) = e₀ ∧
      ∀ z ∈ V, G z = 0 → S z ∈ U ∧ z = Φ (S z) := by
  set L := fderiv ℂ Φ e₀ with hL
  have hLi : LinearMap.ker (L : E →ₗ[ℂ] A) = ⊥ := LinearMap.ker_eq_bot'.mpr hinj
  obtain ⟨p, hp⟩ := (L : E →ₗ[ℂ] A).exists_leftInverse_of_injective hLi
  let π : A →L[ℂ] E := LinearMap.toContinuousLinearMap p
  have hπ : ∀ e, π (L e) = e := fun e => LinearMap.congr_fun hp e

  let h : E → E := fun e => π (Φ e)
  have hh : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) e₀ := by
    have h1 := π.hasStrictFDerivAt.comp e₀ hΦ.hasStrictFDerivAt
    refine h1.congr_fderiv ?_
    ext e
    simp [hπ, ← hL]
  let Φ₁ := hh.toOpenPartialHomeomorph h
  have hΦ₁ : ∀ e, Φ₁ e = π (Φ e) := fun e => rfl
  have hs₁ : e₀ ∈ Φ₁.source := hh.mem_toOpenPartialHomeomorph_source
  have han₁ : AnalyticAt ℂ Φ₁ e₀ := (π.analyticAt _).comp hΦ
  have hsymm : AnalyticAt ℂ Φ₁.symm (Φ₁ e₀) :=
    Φ₁.analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hs₁ han₁ hh.hasFDerivAt.fderiv
  have hback : Φ₁.symm (Φ₁ e₀) = e₀ := Φ₁.left_inv hs₁

  let M : A →L[ℂ] B × E := (fderiv ℂ G (Φ e₀)).prod π
  have hMi : LinearMap.ker (M : A →ₗ[ℂ] B × E) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun w hw => ?_
    have h1 : fderiv ℂ G (Φ e₀) w = 0 := congrArg Prod.fst hw
    have h2 : π w = 0 := congrArg Prod.snd hw
    obtain ⟨e, rfl⟩ := hker w h1
    rw [hπ] at h2
    rw [h2, map_zero]
  obtain ⟨q, hq⟩ := (M : A →ₗ[ℂ] B × E).exists_leftInverse_of_injective hMi
  let R : B × E →L[ℂ] A := LinearMap.toContinuousLinearMap q
  have hR : ∀ w, R (M w) = w := fun w => LinearMap.congr_fun hq w
  let Ξ : A → A := fun z => R (G z, π z)
  have hΞ : HasStrictFDerivAt Ξ ((ContinuousLinearEquiv.refl ℂ A : A ≃L[ℂ] A) : A →L[ℂ] A) (Φ e₀) := by
    have h1 := R.hasStrictFDerivAt.comp (Φ e₀) (hG.hasStrictFDerivAt.prodMk π.hasStrictFDerivAt)
    refine h1.congr_fderiv ?_
    ext w
    exact hR w
  let Φ₂ := hΞ.toOpenPartialHomeomorph Ξ
  have hs₂ : Φ e₀ ∈ Φ₂.source := hΞ.mem_toOpenPartialHomeomorph_source

  have hN : ∀ᶠ e in 𝓝 e₀, e ∈ U ∧ G (Φ e) = 0 ∧ Φ e ∈ Φ₂.source :=
    (Filter.eventually_of_mem hU fun _ h => h).and (hzero.and
      (hΦ.continuousAt.eventually_mem (Φ₂.open_source.mem_nhds hs₂)))
  have hc₁ : ContinuousAt Φ₁.symm (Φ₁ e₀) := hsymm.continuousAt
  have hN' : ∀ᶠ x in 𝓝 (Φ₁ e₀), Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source := by
    have := hc₁.tendsto.eventually (by rw [hback]; exact hN)
    exact this
  have ht₁ : Φ₁ e₀ ∈ Φ₁.target := Φ₁.map_source hs₁
  have hP : ∀ᶠ x in 𝓝 (Φ₁ e₀), (Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source) ∧
      x ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm x :=
    hN'.and ((Φ₁.open_target.mem_nhds ht₁ |> Filter.eventually_of_mem <| fun _ h => h).and hsymm.eventually_analyticAt)
  have hπc : Tendsto π (𝓝 (Φ e₀)) (𝓝 (Φ₁ e₀)) := π.continuous.tendsto _
  have hQ : ∀ᶠ z in 𝓝 (Φ e₀), ((Φ₁.symm (π z) ∈ U ∧ G (Φ (Φ₁.symm (π z))) = 0 ∧ Φ (Φ₁.symm (π z)) ∈ Φ₂.source) ∧
      π z ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm (π z)) ∧ z ∈ Φ₂.source :=
    (hπc.eventually hP).and (Φ₂.open_source.mem_nhds hs₂ |> Filter.eventually_of_mem <| fun _ h => h)
  obtain ⟨V, hVs, hVo, hV0⟩ := mem_nhds_iff.mp hQ
  refine ⟨V, fun z => Φ₁.symm (π z), hVo, hV0, ?_, hback, ?_⟩
  · intro z hz
    exact AnalyticAt.comp (f := fun z => π z) (hVs hz).1.2.2 (π.analyticAt z)
  · intro z hz hGz
    obtain ⟨⟨⟨hU', hG', hsrc⟩, htgt, -⟩, hzs⟩ := hVs hz
    refine ⟨hU', ?_⟩
    have h1 : π (Φ (Φ₁.symm (π z))) = π z := Φ₁.right_inv htgt
    refine Φ₂.injOn hzs hsrc ?_
    show R (G z, π z) = R (G _, π _)
    rw [hGz, hG', h1]


open MvPolynomial in
theorem exists_chart_inverse {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}
    (hP : IsMultiHomogIdeal P) {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) {t₀ : Fin n → ℂ}
    (ht₀ : t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (htan : ∀ v, IsConeTangent (Int.castRingHom ℂ) P (χ.γ t₀) v →
      ∃ (u : Fin n → ℂ) (c : K → ℂ), v = fderiv ℂ χ.γ t₀ u + torusSmul c (χ.γ t₀)) :
    ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin n → ℂ), IsOpen V ∧ χ.γ t₀ ∈ V ∧
      AnalyticOnNhd ℂ T V ∧ T (χ.γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts P, T z ∈ Metric.ball 0 1 ∧
        ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (χ.γ (T z)) := by
  classical
  set z₀ := χ.γ t₀ with hz₀
  let σ : ℤ →+* ℂ := Int.castRingHom ℂ

  let ell : MRing J → Module.Dual ℂ ((Σ k, J k) → ℂ) := fun f =>
    ∑ i, eval z₀ (pderiv i (map σ f)) • LinearMap.proj i
  have hell : ∀ f w, ell f w = ∑ i, eval z₀ (pderiv i (map σ f)) * w i := fun f w => by
    simp [ell, LinearMap.sum_apply]
  obtain ⟨s, hsub, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (ell '' (P : Set (MRing J)))).1
    (IsNoetherian.noetherian (Submodule.span ℂ (ell '' (P : Set (MRing J)))))
  have hch : ∀ l : s, ∃ f ∈ P, ell f = l.1 := fun l => by
    obtain ⟨f, hf, h⟩ := hsub l.2
    exact ⟨f, hf, h⟩
  choose f hfP hfl using hch
  let g : s → MvPolynomial (Σ k, J k) ℂ := fun l => map σ (f l)
  let G : ((Σ k, J k) → ℂ) → s → ℂ := fun z l => eval z (g l)
  let Φ : (K → ℂ) × (Fin n → ℂ) → (Σ k, J k) → ℂ := fun e => torusSmul e.1 (χ.γ e.2)
  let e₀ : (K → ℂ) × (Fin n → ℂ) := (1, t₀)
  have hΦ₀ : Φ e₀ = z₀ := by
    funext p
    simp [Φ, e₀, torusSmul, hz₀]
  have hγ : AnalyticAt ℂ χ.γ t₀ := χ.analytic t₀ ht₀
  have hΦan : AnalyticAt ℂ Φ e₀ := by
    refine AnalyticAt.pi fun p => ?_
    have h1 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1) e₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
        (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).analyticAt e₀
    have h2 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2) e₀ :=
      AnalyticAt.comp (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγ
        ((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt e₀)
    have h3 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p) e₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp h2
    exact h1.mul h3
  have hGan : AnalyticAt ℂ G (Φ e₀) := by
    refine AnalyticAt.pi fun l => ?_
    exact AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (g l) _ (Set.mem_univ _)

  have hdΦ : ∀ c u, fderiv ℂ Φ e₀ (c, u) = fderiv ℂ χ.γ t₀ u + torusSmul c z₀ := by
    have hγd := hγ.differentiableAt.hasFDerivAt
    have hD : HasFDerivAt Φ (ContinuousLinearMap.pi fun p : (Σ k, J k) =>
        (1 : ℂ) • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp
            ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) +
          z₀ p • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ)))) e₀ := by
      refine hasFDerivAt_pi.2 fun p => ?_
      have h1 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))) e₀ :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).hasFDerivAt
      have h2 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2)
          ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ))) e₀ :=
        HasFDerivAt.comp e₀ (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγd
          (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).hasFDerivAt
      have h3 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp
            ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) e₀ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).hasFDerivAt.comp e₀ h2
      refine (h1.mul h3).congr_fderiv ?_
      simp [e₀, hz₀]
    intro c u
    rw [hD.fderiv]
    funext p
    simp [torusSmul, mul_comm]

  have hdG : ∀ w l, fderiv ℂ G (Φ e₀) w l = ell (f l) w := by
    have hD : HasFDerivAt G (ContinuousLinearMap.pi fun l : s =>
        ∑ i, eval (Φ e₀) (pderiv i (g l)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) i)
        (Φ e₀) := hasFDerivAt_pi.2 fun l => hasFDerivAt_eval (g l) (Φ e₀)
    intro w l
    rw [hD.fderiv, hell, hΦ₀]
    simp [g]
  have hinj : ∀ e, fderiv ℂ Φ e₀ e = 0 → e = 0 := by
    rintro ⟨c, u⟩ h
    rw [hdΦ] at h
    have hu : u = 0 := by
      refine χ.immersion t₀ ht₀ u ⟨fun k => - c k, ?_⟩
      funext p
      have := congrFun h p
      simp only [Pi.add_apply, Pi.zero_apply, torusSmul] at this ⊢
      rw [← hz₀]
      linear_combination this
    subst hu
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := (χ.mem t₀ ht₀).1 k
      have := congrFun h ⟨k, i⟩
      simp only [map_zero, Pi.add_apply, Pi.zero_apply, zero_add, torusSmul] at this
      exact (mul_eq_zero.mp this).resolve_right hi
    simp [hc]
  have hker : ∀ w, fderiv ℂ G (Φ e₀) w = 0 → ∃ e, w = fderiv ℂ Φ e₀ e := by
    intro w hw
    have hs0 : ∀ l ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ))), l w = 0 := by
      intro l hl
      induction hl using Submodule.span_induction with
      | mem x hx =>
        have := congrFun hw ⟨x, hx⟩
        rw [hdG, hfl] at this
        exact this
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => simp [hx]
    have htv : IsConeTangent (Int.castRingHom ℂ) P z₀ w := by
      intro q hq
      have : ell q ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ))) := by
        rw [← hspan]
        exact Submodule.subset_span ⟨q, hq, rfl⟩
      have h0 := hs0 _ this
      rw [hell] at h0
      exact h0
    obtain ⟨u, c, hv⟩ := htan w htv
    exact ⟨(c, u), by rw [hdΦ, hv]⟩
  have hopen : ∀ᶠ e : (K → ℂ) × (Fin n → ℂ) in 𝓝 e₀, (∀ k, e.1 k ≠ 0) ∧ e.2 ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    refine Filter.Eventually.and (eventually_all.2 fun k => ?_) ?_
    · have hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 k) e₀ := by fun_prop
      exact hc.eventually_ne (by simp [e₀])
    · have hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.2) e₀ := by fun_prop
      exact hc.eventually_mem (Metric.isOpen_ball.mem_nhds ht₀)
  have hzero : ∀ᶠ e in 𝓝 e₀, G (Φ e) = 0 := by
    filter_upwards [hopen] with e he
    funext l
    exact (mcPts_smul hP e.1 he.1 (χ.mem e.2 he.2)).2 (f l) (hfP l)
  obtain ⟨V, S, hVo, hV0, hSan, hS0, hS⟩ := exists_analytic_param hΦan hGan hinj hker hzero hopen
  rw [hΦ₀] at hV0 hS0
  refine ⟨V, fun z => (S z).2, hVo, hV0, ?_, by simp [hS0, e₀], ?_⟩
  · intro z hz
    exact ((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt _).comp (hSan z hz)
  · rintro z ⟨hzV, hzP⟩
    have hGz : G z = 0 := by
      funext l
      exact hzP.2 (f l) (hfP l)
    obtain ⟨hU, hz⟩ := hS z hzV hGz
    exact ⟨hU.2, (S z).1, hU.1, hz⟩

theorem chart_torus_open : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts), ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), IsOpen V ∧ (D.chart a).γ t₀ ∈ V ∧ AnalyticOnNhd ℂ T V ∧ T ((D.chart a).γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts (mCoordIdeal D.y), T z ∈ Metric.ball 0 1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((D.chart a).γ (T z)) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D a t₀ ht₀
  exact exists_chart_inverse D.arith.2.1.2.1 (D.chart a) ht₀
    (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.coneTangent_eq_fderiv_add_torusSmul K J II Ψ Ω W D a t₀ ht₀)

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CutoffFunctionOnCompatibleAtlas
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds : ∀ (n p q : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas n X) (Z Cl U : Set X) (r : X → ℝ) (Γ : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), A.Compatible B → (∀ k, Metric.closedBall (0 : Fin n → ℂ) 2 ⊆ (B.chart k).target) → (∀ x, ∃ k, x ∈ (B.chart k).source ∧ B.chart k x ∈ Metric.ball (0 : Fin n → ℂ) 1) → IsClosed Z → IsClosed Cl → IsOpen U → U ⊆ Cl → (∀ x, x ∉ Z → Real.exp 1 ≤ r x) → (∀ (k : Fin B.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → (B.chart k).symm w₀ ∈ Cl → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (B.chart k).symm w ∉ Z → (Γ ((B.chart k).symm w)).PosDef ∧ ((Γ ((B.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef ∧ (((C * r ((B.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ ((B.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ ((B.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => Γ ((B.chart k).symm w') a b) w‖ ≤ C * Real.exp (r ((B.chart k).symm w) / 2)) → (∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧ A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im)) ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → (∀ x ∈ Cl \ Z, (((r x ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ x)).PosSemidef ∧ (((r x ^ C : ℝ) : ℂ) • blockG (Γ x) - 1).PosSemidef) ∧ ∀ (a b : Fin (p + q)) (k : Fin B.n), ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (B.chart k).symm w ∈ Cl \ Z → ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤ C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) :=
  @PositivityTheory.Xgp.t_c_bm_exists_bounds
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFiniteFrameCover
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames

theorem exists_finite_good_frames : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), ∃ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι Ψ N M.Ω M.blk), (∀ l, IsOpen (O l)) ∧ (∀ x, ∃ l, x ∈ O l) ∧ (∀ l, M.IsFrame (F l)) ∧ ∀ l, ∀ x ∈ closure (O l), M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) := by
  exact @PositivityTheory.Xgp.t_c_bm_exists_frames

end GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

private theorem sum_eq_sum_orderEmbOfFin_of_zero_off {N : ℕ} (S : Finset (Fin N)) (F : Fin N → ℂ)
    (hz : ∀ a, a ∉ S → F a = 0) :
    ∑ a, F a = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) := by
  calc ∑ a, F a = ∑ a ∈ S, F a :=
        (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hz a ha)).symm
    _ = ∑ i : S, F i := (Finset.sum_coe_sort S F).symm
    _ = ∑ z : Fin S.card, F (S.orderEmbOfFin rfl z) :=
        (Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _
          (fun z => by simp [Finset.coe_orderIsoOfFin_apply])).symm

private theorem minorIJ_mul_of_block {N : ℕ} (h B : Matrix (Fin N) (Fin N) ℂ) (S I : Finset (Fin N))
    (hB : ∀ a c, c ∈ S → a ∉ S → B a c = 0) :
    minorIJ (h * B) I S = minorIJ h I S * minorIJ B S S := by
  unfold minorIJ
  by_cases e : I.card = S.card
  · rw [dite_eq_left e, dite_eq_left e, dite_eq_left rfl, ← Matrix.det_mul]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    exact sum_eq_sum_orderEmbOfFin_of_zero_off S (fun a => h (I.orderEmbOfFin e x) a * B a (S.orderEmbOfFin rfl y))
      (fun a ha => by rw [hB a _ (Finset.orderEmbOfFin_mem S rfl y) ha, mul_zero])
  · rw [dite_eq_right e, dite_eq_right e, zero_mul]

private theorem apply_eq_zero_of_mem_stepCols_not_mem {N j : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (hd : IsBlockDiag j B) (ht : B.BlockTriangular id) :
    ∀ a c, c ∈ stepCols N j i → a ∉ stepCols N j i → B a c = 0 := by
  intro a c hc ha
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc ha
  have hi := i.isLt
  by_cases hblk : ((a : ℕ) < N - j ↔ (c : ℕ) < N - j)
  · apply ht
    show c < a
    rw [Fin.lt_def]
    split_ifs at hc ha <;> omega
  · exact hd a c hblk

private theorem minorIJ_ne_zero_of_blockTriangular {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (ht : B.BlockTriangular id) (hdet : B.det ≠ 0) : minorIJ B S S ≠ 0 := by
  unfold minorIJ
  rw [dite_eq_left rfl]
  have hdiag : ∀ a, B a a ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular ht] at hdet
    exact fun a => (Finset.prod_ne_zero_iff.mp hdet) a (Finset.mem_univ a)
  have htS : (B.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).BlockTriangular id :=
    fun x y hxy => ht ((S.orderEmbOfFin rfl).strictMono hxy)
  rw [Matrix.det_of_isUpperTriangular htS]
  exact Finset.prod_ne_zero_iff.mpr (fun z _ => hdiag _)

theorem sameOrbit_flagPt_mul : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h B : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsBlockDiag j (B τ') ∧ (B τ').BlockTriangular id ∧ (B τ').det ≠ 0) → SameOrbit (FC.flagPt M F b fun τ' => h τ' * B τ') (FC.flagPt M F b h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h B hB
  refine Exists.intro (fun k => if hk : ∀ p, M.blk p ≠ some k then (1 : ℂ) else
    minorIJ (B (not_forall.1 hk).choose.1) (stepCols N j (not_forall.1 hk).choose.2)
      (stepCols N j (not_forall.1 hk).choose.2)) ⟨fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with hk
    · exact one_ne_zero
    · generalize (not_forall.1 hk).choose = p
      exact minorIJ_ne_zero_of_blockTriangular (B p.1) (stepCols N j p.2) (hB p.1).2.1 (hB p.1).2.2
  · funext q
    simp only [flagPt]
    split_ifs with hk
    · rw [one_mul]
    · generalize (not_forall.1 hk).choose = p
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I _ => ?_)
      rw [minorIJ_mul_of_block (h p.1) (B p.1) (stepCols N j p.2) I
        (apply_eq_zero_of_mem_stepCols_not_mem (B p.1) p.2 (hB p.1).1 (hB p.1).2.1)]
      ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentMinorFormulaStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_minor_formula : ∀ (N j : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (a' b' : Fin N), j ≤ N → IsBlockDiag j X → IsLowerUni X → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → minorIJ X (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) = 1 ∧ minorIJ X (insert a' ((stepCols N j (stepOf N j b')).erase b')) (stepCols N j (stepOf N j b')) = X a' b' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni <;> assumption)
end

