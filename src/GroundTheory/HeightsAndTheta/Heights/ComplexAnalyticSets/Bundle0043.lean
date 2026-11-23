module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolyDerivationsDetectSquare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

open IsLocalRing KaehlerDifferential TensorProduct

theorem PolyDerivationsDetectSquare.of_perfectField
    (h₁ : PerfectFieldExtensionFormallySmooth.Statement) (h₂ : PolyKaehlerFree.Statement)
    (F k : Type) [Field F] [Field k] [Algebra F k] [PerfectField F] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] (g : MvPolynomial (Fin n) k) (hg : g ∈ p)
    (hD : ∀ D : Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k), D g ∈ p) :
    algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  classical

  have : Algebra.FormallySmooth F k := h₁ F k
  have : Algebra.FormallySmooth F p.ResidueField := h₁ F p.ResidueField
  have : Algebra.FormallySmooth F (MvPolynomial (Fin n) k) :=
    Algebra.FormallySmooth.comp F k (MvPolynomial (Fin n) k)
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime p) p.ResidueField) :=
    IsLocalRing.residue_surjective
  obtain ⟨ret, hret⟩ := (Algebra.FormallySmooth.iff_split_injection (R := F)
    (P := Localization.AtPrime p) hsurj).mp inferInstance
  have hinj : Function.Injective (kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField) :=
    Function.LeftInverse.injective (g := ret) fun x => LinearMap.congr_fun hret x
  have hgI : algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) := by
    rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hg

  have : Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F] := h₂ F k n
  let b := Module.Free.chooseBasis (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F]
  have hc : ∀ α, b.repr (D F (MvPolynomial (Fin n) k) g) α ∈ p := fun α =>
    hD (((b.coord α).compDer (D F (MvPolynomial (Fin n) k))).restrictScalars ℤ)

  have hzero : kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField
      (Ideal.toCotangent _ ⟨_, hgI⟩) = 0 := by
    change (1 : p.ResidueField) ⊗ₜ[Localization.AtPrime p]
      D F (Localization.AtPrime p) (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g) = 0
    rw [← map_D F F (MvPolynomial (Fin n) k) (Localization.AtPrime p),
      ← b.linearCombination_repr (D F (MvPolynomial (Fin n) k) g), Finsupp.linearCombination_apply,
      map_finsuppSum, Finsupp.sum, tmul_sum]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [LinearMap.map_smul, ← algebraMap_smul (Localization.AtPrime p), tmul_smul,
      ← algebraMap_smul p.ResidueField, ← IsScalarTower.algebraMap_apply,
      Ideal.algebraMap_residueField_eq_zero.mpr (hc α), zero_smul]
  have h0 := hinj (hzero.trans (map_zero _).symm)
  have hker : RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) =
      maximalIdeal (Localization.AtPrime p) := IsLocalRing.ker_residue
  rw [Ideal.toCotangent_eq_zero] at h0
  rw [← hker]
  exact h0

theorem PolyDerivationsDetectSquare.proof (h₁ : PerfectFieldExtensionFormallySmooth.Statement)
    (h₂ : PolyKaehlerFree.Statement) : PolyDerivationsDetectSquare.Statement := by
  intro k _ n p _ g hg hD
  obtain ⟨q, hq⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k q with hqp | rfl
  · have : Fact q.Prime := ⟨hqp⟩
    let _ : Algebra (ZMod q) k := ZMod.algebra k q
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ (ZMod q) k n p g hg hD
  · have : CharZero k := CharP.charP_to_charZero k
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ ℚ k n p g hg hD

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem graphPt_injective {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) : Function.Injective (graphPt e F) := by
  intro x y h
  ext i
  have := congrArg (fun z : EuclideanSpace ℂ (Fin n) => z (e.symm (Sum.inl i))) h
  simpa [graphPt] using this

theorem differentiableAt_graphPt {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℂ F x) : DifferentiableAt ℂ (graphPt e F) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℂ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x
  rcases hj : e j with i | i
  · simp only [Sum.elim_inl]
    exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · simp only [Sum.elim_inr]
    exact (differentiableAt_piLp 2).1 hF i

theorem continuous_areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt

theorem ProjectionFormula.proof (h1 : AreaMultiplicity.Statement) (h2 : FrameJacobianSum.Statement)
    (h3 : GraphAreaHolomorphic.Statement) : ProjectionFormula.Statement := by
  classical
  intro d m n e Ω F hΩ hF b B hB
  have hGd : ∀ x ∈ Ω, DifferentiableAt ℂ (graphPt e F) x := fun x hx =>
    differentiableAt_graphPt e (hF.differentiableAt (hΩ.mem_nhds hx))
  set A := Ω ∩ graphPt e F ⁻¹' B with hAdef
  have hAΩ : A ⊆ Ω := Set.inter_subset_left
  have hA : MeasurableSet A := by
    have hc : ContinuousOn (graphPt e F) Ω := fun x hx => (hGd x hx).continuousAt.continuousWithinAt
    have hm := (hc.measurable_piecewise (continuousOn_const (c := (0 : EuclideanSpace ℂ (Fin n))))
      hΩ.measurableSet) hB
    have hEq : A = Ω ∩ (Ω.piecewise (graphPt e F) fun _ => 0) ⁻¹' B := by
      ext x
      simp only [hAdef, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx'⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨hx, by rw [Set.piecewise_eq_of_mem _ _ _ hx] at hx'; exact hx'⟩
    rw [hEq]
    exact hΩ.measurableSet.inter hm

  let πR : ∀ I : Finset (Fin n), EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ I := fun I =>
    (LinearMap.toContinuousLinearMap (frameProjLin b I)).restrictScalars ℝ
  have hpt : ∀ x ∈ A, ENNReal.ofReal (areaJacobian
      (fderiv ℝ (graphPt e F) x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) =
      ∑ I ∈ Finset.univ.powersetCard d, ENNReal.ofReal (areaJacobian
        ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)) := by
    intro x hx
    set L := fderiv ℂ (graphPt e F) x with hL
    have e0 : ((L.restrictScalars ℝ : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) =
        (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
      LinearMap.ext fun v => rfl
    have eI : ∀ I : Finset (Fin n), (((πR I).comp (L.restrictScalars ℝ)) :
        EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I) =
        (frameProjLin b I ∘ₗ (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).restrictScalars ℝ :=
      fun I => LinearMap.ext fun v => rfl
    rw [(hGd x (hAΩ hx)).fderiv_restrictScalars ℝ, ← hL, e0, ← ENNReal.ofReal_sum_of_nonneg]
    · simp only [eI]
      exact congrArg ENNReal.ofReal (h2 d n _ b)
    · exact fun I _ => Real.sqrt_nonneg _
  have hmeas : ∀ I : Finset (Fin n), AEMeasurable (fun x => ENNReal.ofReal (areaJacobian
      ((πR I).comp (fderiv ℝ (graphPt e F) x) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ I)))
      ((μH[((2 * d : ℕ) : ℝ)]).restrict A) := fun I =>
    ((ENNReal.continuous_ofReal.comp (continuous_areaJacobian.comp
      (continuous_const.clm_comp continuous_id))).measurable.comp
        (measurable_fderiv ℝ (graphPt e F))).aemeasurable
  rw [(Set.image_inter_preimage (graphPt e F) Ω B).symm, h3 d m n e Ω F hΩ hF A hAΩ hA,
    setLIntegral_congr_fun hA hpt, lintegral_finsetSum' _ fun I _ => hmeas I]
  refine Finset.sum_congr rfl fun I hI => ?_
  have hcard : I.card = d := (Finset.mem_powersetCard.1 hI).2
  have hfr1 : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]
  have hfr2 : finrank ℝ (EuclideanSpace ℂ I) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_coe, hcard]
  have hder : ∀ x ∈ A, HasFDerivWithinAt (fun x => frameProjLin b I (graphPt e F x))
      ((πR I).comp (fderiv ℝ (graphPt e F) x)) A x := fun x hx =>
    ((πR I).hasFDerivAt.comp x ((hGd x (hAΩ hx)).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  rw [h1 _ _ (2 * d) hfr1 hfr2 A _ _ hA hder]
  refine lintegral_congr fun y => ?_
  have hset : {z ∈ graphPt e F '' A | frameProj b I z = WithLp.ofLp y} =
      graphPt e F '' {x ∈ A | frameProjLin b I (graphPt e F x) = y} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨x, ⟨hx, WithLp.ofLp_injective 2 (by rw [frameProjLin_apply]; exact hz)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxy⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rw [← frameProjLin_apply, hxy]⟩
  unfold frameFibreCount
  rw [hset, (graphPt_injective e F).injOn.encard_image]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularLocusDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Module
open scoped ContDiff

section Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eventually_zero_of_iteratedFDeriv_diag {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀)
    (h0 : ∀ (n : ℕ) (v : E), iteratedFDeriv ℂ n ψ y₀ (fun _ => v) = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by
  obtain ⟨p, r, hp⟩ := hψ
  filter_upwards [Metric.eball_mem_nhds y₀ hp.r_pos] with u hu
  have hmem : u - y₀ ∈ Metric.eball (0 : E) r := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub] using hu
  have hs := hp.hasSum_iteratedFDeriv hmem
  simp only [h0, smul_zero, add_sub_cancel] at hs
  exact hs.unique hasSum_zero

theorem iteratedFDeriv_succ_diag_eq {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀) (n : ℕ) (v : E) :
    iteratedFDeriv ℂ (n + 1) ψ y₀ (fun _ => v) =
      iteratedFDeriv ℂ n (fun y => fderiv ℂ ψ y v) y₀ (fun _ => v) := by
  rw [iteratedFDeriv_succ_apply_right]
  have hc : ContDiffAt ℂ ω (fderiv ℂ ψ) y₀ := hψ.fderiv.contDiffAt
  have h1 := (ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left hc (i := n) le_top
  have h2 : (fun y => fderiv ℂ ψ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ ψ := rfl
  rw [h2, h1]
  rfl

theorem eventually_zero_of_conormal_zero {C : Set E} {y₀ : E} (hy₀ : y₀ ∈ C) {U : Set E} (hU : U ∈ 𝓝 y₀)
    (hC : ∀ c ∈ C ∩ U, ∀ ψ : E → ℂ, AnalyticAt ℂ ψ c → (∀ᶠ u in 𝓝 c, u ∈ C → ψ u = 0) →
      fderiv ℂ ψ c = 0)
    {ψ : E → ℂ} (hψ : AnalyticAt ℂ ψ y₀) (hψC : ∀ᶠ u in 𝓝 y₀, u ∈ C → ψ u = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by
  have step : ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) → ∀ v : E,
      AnalyticAt ℂ (fun y => fderiv ℂ φ y v) y₀ ∧ ∀ᶠ u in 𝓝 y₀, u ∈ C → fderiv ℂ φ u v = 0 := by
    intro φ hφ hφC v
    refine ⟨((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hφ.fderiv, ?_⟩
    filter_upwards [hφ.eventually_analyticAt, hφC.eventually_nhds, hU] with c hca hcC hcU hc
    rw [hC c ⟨hc, hcU⟩ φ hca hcC]
    rfl
  have key : ∀ n : ℕ, ∀ φ : E → ℂ, AnalyticAt ℂ φ y₀ → (∀ᶠ u in 𝓝 y₀, u ∈ C → φ u = 0) →
      ∀ v : E, iteratedFDeriv ℂ n φ y₀ (fun _ => v) = 0 := by
    intro n
    induction n with
    | zero => intro φ _ hφC v; simpa using hφC.self_of_nhds hy₀
    | succ n ih =>
      intro φ hφ hφC v
      rw [iteratedFDeriv_succ_diag_eq hφ]
      obtain ⟨h1, h2⟩ := step φ hφ hφC v
      exact ih _ h1 h2 v
  exact eventually_zero_of_iteratedFDeriv_diag hψ fun n v => key n ψ hψ hψC v

end Germs

noncomputable def conormalSpan {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (z : σ → ℂ) :
    Submodule ℂ ((σ → ℂ) →L[ℂ] ℂ) :=
  Submodule.span ℂ {ℓ | ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h z ∧ (∀ᶠ u in 𝓝 z, u ∈ Y → h u = 0) ∧
    fderiv ℂ h z = ℓ}

theorem exists_maxRank_equations {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) {U : Set (σ → ℂ)}
    (hU : IsOpen U) (hne : (Y ∩ U).Nonempty) :
    ∃ a ∈ Y, ∃ (ι : Type) (_ : Fintype ι) (h : ι → (σ → ℂ) → ℂ) (W : Set (σ → ℂ)),
      IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧ (∀ j, ∀ z ∈ W, AnalyticAt ℂ (h j) z) ∧
      (∀ j, ∀ z ∈ W, z ∈ Y → h j z = 0) ∧ LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) ∧
      ∀ z ∈ W ∩ Y, ∀ ψ : (σ → ℂ) → ℂ, AnalyticAt ℂ ψ z → (∀ᶠ u in 𝓝 z, u ∈ Y → ψ u = 0) →
        fderiv ℂ ψ z ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) := by
  classical
  set rk : (σ → ℂ) → ℕ := fun z => finrank ℂ (conormalSpan Y z) with hrk
  have hbdd : BddAbove (rk '' (Y ∩ U)) :=
    ⟨finrank ℂ ((σ → ℂ) →L[ℂ] ℂ), by rintro _ ⟨z, -, rfl⟩; exact Submodule.finrank_le _⟩
  obtain ⟨a, haYU, har⟩ := Nat.sSup_mem (hne.image rk) hbdd
  have hmax : ∀ z ∈ Y ∩ U, rk z ≤ rk a := fun z hz => har ▸ le_csSup hbdd ⟨z, hz, rfl⟩
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ
    {ℓ : (σ → ℂ) →L[ℂ] ℂ | ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧
      fderiv ℂ h a = ℓ}
  have : Finite b := hbli.finite
  let _ : Fintype b := Fintype.ofFinite b
  have hb' : ∀ ℓ : b, ∃ h : (σ → ℂ) → ℂ, AnalyticAt ℂ h a ∧ (∀ᶠ u in 𝓝 a, u ∈ Y → h u = 0) ∧
      fderiv ℂ h a = ℓ := fun ℓ => hbS ℓ.2
  choose h hha hhY hhd using hb'
  have hfun : (fun j : b => fderiv ℂ (h j) a) = ((↑) : b → (σ → ℂ) →L[ℂ] ℂ) := funext hhd
  have hli_a : LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) := hfun ▸ hbli
  have hcard : rk a = Fintype.card b := by
    have hsp : conormalSpan Y a = Submodule.span ℂ (Set.range fun j : b => fderiv ℂ (h j) a) := by
      rw [hfun, Subtype.range_coe, hbspan]
      rfl
    show finrank ℂ (conormalSpan Y a) = _
    rw [hsp]
    exact finrank_span_eq_card hli_a
  have E3 : ∀ᶠ z in 𝓝 a, LinearIndependent ℂ (fun j => fderiv ℂ (h j) z) := by
    have ht : Tendsto (fun z => fun j => fderiv ℂ (h j) z) (𝓝 a) (𝓝 fun j => fderiv ℂ (h j) a) :=
      tendsto_pi_nhds.2 fun j => (hha j).fderiv.continuousAt.tendsto
    exact ht.eventually hli_a.eventually
  have E : ∀ᶠ z in 𝓝 a, z ∈ U ∧ (∀ j, AnalyticAt ℂ (h j) z) ∧ (∀ j, z ∈ Y → h j z = 0) ∧
      LinearIndependent ℂ (fun j => fderiv ℂ (h j) z) :=
    (show ∀ᶠ z in 𝓝 a, z ∈ U from hU.mem_nhds haYU.2).and ((eventually_all.2 fun j => (hha j).eventually_analyticAt).and
      ((eventually_all.2 hhY).and E3))
  obtain ⟨W, hWP, hWo, haW⟩ := eventually_nhds_iff.1 E
  refine ⟨a, haYU.1, b, inferInstance, h, W, hWo, haW, fun z hz => (hWP z hz).1,
    fun j z hz => (hWP z hz).2.1 j, fun j z hz => (hWP z hz).2.2.1 j, hli_a, ?_⟩
  rintro z ⟨hzW, hzY⟩ ψ hψ hψY
  obtain ⟨hzU, hza, -, hzli⟩ := hWP z hzW
  have hle : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) ≤ conormalSpan Y z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨h j, hza j, ?_, rfl⟩
    filter_upwards [hWo.mem_nhds hzW] with u hu huY using (hWP u hu).2.2.1 j huY
  have heq : Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) z) = conormalSpan Y z :=
    Submodule.eq_of_le_of_finrank_le hle
      (by rw [finrank_span_eq_card hzli, ← hcard]; exact hmax z ⟨hzY, hzU⟩)
  rw [heq]
  exact Submodule.subset_span ⟨ψ, hψ, hψY, rfl⟩

theorem RegularLocusDense.proof (hIFT : AnalyticImplicitChart.Statement) : RegularLocusDense.Statement := by
  intro σ _ X w hX
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨N, hNo, hwN, fun B hBo hBN x hx => ?_⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  have hU : IsOpen (interior t ∩ B) := isOpen_interior.inter hBo
  obtain ⟨a, haY, ι, hι, h, W, hWo, haW, hWU, hha, hhY, hli, hspan⟩ :=
    exists_maxRank_equations (X ∩ B) hU ⟨x, hx, mem_interior_iff_mem_nhds.2 ht, hx.2⟩
  obtain ⟨d, A, O, V, g, -, hOo, hVo, haV, hVW, hg, hAg, hVO⟩ :=
    hIFT σ ι h a W (fun j => hha j a haW) (fun j => hhY j a haW haY) hli (hWo.mem_nhds haW)

  have hgV : ∀ y ∈ O, g y ∈ V ∧ ∀ j, h j (g y) = 0 := fun y hy =>
    (show g y ∈ {z | z ∈ V ∧ ∀ j, h j z = 0} from hVO ▸ Set.mem_image_of_mem g hy)
  have hYV : ∀ z ∈ X ∩ B, z ∈ V → g (A z) = z ∧ A z ∈ O := by
    intro z hzY hzV
    have hz : z ∈ g '' O := hVO ▸ (⟨hzV, fun j => hhY j z (hVW hzV) hzY⟩ : z ∈ {z | z ∈ V ∧ ∀ j, h j z = 0})
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hAg y hy]
    exact ⟨rfl, hy⟩
  obtain ⟨hga, hy₀O⟩ := hYV a haY haV

  have hAD : ∀ y ∈ O, A.comp (fderiv ℂ g y) = ContinuousLinearMap.id ℂ _ := by
    intro y hy
    have h3 : HasFDerivAt (fun y => A (g y)) (A.comp (fderiv ℂ g y)) y :=
      A.hasFDerivAt.comp y (hg y hy).differentiableAt.hasFDerivAt
    have h4 : HasFDerivAt (fun y => A (g y)) (ContinuousLinearMap.id ℂ (Fin d → ℂ)) y :=
      (hasFDerivAt_id y).congr_of_eventuallyEq (by filter_upwards [hOo.mem_nhds hy] with u hu using hAg u hu)
    exact h3.unique h4
  have hhD : ∀ y ∈ O, ∀ j, (fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y) = 0 := by
    intro y hy j
    have h3 : HasFDerivAt (fun y => h j (g y)) ((fderiv ℂ (h j) (g y)).comp (fderiv ℂ g y)) y :=
      (hha j (g y) (hVW (hgV y hy).1)).differentiableAt.hasFDerivAt.comp y
        (hg y hy).differentiableAt.hasFDerivAt
    have h4 : HasFDerivAt (fun y => h j (g y)) (0 : (Fin d → ℂ) →L[ℂ] ℂ) y :=
      (hasFDerivAt_const 0 y).congr_of_eventuallyEq
        (by filter_upwards [hOo.mem_nhds hy] with u hu using (hgV u hu).2 j)
    exact h3.unique h4

  have hC : ∀ c ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} ∩ O, ∀ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ c →
      (∀ᶠ u in 𝓝 c, u ∈ {y | y ∈ O ∧ g y ∈ X ∩ B} → ψ u = 0) → fderiv ℂ ψ c = 0 := by
    rintro c ⟨⟨hcO, hcY⟩, -⟩ ψ hψ hψC
    have hzV := (hgV c hcO).1
    have hAz : A (g c) = c := hAg c hcO
    have hψ' : AnalyticAt ℂ ψ (A (g c)) := by rw [hAz]; exact hψ
    have hH : AnalyticAt ℂ (fun u => ψ (A u)) (g c) := hψ'.comp (A.analyticAt (g c))
    have hHY : ∀ᶠ u in 𝓝 (g c), u ∈ X ∩ B → ψ (A u) = 0 := by
      have hAt : Tendsto A (𝓝 (g c)) (𝓝 c) := by
        have h0 := A.continuous.tendsto (g c)
        rwa [hAz] at h0
      filter_upwards [hVo.mem_nhds hzV, hAt hψC] with u huV huψ huY
      obtain ⟨hgu, huO⟩ := hYV u huY huV
      exact huψ ⟨huO, hgu.symm ▸ huY⟩
    have hmem := hspan (g c) ⟨hVW hzV, hcY⟩ _ hH hHY
    have hchain : fderiv ℂ (fun u => ψ (A u)) (g c) = (fderiv ℂ ψ c).comp A := by
      have hψd : HasFDerivAt ψ (fderiv ℂ ψ c) (A (g c)) := by
        rw [hAz]; exact hψ.differentiableAt.hasFDerivAt
      exact (hψd.comp (g c) A.hasFDerivAt).fderiv
    have hkill : ∀ ℓ ∈ Submodule.span ℂ (Set.range fun j => fderiv ℂ (h j) (g c)),
        ℓ.comp (fderiv ℂ g c) = 0 := by
      intro ℓ hℓ
      induction hℓ using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hhD c hcO j
      | zero => simp
      | add x y _ _ hx hy => rw [ContinuousLinearMap.add_comp, hx, hy, add_zero]
      | smul r x _ hx =>
        rw [ContinuousLinearMap.smul_comp, hx]
        ext v
        simp
    have hk := hkill _ hmem
    rw [hchain, ContinuousLinearMap.comp_assoc, hAD c hcO, ContinuousLinearMap.comp_id] at hk
    exact hk

  have hvan : ∀ i, ∀ᶠ y in 𝓝 (A a), f i (g y) = 0 := by
    intro i
    refine eventually_zero_of_conormal_zero (C := {y | y ∈ O ∧ g y ∈ X ∩ B})
      ⟨hy₀O, hga.symm ▸ haY⟩ (hOo.mem_nhds hy₀O) hC ?_ ?_
    · have hfa : AnalyticAt ℂ (f i) (g (A a)) := hga.symm ▸ hf i a (hBN haY.2)
      exact hfa.comp (hg (A a) hy₀O)
    · refine Eventually.of_forall fun y hy => ?_
      have hgy : g y ∈ X ∩ N := ⟨hy.2.1, hBN hy.2.2⟩
      rw [hXN] at hgy
      exact hgy.2 i
  obtain ⟨O', hO'P, hO'o, hy₀O'⟩ :=
    eventually_nhds_iff.1 ((eventually_all.2 hvan).and (hOo.mem_nhds hy₀O))
  refine ⟨a, interior_subset (hWU haW).1, haY, d, A, O', V ∩ A ⁻¹' O', g, hO'o,
    hVo.inter (hO'o.preimage A.continuous), ⟨haV, hy₀O'⟩, hg.mono fun y hy => (hO'P y hy).2,
    fun y hy => hAg y (hO'P y hy).2, ?_⟩
  ext z
  constructor
  · rintro ⟨hzY, hzV, hzO'⟩
    exact ⟨A z, hzO', (hYV z hzY hzV).1⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hf0, hyO⟩ := hO'P y hy
    have hgyV := (hgV y hyO).1
    have hgB : g y ∈ B := (hWU (hVW hgyV)).2
    have hgX : g y ∈ X := by
      have hz : g y ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hBN hgB, hf0⟩
      rw [← hXN] at hz
      exact hz.1
    refine ⟨⟨hgX, hgB⟩, hgyV, ?_⟩
    show A (g y) ∈ O'
    rw [hAg y hyO]
    exact hy

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreRFlatAscent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem SerreRFlatAscent.proof : SerreRFlatAscent.Statement := by
  intro A B _ _ _ hA hB hflat k hRA hfib P _ hdim
  have : IsNoetherianRing A := hA
  have : IsNoetherianRing B := hB
  have : Module.Flat A B := hflat
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  have : IsLocalHom (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) :=
    Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  have := isLocalRing_closedFibre (R := Localization.AtPrime (P.under A)) (S := Localization.AtPrime P)
  let e := Ideal.quotEquivOfEq (map_maximalIdeal_localization_eq (A := A) P).symm
  have hsum := ringKrullDim_eq_add_ringKrullDim_closedFibre (R := Localization.AtPrime (P.under A))
    (S := Localization.AtPrime P)
  have h0A : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime (P.under A)) :=
    ringKrullDim_nonneg_of_nontrivial
  have h0F : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P ⧸
      (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [hsum] at hdim
  have hAk := (le_add_of_nonneg_right h0F).trans hdim
  have hFk := (le_add_of_nonneg_left h0A).trans hdim
  have hF : IsRegularLocalRing (primeFibreLocalRing A P) :=
    hfib P (by rw [ringKrullDim_eq_of_ringEquiv e]; exact hFk)
  exact isRegularLocalRing_of_flat_of_closedFibre (hRA (P.under A) hAk) (hF.of_ringEquiv e)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermPointIdealSpan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def HolGermPointIdealSpan.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ),
    holGermPointIdeal w = Ideal.span (Set.range fun i : σ => polyGerm w (X i - C (w i)))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

