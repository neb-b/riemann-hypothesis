module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0002
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.AutomorphicTheory.ThetaDilations.WeilImplicationNonarchQuadratic

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateBijectionTraceForm
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem repr_ofF {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) (u : Fin 1) (i : Fin M) (k : Fin d) :
    b.repr (ofF b x u i) k = x (i, k) := by
  have h : ofF b x u i = b.equivFun.symm (fun k => x (i, k)) := by
    simp [ofF, Module.Basis.equivFun_symm_apply]
  rw [h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem ofF_bijective {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) :
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) := by
  constructor
  · intro x y hxy
    funext p
    obtain ⟨i, k⟩ := p
    rw [← repr_ofF b x 0 i k, ← repr_ofF b y 0 i k, hxy]
  · intro Y
    refine ⟨fun p => b.repr (Y 0 p.1) p.2, ?_⟩
    funext u i
    obtain rfl : u = 0 := Subsingleton.elim _ _
    exact b.sum_repr (Y 0 i)

theorem ofF_zero {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) :
    ofF b (0 : Fin M × Fin d → F) = 0 := by
  funext u i
  simp [ofF]

theorem exists_algebraMap_of_fixed {F E : Type} [Field F] [Field E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {σ : E →ₐ[F] E} (hne : σ ≠ AlgHom.id F E) {h : E}
    (hh : σ h = h) : ∃ c : F, h = algebraMap F E c := by
  by_contra hcon
  push Not at hcon
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have li : LinearIndependent F ![(1 : E), h] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hcon (-(s / t))
      have h1 : algebraMap F E t * h = -algebraMap F E s := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        linear_combination hst
      have ht' : algebraMap F E t ≠ 0 := by simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination h1
    subst ht
    simpa using hst
  have hspan : Submodule.span F (Set.range ![(1 : E), h]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by simp [h2])
  apply hne
  have hlin : σ.toLinearMap = LinearMap.id := by
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i
    · simp
    · simpa using hh
  ext y
  exact congrArg (fun f : E →ₗ[F] E => f y) hlin

theorem sigma_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  intro hσ
  have := h.2.1
  have hc := IsTotallyComplex.complexEmbedding_not_isReal τ
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa using this.symm

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigma_hE_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (y : Fin M → E) :
    σ (hE σ J y y) = hE σ J y y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (σ : E →+* E) (y j) = σ (y j) := rfl
  have h2 : (σ : E →+* E) (y i) = σ (y i) := rfl
  rw [h1, h2, sigma_sigma hσ, hJ.1 i j]
  ring

theorem ofF_gram_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    Function.Bijective (ofF b : (Fin M × Fin d → F) → Fin 1 → Fin M → E) ∧
    (∀ x : Fin M × Fin d → F, ofF b x ≠ 0 ↔ x ≠ 0) ∧
    ∀ (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F),
      (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) =
        (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ
          (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) →
      ∀ (β : F) (x : Fin M × Fin d → F),
        gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔
          (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  refine ⟨ofF_bijective b, ?_, ?_⟩
  · intro x
    rw [not_iff_not]
    constructor
    · intro h
      exact (ofF_bijective b).1 (h.trans (ofF_zero b).symm)
    · rintro rfl
      exact ofF_zero b
  · intro B hB β x
    obtain ⟨c, hc⟩ := exists_algebraMap_of_fixed hσ.2.2.1 (sigma_ne_id hσ)
      (sigma_hE_self hσ hJ (ofF b x 0))
    have hco : (fun p : Fin M × Fin d => b.repr (ofF b x 0 p.1) p.2) = x := by
      funext p
      exact repr_ofF b x 0 p.1 p.2
    have htr := hB (ofF b x 0)
    rw [hco, hc, Algebra.trace_algebraMap, hσ.2.2.1] at htr
    have hgram : gramE σ J (ofF b x) = (fun _ _ => algebraMap F E β) ↔ c = β := by
      constructor
      · intro h
        have h0 := congrFun (congrFun h 0) 0
        have h1 : hE σ J (ofF b x 0) (ofF b x 0) = algebraMap F E β := h0
        rw [hc] at h1
        exact (algebraMap F E).injective h1
      · rintro rfl
        funext u v
        obtain rfl : u = 0 := Subsingleton.elim _ _
        obtain rfl : v = 0 := Subsingleton.elim _ _
        exact hc
    rw [hgram, ← htr, nsmul_eq_mul]
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have e : (1 / 2 : F) * (((2 : ℕ) : F) * c) = c := by
      push_cast
      field_simp
    rw [e]

end GlobalTheory.CompanionTheory.SW.BB.RatCoord
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHomeomorphRankOneTuples
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section CoordMap

theorem map_curry_symm_pi {R : Type} [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam]
    (M d : ℕ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam).map
        (MeasurableEquiv.curry (Fin M) (Fin d) R).symm =
      Measure.pi fun _ : Fin M × Fin d => lam := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [(MeasurableEquiv.curry (Fin M) (Fin d) R).symm.map_apply]
  have hpre : (MeasurableEquiv.curry (Fin M) (Fin d) R).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i : Fin M => Set.pi Set.univ fun k : Fin d => s (i, k) := by
    ext x
    simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall, Function.uncurry]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem coordK_eq_map {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (e : R ⊗[F] E ≃ᵐ (Fin d → R))
    (he : ∀ y k, e y k = (Algebra.TensorProduct.basis R b).repr y k) :
    coordK R b lam = (Measure.pi fun _ => lam).map e.symm := by
  rw [MeasurableEquiv.map_symm]
  have : (e : R ⊗[F] E → Fin d → R) =
      fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k := by
    funext y k; exact he y k
  rw [coordK, this]

theorem coordMap_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ M : ℕ, IsHomeomorph (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ MeasurableEmbedding (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ (coordW R b lam 1 M).map (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) = Measure.pi fun _ : Fin M × Fin d => lam := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b lam hlam M
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hlam
  have hSF : SigmaFinite lam := inferInstance
  let e : R ⊗[F] E ≃ₜ (Fin d → R) := (hh d b).homeomorph _
  have he : ∀ y k, e y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  let em : R ⊗[F] E ≃ᵐ (Fin d → R) := e.toMeasurableEquiv
  have hem : ∀ y k, em y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  have hK : coordK R b lam = (Measure.pi fun _ => lam).map em.symm := coordK_eq_map b lam em hem
  haveI : SigmaFinite (coordK R b lam) := by
    rw [hK]; exact em.symm.measurableEmbedding.sigmaFinite_map
  have hmp : MeasurePreserving em (coordK R b lam) (Measure.pi fun _ : Fin d => lam) :=
    ⟨em.measurable, by rw [hK]; exact MeasurableEquiv.map_map_symm em⟩
  let Φ : (Fin 1 → Fin M → R ⊗[F] E) ≃ᵐ (Fin M × Fin d → R) :=
    (MeasurableEquiv.funUnique (Fin 1) (Fin M → R ⊗[F] E)).trans
      ((MeasurableEquiv.piCongrRight fun _ : Fin M => em).trans
        (MeasurableEquiv.curry (Fin M) (Fin d) R).symm)
  have hΦ : (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) = Φ := rfl
  have hsymm : (Φ.symm : (Fin M × Fin d → R) → Fin 1 → Fin M → R ⊗[F] E) =
      fun x _ i => e.symm fun k => x (i, k) := rfl
  have hc1 : Continuous (Φ : (Fin 1 → Fin M → R ⊗[F] E) → Fin M × Fin d → R) := by
    rw [← hΦ]
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2).comp
      (e.continuous.comp ((continuous_apply p.1).comp (continuous_apply 0)))
  have hc2 : Continuous (Φ.symm : (Fin M × Fin d → R) → Fin 1 → Fin M → R ⊗[F] E) := by
    rw [hsymm]
    refine continuous_pi fun _ => continuous_pi fun i => e.symm.continuous.comp ?_
    exact continuous_pi fun k => continuous_apply _
  let Ψ : (Fin 1 → Fin M → R ⊗[F] E) ≃ₜ (Fin M × Fin d → R) :=
    { Φ.toEquiv with continuous_toFun := hc1, continuous_invFun := hc2 }
  refine ⟨Ψ.isHomeomorph, Φ.measurableEmbedding, ?_⟩
  have s1 := measurePreserving_funUnique (Measure.pi fun _ : Fin M => coordK R b lam) (Fin 1)
  have s2 := measurePreserving_pi (fun _ : Fin M => coordK R b lam)
    (fun _ : Fin M => Measure.pi fun _ : Fin d => lam) (fun _ => hmp)
  have h12 := s2.comp s1
  rw [hΦ, ← map_curry_symm_pi lam M d, ← h12.map_eq,
    Measure.map_map (MeasurableEquiv.curry (Fin M) (Fin d) R).symm.measurable h12.measurable]
  rfl

end CoordMap

end GlobalTheory.CompanionTheory.SW.BB
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsNormOneUnitShift
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LamUnit

theorem conj_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

theorem fixed_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (a : E) : σ a = a ↔ a ∈ (algebraMap F E).range := by
  constructor
  · intro ha
    by_contra hnot
    have hli : LinearIndependent F ![(1 : E), a] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have ht : t = 0 := by
        by_contra ht
        apply hnot
        refine ⟨-(s / t), ?_⟩
        have ht' : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
        have h1 : algebraMap F E s + algebraMap F E t * a = 0 := by
          simpa [Algebra.smul_def] using hst
        rw [map_neg, map_div₀]
        field_simp
        linear_combination -h1
      subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [h.2.2.1])
    apply conj_ne_id h
    have hlin : σ.toLinearMap = (AlgHom.id F E).toLinearMap := by
      refine LinearMap.ext_on hspan ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp
      · simpa using ha
    ext x
    exact LinearMap.congr_fun hlin x
  · rintro ⟨c, rfl⟩
    exact σ.commutes c

theorem exists_norm_one_sub_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R],
    PIW.AdelicOrbitU.UnitChoice R → ∀ (t : R ⊗[F] E) (β : Rˣ), ∃ lam : R ⊗[F] E,
      lam * sigR R σ lam = 1 ∧ IsUnit (algebraMap R (R ⊗[F] E) (β : R) - sigR R σ lam * t) := by
  intro F E _ _ _ _ _ σ hcm R _ _ hU t β
  obtain ⟨lam, h1, h2⟩ := PIW.AdelicOrbitU.stLam F E σ hcm.2.2.1 (fixed_iff hcm) R hU
    (algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) * t) 1 one_ne_zero
  refine ⟨lam, h1, ?_⟩
  have hb : IsUnit (algebraMap R (R ⊗[F] E) (β : R)) := β.isUnit.map _
  have hinv : algebraMap R (R ⊗[F] E) (β : R) * algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have key : algebraMap R (R ⊗[F] E) (β : R) - sigR R σ lam * t =
      algebraMap R (R ⊗[F] E) (β : R) * (algebraMap F (R ⊗[F] E) 1 -
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ lam * (algebraMap R (R ⊗[F] E) ((β⁻¹ : Rˣ) : R) * t)) := by
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ lam = sigR R σ lam := rfl
    rw [map_one, hs]
    linear_combination (sigR R σ lam * t) * hinv
  rw [key]
  exact hb.mul h2

end GlobalTheory.CompanionTheory.SW.LamUnit
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsRealFlowAdelicUnits
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Flow

theorem continuous_tmul_one (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (fun a : AF F => a ⊗ₜ[F] (1 : E)) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  let φ : AF F →ₗ[AF F] AF F ⊗[F] E :=
    (TensorProduct.AlgebraTensorModule.mk F (AF F) (AF F) E).flip (1 : E)
  exact IsModuleTopology.continuous_of_linearMap φ

theorem exists_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ := by
  intro F E _ _ _ _ _ σ hCM
  obtain ⟨θ, hθ⟩ := (_root_.GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding F hCM.1).1
  let g : ℝ → AF F ⊗[F] E := fun x => pairA F (θ (Real.exp x)) 1 ⊗ₜ[F] (1 : E)
  have g0 : g 0 = 1 := by
    simp only [g, Real.exp_zero, map_one]
    rfl
  have gadd : ∀ x y, g (x + y) = g x * g y := by
    intro x y
    have h : pairA F (θ (Real.exp x) * θ (Real.exp y)) 1 =
        pairA F (θ (Real.exp x)) 1 * pairA F (θ (Real.exp y)) 1 :=
      Prod.ext rfl (mul_one (1 : Af F)).symm
    simp only [g, Real.exp_add, map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, h]
  have gc : Continuous g := by
    refine (continuous_tmul_one F E).comp ?_
    show Continuous fun x : ℝ => ((θ (Real.exp x), 1) : AF F)
    exact (hθ.comp Real.continuous_exp).prodMk continuous_const
  let f : Multiplicative ℝ →* AF F ⊗[F] E :=
    { toFun := fun x => g x.toAdd
      map_one' := g0
      map_mul' := fun x y => gadd x.toAdd y.toAdd }
  refine ⟨f.toHomUnits, ?_, θ, hθ, fun x => rfl⟩
  rw [Units.continuous_iff]
  constructor
  · exact gc.comp continuous_toAdd
  · have : (fun x : Multiplicative ℝ => (((f.toHomUnits x)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) =
        fun x => g (-x.toAdd) := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact gc.comp (continuous_neg.comp continuous_toAdd)

end GlobalTheory.CompanionTheory.SW.Flow
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicLatticeMembershipIff
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.Lat

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem repr_map_evalV {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (y : Af F ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr
        (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) y) k =
      evalV F v ((Algebra.TensorProduct.basis (Af F) b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem repr_natCast_mul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (a : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((a : R ⊗[F] E) * y) k =
      (a : R) * (Algebra.TensorProduct.basis R b).repr y k := by
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem natCast_mul_mem_latV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (d M : ℕ) (b : Module.Basis (Fin d) F E) (a : ℕ) (X : Fin 1 → Fin M → Af F ⊗[F] E),
    (∀ v, (fun p i => (a : Fv F v ⊗[F] E) * projV v X p i) ∈ latV b v) ↔
      ∀ i v, ((a : Af F) * cv (Af F) b (X 0) i) v ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ d M b a X
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (p : Fin 1) (i : Fin M) (k : Fin d),
      (Algebra.TensorProduct.basis (Fv F v) b).repr ((a : Fv F v ⊗[F] E) * projV v X p i) k =
        ((a : Af F) * cv (Af F) b (X 0) (i, k)) v := by
    intro v p i k
    obtain rfl : p = 0 := Subsingleton.elim _ _
    rw [repr_natCast_mul]
    have h := repr_map_evalV b v (X 0 i) k
    simp only [projV, h, cv]
    have h2 : ((a : Af F) * (Algebra.TensorProduct.basis (Af F) b).repr (X 0 i) k) v =
        evalV F v ((a : Af F) * (Algebra.TensorProduct.basis (Af F) b).repr (X 0 i) k) := rfl
    rw [h2, map_mul, map_natCast]
  constructor
  · rintro h ⟨i, k⟩ v
    rw [← key v 0 i k]
    exact h v 0 i k
  · intro h v p i k
    change (Algebra.TensorProduct.basis (Fv F v) b).repr ((a : Fv F v ⊗[F] E) * projV v X p i) k ∈ _
    rw [key v p i k]
    exact h (i, k) v

end GlobalTheory.CompanionTheory.SW.BB.Lat
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierInversionSchwartzBruhat
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.FouSB

theorem fou_sb : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.Tgt.c_fou_sb

end GlobalTheory.CompanionTheory.SW.FouSB
end

