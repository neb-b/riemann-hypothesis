module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0052
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0050
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinates
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0051
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.SdCoord

section Gen

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def matE (M : Matrix ι ι R) (hu : IsUnit M.det) : (ι → R) ≃ₜ+ (ι → R) where
  toFun x := M *ᵥ x
  invFun x := M⁻¹ *ᵥ x
  left_inv x := by
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  right_inv x := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu]
  map_add' x y := Matrix.mulVec_add _ _ _
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem pi_smul {X : Type} [MeasurableSpace X] (lam : Measure X) [SigmaFinite lam] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • lam) = c ^ Fintype.card ι • Measure.pi fun _ : ι => lam := by
  refine (Measure.pi_eq fun s hs => ?_)
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

variable [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R]

theorem selfDual_mat (ψR : R → ℂ) (M : Matrix ι ι R) (hM : M.IsSymm) (hu : IsUnit M.det)
    (μ : Measure (ι → R)) (h : SelfDual μ (fun x y => ψR (x ⬝ᵥ y))) (c : ℝ≥0)
    (hc : μ.map (fun x => M *ᵥ x) = c • μ) :
    SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => ψR (x ⬝ᵥ (M *ᵥ y))) := by
  refine _root_.GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist (ι → R) μ (fun x y => ψR (x ⬝ᵥ y)) h (matE M hu) (fun x y => ?_) c hc
  change ψR (x ⬝ᵥ (M *ᵥ y)) = ψR ((M *ᵥ x) ⬝ᵥ y)
  congr 1
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq]

theorem iff_of (ψR : R → ℂ) (M : Matrix ι ι R) (hM : M.IsSymm) (hu : IsUnit M.det)
    (k : Measure R) [SigmaFinite k] (lam : Measure R) [SigmaFinite lam] (c₀ c : ℝ≥0)
    (hk : k = c₀ • lam)
    (h : SelfDual (Measure.pi fun _ : ι => k) (fun x y => ψR (x ⬝ᵥ y)))
    (hc : (Measure.pi fun _ : ι => k).map (fun x => M *ᵥ x) = c • Measure.pi fun _ : ι => k)
    (hU : ∀ μ ν : Measure (ι → R), SelfDual μ (fun x y => ψR (x ⬝ᵥ (M *ᵥ y))) →
      SelfDual ν (fun x y => ψR (x ⬝ᵥ (M *ᵥ y))) → μ = ν)
    (μ : Measure (ι → R)) :
    SelfDual μ (fun x y => ψR (x ⬝ᵥ (M *ᵥ y))) ↔
      μ = ((NNReal.sqrt c)⁻¹ * c₀ ^ Fintype.card ι) • Measure.pi fun _ : ι => lam := by
  have h1 := selfDual_mat ψR M hM hu _ h c hc
  have e : (NNReal.sqrt c)⁻¹ • Measure.pi (fun _ : ι => k) =
      ((NNReal.sqrt c)⁻¹ * c₀ ^ Fintype.card ι) • Measure.pi fun _ : ι => lam := by
    subst hk
    rw [pi_smul, smul_smul]
  rw [e] at h1
  exact ⟨fun h2 => hU _ _ h2 h1, fun h2 => h2 ▸ h1⟩

end Gen

theorem dot_smul {F R : Type} [Field F] [CommRing R] [Algebra F R] {ι : Type} [Fintype ι]
    (a : F) (B : Matrix ι ι F) (x y : ι → R) :
    x ⬝ᵥ ((a • B).map (algebraMap F R) *ᵥ y) =
      algebraMap F R a * (x ⬝ᵥ (B.map (algebraMap F R) *ᵥ y)) := by
  have e : (a • B).map (algebraMap F R) = algebraMap F R a • B.map (algebraMap F R) := by
    ext i j
    simp [Algebra.smul_def]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem isUnit_det_map {F R : Type} [Field F] [CommRing R] [Algebra F R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι F) (h : A.det ≠ 0) : IsUnit (A.map (algebraMap F R)).det := by
  have := (h.isUnit).map (algebraMap F R)
  rwa [RingHom.map_det] at this

section Lems
variable (F : Type) [Field F] [NumberField F]

theorem scale_inf (ψ ψ₀ : AddChar (AF F) ℂ) (a : F)
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) (s : Ainf F) :
    psiInf F ψ s = psiInf F ψ₀ (algebraMap F (Ainf F) a * s) := by
  have e : algebraMap F (AF F) a * pairA F s 0 = pairA F (algebraMap F (Ainf F) a * s) 0 :=
    Prod.ext rfl (mul_zero _)
  rw [psiInf, psiInf, h, e]

theorem scale_v (ψ ψ₀ : AddChar (AF F) ℂ) (a : F)
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    psiV F ψ v s = psiV F ψ₀ v (algebraMap F (Fv F v) a * s) := by
  classical
  have e : algebraMap F (AF F) a * pairA F 0 (singleV F v s) =
      pairA F 0 (singleV F v (algebraMap F (Fv F v) a * s)) := by
    refine Prod.ext (mul_zero _) ?_
    refine Subtype.ext (funext fun w => ?_)
    change algebraMap F (Fv F w) a * (singleV F v s) w = (singleV F v (algebraMap F (Fv F v) a * s)) w
    by_cases hw : w = v
    · subst hw
      change _ * (Pi.single w s : ∀ u : HeightOneSpectrum (𝓞 F), Fv F u) w =
        (Pi.single w (algebraMap F (Fv F w) a * s) : ∀ u : HeightOneSpectrum (𝓞 F), Fv F u) w
      simp only [Pi.single_eq_same]
    · change _ * (Pi.single v s : ∀ u : HeightOneSpectrum (𝓞 F), Fv F u) w =
        (Pi.single v (algebraMap F (Fv F v) a * s) : ∀ u : HeightOneSpectrum (𝓞 F), Fv F u) w
      simp only [Pi.single_eq_of_ne hw, mul_zero]
  rw [psiV, psiV, h, e]

end Lems

theorem selfDual_coord : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), SelfDual μ (fun x y => psiInf F ψ (x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ y))) ↔ μ = cinf • Measure.pi fun _ => laminf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), SelfDual μ (fun x y => psiV F ψ v (x ⬝ᵥ (B.map (algebraMap F (Fv F v)) *ᵥ y))) ↔ μ = c v • Measure.pi fun _ => lam v) := by
  intro F _ _ hF laminf lam hinf hlam ψ hψ ι _ _ B hB hdet
  obtain ⟨ψ₀, hψ₀, c₀, e₀, hU0, hsd0, hsdv⟩ := _root_.GlobalTheory.CompanionTheory.SW.SDOne.selfDual_std F hF laminf lam hinf hlam
  obtain ⟨a, ha, hax⟩ := GlobalTheory.CompanionTheory.SW.char_dual F ψ₀ ψ hψ₀ hψ
  have hAdet : (a • B).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ ha) hdet
  have hAs : (a • B).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_smul, hB.eq]
  obtain ⟨c₁, e₁, hU1, hm, hmv⟩ := _root_.GlobalTheory.CompanionTheory.SW.ProdFormula.modulus_matrix F ι (a • B) hAdet
  have hsq := (_root_.GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F c₁ c₁ e₁ e₁ hU1 hU1).2.2.2.2.2.1
  have hinv := (_root_.GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F _ _ _ _ hsq hsq).2.2.2.1
  have hpow := (_root_.GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F c₀ c₀ e₀ e₀ hU0 hU0).2.2.2.2.2.2.1 (Fintype.card ι)
  have hprod := (_root_.GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F _ _ _ _ hinv hpow).2.2.1
  refine ⟨_, _, hprod, ?_, fun v => ?_⟩
  · obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := isLocR_Ainf F hF
    haveI := h1; haveI := h2; haveI := h3; haveI := h4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    have hA' : ∀ x y : ι → Ainf F, psiInf F ψ (x ⬝ᵥ (B.map (algebraMap F (Ainf F)) *ᵥ y)) =
        psiInf F ψ₀ (x ⬝ᵥ ((a • B).map (algebraMap F (Ainf F)) *ᵥ y)) := by
      intro x y
      rw [scale_inf F ψ ψ₀ a hax, dot_smul]
    intro μ
    simp only [hA']
    haveI := hinf.1
    exact iff_of (psiInf F ψ₀) ((a • B).map (algebraMap F (Ainf F))) (hAs.map _)
      (isUnit_det_map _ hAdet) (c₀ • laminf) laminf c₀ c₁ rfl (_root_.GlobalTheory.CompanionTheory.SW.selfDual_pi_inf F hF ψ₀ hψ₀ _ hsd0 ι)
      (by haveI := (_root_.GlobalTheory.CompanionTheory.SW.selfDual_pi_inf F hF ψ₀ hψ₀ _ hsd0 ι).1; exact hm _ inferInstance)
      (_root_.GlobalTheory.CompanionTheory.SW.selfDual_rationalForm_Ainf_unique F hF ψ₀ hψ₀ _ hsd0 ι (a • B) hAs hAdet) μ
  · obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := h1; haveI := h2; haveI := h3; haveI := h4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hA' : ∀ x y : ι → Fv F v, psiV F ψ v (x ⬝ᵥ (B.map (algebraMap F (Fv F v)) *ᵥ y)) =
        psiV F ψ₀ v (x ⬝ᵥ ((a • B).map (algebraMap F (Fv F v)) *ᵥ y)) := by
      intro x y
      rw [scale_v F ψ ψ₀ a hax, dot_smul]
    intro μ
    simp only [hA']
    haveI := (hlam v).1
    exact iff_of (psiV F ψ₀ v) ((a • B).map (algebraMap F (Fv F v))) (hAs.map _)
      (isUnit_det_map _ hAdet) (e₀ v • lam v) (lam v) (e₀ v) (e₁ v) rfl
      (_root_.GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v F ψ₀ hψ₀ v _ (hsdv v) ι)
      (by haveI := (_root_.GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v F ψ₀ hψ₀ v _ (hsdv v) ι).1; exact hmv v _ inferInstance)
      (_root_.GlobalTheory.CompanionTheory.SW.SdUniq.selfDual_unique_coord F ψ₀ hψ₀ v _ (hsdv v) ι (a • B) hAs hAdet) μ

end GlobalTheory.CompanionTheory.SW.SdCoord
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilArchimedeanDensity
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.CountHyp

theorem size_eq_sum {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) :
    sizeTup b X = ∑ w, ∑ p, |xw e b X w p| := by
  simp only [sizeTup, sizeInf, xw, cv, he, Fintype.sum_prod_type, Fin.sum_univ_one]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem size_le {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) {R : ℝ} (hR : 0 < R)
    (h : ∀ w, ‖xw e b X w‖ ≤ R) :
    sizeTup b X ≤ ((M * d * Fintype.card (InfinitePlace F) + 1 : ℕ) : ℝ) * R := by
  rw [size_eq_sum b e he]
  have h1 : ∀ w, ∑ p, |xw e b X w p| ≤ ((M * d : ℕ) : ℝ) * R := by
    intro w
    calc ∑ p, |xw e b X w p| ≤ ∑ _p : Fin M × Fin d, R :=
          Finset.sum_le_sum fun p _ => (norm_le_pi_norm (xw e b X w) p).trans (h w)
      _ = ((M * d : ℕ) : ℝ) * R := by simp
  calc ∑ w, ∑ p, |xw e b X w p| ≤ ∑ _w : InfinitePlace F, ((M * d : ℕ) : ℝ) * R :=
        Finset.sum_le_sum fun w _ => h1 w
    _ = ((M * d * Fintype.card (InfinitePlace F) : ℕ) : ℝ) * R := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hR.le
        push_cast
        linarith

theorem ofF_ne_zero_iff {F E : Type} [Field F] [Field E] [Algebra F E] {M d : ℕ}
    (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) : ofF b x ≠ 0 ↔ x ≠ 0 := by
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · funext ⟨i, k⟩
    have h1 : ∑ k, x (i, k) • b k = 0 := congrFun (congrFun h 0) i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent (fun k => x (i, k)) h1 k
  · subst h
    funext a i
    simp [ofF]

theorem real_bound {C₀ c R : ℝ} (hc : 1 ≤ c) (hR : 0 < R) (a b : ℕ) :
    C₀ * ((c * R) ^ a + (c * R) ^ b) ≤ (|C₀| * (c ^ a + c ^ b)) * (R ^ a + R ^ b) := by
  have hc0 : 0 < c := by linarith
  have ha : 0 < c ^ a := by positivity
  have hb : 0 < c ^ b := by positivity
  have hRa : 0 < R ^ a := by positivity
  have hRb : 0 < R ^ b := by positivity
  have h1 : C₀ * ((c * R) ^ a + (c * R) ^ b) ≤ |C₀| * ((c * R) ^ a + (c * R) ^ b) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  refine h1.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [mul_pow, mul_pow]
  nlinarith [mul_pos ha hRb, mul_pos hb hRa]

theorem main_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → (∀ y w, |e y w| = ‖y w‖) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // x ≠ 0}, Set.indicator {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂(prH μ 𝓕) ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b ρ e hom hρ he μ 𝓕 hμ hF N hN
  obtain ⟨C₀, hC₀⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeanCount.mean_count_box F E σ hCM M J hJ hM d b μ 𝓕 hμ hF N hN
  set c : ℕ := M * d * Fintype.card (InfinitePlace F) + 1 with hc
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by
    have : 1 ≤ c := by omega
    exact_mod_cast this
  set a := Module.finrank ℚ F * M with ha
  set a2 := 2 * Module.finrank ℚ F * M with ha2
  refine ⟨|C₀| * ((c : ℝ) ^ a + (c : ℝ) ^ a2), fun R hR => ?_⟩

  set S : Set (Fin 1 → Fin M → AF F ⊗[F] E) :=
    {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧
      sizeTup b (projInf X) ≤ c * R} with hS
  have hmeasSize : Measurable fun X : Fin 1 → Fin M → AF F ⊗[F] E => sizeTup b (projInf X) := by
    obtain ⟨hp, -, -, -, -, -, -, -, hs⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b 1 1
    have hcont : Continuous fun y : AF F ⊗[F] E =>
        sizeInf b (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) := by
      have h := hs.comp (hp.comp (continuous_pi fun _ : Fin 1 => continuous_pi fun _ : Fin 1 =>
        (continuous_id : Continuous fun y : AF F ⊗[F] E => y)))
      simpa [Function.comp_def, sizeTup, projInf] using h
    haveI : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
    have hm := hcont.measurable
    unfold sizeTup projInf
    refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun i _ => ?_
    exact hm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hmeasS : MeasurableSet S :=
    (_root_.GlobalTheory.CompanionTheory.SW.BB.measurableSet_natMul_int F E σ hCM d M b N).inter (measurableSet_le hmeasSize measurable_const)
  have hpull := _root_.GlobalTheory.CompanionTheory.SW.BB.PullCoord.lintegral_thetaMeas_coord F E σ hCM M J hJ d b μ 𝓕 hμ hF
    {x : Fin M × Fin d → F | x ≠ 0} {X : Fin 1 → Fin M → E | X ≠ 0}
    (fun x => ofF_ne_zero_iff b x) (S.indicator fun _ => (1 : ℝ≥0∞))
    (measurable_const.indicator hmeasS)
  rw [lintegral_indicator_const hmeasS, one_mul] at hpull
  have hpt : ∀ (ω : HA (AF F) σ J) (x : {x : Fin M × Fin d → F // x ≠ 0}),
      Set.indicator {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ≤
      S.indicator (fun _ => (1 : ℝ≥0∞)) (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) := by
    intro ω x
    by_cases hA : x.1 ∈ {x : Fin M × Fin d → F | (∀ i v, ((N : Af F) * (gfin σ J b ω *ᵥ fun j => algebraMap F (Af F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf e σ J b ω w *ᵥ fun j => ρ w (x j)‖ ≤ R}
    · obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.SW.BB.RatCoord.coords_ratTup F E σ hCM M J hJ d b ρ e hρ ω x.1
      have hY : actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1)) ∈ S := by
        refine ⟨(_root_.GlobalTheory.CompanionTheory.SW.BB.Lat.natCast_mul_mem_latV_iff F E d M b N _).2 ?_, size_le b e he _ hR fun w => ?_⟩
        · rw [h2]
          exact hA.1
        · rw [h1 w]
          exact hA.2 w
      rw [Set.indicator_of_mem hA, Set.indicator_of_mem hY]
    · rw [Set.indicator_of_notMem hA]
      exact bot_le
  calc _ ≤ ∫⁻ ω, ∑' x : {x : Fin M × Fin d → F // x ≠ 0},
        S.indicator (fun _ => (1 : ℝ≥0∞)) (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) :=
        lintegral_mono fun ω => ENNReal.tsum_le_tsum fun x => hpt ω x
    _ = thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} S := hpull.symm
    _ ≤ ENNReal.ofReal (C₀ * (((c : ℝ) * R) ^ a + ((c : ℝ) * R) ^ a2)) :=
        hC₀ ((c : ℝ) * R) (mul_pos (by linarith) hR)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (real_bound hc1 hR a a2)

end GlobalTheory.CompanionTheory.SW.BB.CountHyp
end

