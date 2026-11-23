module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NumberFieldApproximateIdentity
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSchwartzBruhatCompactSupportNonzero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest

open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

theorem exists_compactSupport_ne_zero :
    ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι],
      ∃ f ∈ schwartzBruhatPi (K := F) (ι := ι), HasCompactSupport f ∧ f 0 ≠ 0 := by
  intro F _ _ ι _ _
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (0 : ι → 𝔸[F])
  obtain ⟨r, -, -, hr0, hrU, hrS⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_bump (K := F) 0 U hU
  refine ⟨_, hrS, HasCompactSupport.intro hUc fun x hx => ?_, ?_⟩
  · have : r x = 0 := by
      by_contra h
      exact hx (hrU x h)
    simp [this]
  · exact_mod_cast hr0.ne'

end GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventually
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

variable {F : Type} [Field F] [NumberField F]

theorem singleV_apply_self' (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) : (singleV F v s) v = s := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v s

theorem singleV_apply_ne' (v w : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (h : w ≠ v) :
    (singleV F v s) w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) s h

theorem singleV_mul_box (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (b : Af F) :
    singleV F v s * b = singleV F v (s * b v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change (singleV F v s) w * b w = (singleV F v (s * b v)) w
  by_cases h : w = v
  · subst h
    rw [singleV_apply_self', singleV_apply_self']
  · rw [singleV_apply_ne' v w _ h, singleV_apply_ne' v w _ h, zero_mul]

open Classical in
theorem sum_singleV_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (c : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (∑ v ∈ T, singleV F v (c v)) w = if w ∈ T then c w else 0 := by
  classical
  have h1 : (∑ v ∈ T, singleV F v (c v)) w = ∑ v ∈ T, (singleV F v (c v)) w :=
    map_sum (evalV F w) _ T
  rw [h1]
  split_ifs with hw
  · rw [Finset.sum_eq_single w (fun v _ hv => singleV_apply_ne' v w _ (Ne.symm hv))
      (fun h => absurd hw h), singleV_apply_self']
  · exact Finset.sum_eq_zero fun v hv => singleV_apply_ne' v w _ (fun h => hw (h ▸ hv))

theorem singleV_mem_boxA (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hU : ∀ v, (0 : Fv F v) ∈ U v) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v)
    (hS : v ∈ S → s ∈ U v) (hO : v ∉ S → s ∈ v.adicCompletionIntegers F) :
    singleV F v s ∈ Coef.boxA S U := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hS hw
    · rw [singleV_apply_ne' v w _ h]; exact hU w
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hO hw
    · rw [singleV_apply_ne' v w _ h]; exact zero_mem _

theorem annF_boxA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  intro F _ _ ψ hψ S hS U hU
  classical
  ext b
  constructor
  · intro hb
    have key : ∀ v (s : Fv F v), (v ∈ S → s ∈ U v) → (v ∉ S → s ∈ v.adicCompletionIntegers F) →
        psiV F ψ v (s * b v) = 1 := by
      intro v s h1 h2
      have := hb _ (singleV_mem_boxA S U hU v s h1 h2)
      rwa [singleV_mul_box, psiF_singleV] at this
    refine ⟨fun v hv s hs => key v s (fun _ => hs) (fun h => absurd hv h), fun v hv => ?_⟩
    have hmem : b v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) :=
      fun s hs => key v s (fun h => absurd h hv) (fun _ => hs)
    rw [hS v hv] at hmem
    exact hmem
  · rintro ⟨hb1, hb2⟩ y ⟨hy1, hy2⟩
    obtain ⟨T, hT⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish F ψ hψ
    set c := y * b with hc
    have hcv : ∀ v, c v = y v * b v := fun v => rfl
    set T' := T ∪ S with hT'
    set e : Af F := ∑ v ∈ T', singleV F v (c v) with he
    have hcint : ∀ v, v ∉ S → c v ∈ v.adicCompletionIntegers F := fun v hv => by
      rw [hcv]; exact mul_mem (hy2 v hv) (hb2 v hv)
    have hd : psiF ψ (c - e) = 1 := by
      have happ : ∀ w, (c - e) w = c w - (if w ∈ T' then c w else 0) := fun w => by
        rw [← sum_singleV_apply T' c w]; rfl
      refine hT _ (fun w => ?_) (fun w hw => ?_)
      · rw [happ]
        split_ifs with h
        · rw [sub_self]; exact zero_mem _
        · rw [sub_zero]
          exact hcint w (fun hw => h (Finset.mem_union_right _ hw))
      · rw [happ, if_pos (Finset.mem_union_left _ hw), sub_self]
    have hsum : psiF ψ e = 1 := by
      rw [he]
      refine Finset.sum_induction _ (fun x => psiF ψ x = 1) (fun a b ha hb => by rw [psiF_add, ha, hb, one_mul])
        (psiF_zero ψ) (fun v _ => ?_)
      rw [psiF_singleV]
      by_cases hv : v ∈ S
      · rw [hcv]; exact hb1 v hv (y v) (hy1 v hv)
      · have h1 : c v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := by
          rw [hS v hv]; exact hcint v hv
        have := h1 1 (one_mem _)
        rwa [one_mul] at this
    have : c = (c - e) + e := by abel
    change psiF ψ c = 1
    rw [this, psiF_add, hd, hsum, one_mul]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NumberFieldApproximateIdentityStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_approximate_identity : ∀ (P : Type) [Fintype P] (a : P → ℝ), (∀ w, a w ≠ 0) → ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfReal.exists_bumps | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfReal.exists_bumps | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfReal.exists_bumps <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicBlockEmbeddingCompact
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Glob.MinParLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_block_of_triangular {n r s : ℕ} (X : Matrix (Fin n) (Fin r) E) (S : Finset (Fin r)) (hs : s ≤ r)
    {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular id) (e : M * adMat F X = adMat F X * B) :
    ∃ B' : Matrix (Fin s) (Fin s) (AF F ⊗[F] E),
      (B'.BlockTriangular fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) ∧
      M * adMat F (X.submatrix id (Fin.castLE hs)) = adMat F (X.submatrix id (Fin.castLE hs)) * B' := by
  refine ⟨B.submatrix (Fin.castLE hs) (Fin.castLE hs), fun i j hij => ?_, Matrix.ext fun x j => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_notMem_of_card_lt_card hij
    have hk1 := Finset.mem_filter.1 hk
    have h2 : k.val < i.val := by simpa [Fin.lt_def] using hk1.2
    have h1 : j.val ≤ k.val := by
      by_contra hc
      exact hk' (Finset.mem_filter.2 ⟨hk1.1, Fin.lt_def.2 (by simpa using not_le.1 hc)⟩)
    exact hB (show Fin.castLE hs j < Fin.castLE hs i from Fin.lt_def.2 (by simp only [Fin.val_castLE]; omega))
  · have e1 := congrFun (congrFun e x) (Fin.castLE hs j)
    have l1 : (M * adMat F (X.submatrix id (Fin.castLE hs))) x j =
        (M * adMat F X) x (Fin.castLE hs j) := rfl
    rw [l1, e1, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ (fun i hi => ?_) fun i => rfl
    have hi' : s ≤ i.val := by
      by_contra hc
      exact hi ⟨⟨i.val, not_le.1 hc⟩, rfl⟩
    have hz : B i (Fin.castLE hs j) = 0 :=
      hB (show Fin.castLE hs j < i by rw [Fin.lt_def]; simp only [Fin.val_castLE]; omega)
    rw [hz, mul_zero]

theorem minPar_eq_unip_mul_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)), ∀ p ∈ PositivityTheory.ThKR.minPar σ J X, ∃ u ∈ GlobalTheory.StdPar.unip σ J X S, ∃ l ∈ GlobalTheory.StdPar.levi σ J X Y S, p = u * l := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S p hp
  obtain ⟨s, hs, hS⟩ : ∃ s, ∃ hs : s ≤ r, ∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k := by
    refine ⟨S.sup fun k => k.val + 1, Finset.sup_le fun k _ => k.2, fun i => ?_⟩
    rw [Finset.lt_sup_iff]
    exact exists_congr fun k => and_congr_right fun _ => by rw [Fin.le_def]; omega
  obtain ⟨hu, hl, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S s hs hS
    (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) fun _ => rfl
  have hp' : p ∈ parFlag σ J (X.submatrix id (Fin.castLE hs))
      (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card) := by
    obtain ⟨B, hB, e⟩ := hp
    obtain ⟨B', hB', e'⟩ := PositivityTheory.ThKR.inv_mem_minPar h hJ hW (show p ∈ PositivityTheory.ThKR.minPar σ J X from ⟨B, hB, e⟩)
    exact ⟨exists_block_of_triangular X S hs hB e, exists_block_of_triangular X S hs hB' e'⟩
  obtain ⟨u, hu', m, hm, e, -⟩ := (_root_.GlobalTheory.LeviFlag.levi_decomposition F E σ h n J hJ s (X.submatrix id (Fin.castLE hs))
    (Y.submatrix id (Fin.castLE hs)) (fun i : Fin s => (S.filter (· < Fin.castLE hs i)).card)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).1 p hp'
  exact ⟨u, hu ▸ hu', m, hl ▸ hm, e⟩

end GlobalTheory.CompanionTheory.Glob.MinParLevi
end
end

