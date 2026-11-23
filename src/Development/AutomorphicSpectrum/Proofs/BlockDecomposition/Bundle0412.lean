module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0283
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianValuationSplitCriterion
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin.EvenAniso

section Form

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R}

theorem add_left (hH : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hH.symm z (x + y), hH.add_right, map_add (f := _), ← hH.symm z x, ← hH.symm z y]

theorem smul_left (hH : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [hH.symm y (a • x), hH.smul_right, map_mul, ← hH.symm y x]

theorem zero_left (hH : IsHerm c h) (y : V) : h 0 y = 0 := by
  rw [← zero_smul R (0 : V), smul_left hH, map_zero, zero_mul]

theorem zero_right (hH : IsHerm c h) (x : V) : h x 0 = 0 := by
  rw [← zero_smul R (0 : V), hH.smul_right, zero_mul]

end Form

theorem le_one_of_mul_self {γ : ℝ≥0} (h : γ * γ ≤ 1) : γ ≤ 1 := by
  by_contra hc
  have hg : 1 < γ := not_le.mp hc
  have hgg : 1 < γ * γ := by
    calc (1 : ℝ≥0) = 1 * 1 := (one_mul 1).symm
      _ < γ * γ := mul_lt_mul'' hg hg zero_le zero_le
  exact absurd h (not_le.mpr hgg)

theorem pair_mem_of_even : ∀ {k R V : Type} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] (c : R →+* R) (𝔬 : Subring R) (W : Valuation R ℝ≥0), (∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1) → (∀ a, c (c a) = a) → (∀ a, c a = a → ∃ x : k, algebraMap k R x = a) → (∀ x : k, c (algebraMap k R x) = algebraMap k R x) → (∀ a, a ∈ 𝔬 ↔ W a ≤ 1) → (∀ a, W (c a) = W a) → (∀ a, W a = 0 → a = 0) → (∀ e : k, W (algebraMap k R e) < 1 → ∃ u : k, u * u + u + e = 0) → ∀ h : V → V → R, IsHerm c h → (∀ z, h z z = 0 → z = 0) → ∀ (z w : V) (a b : R), a ∈ 𝔬 → b ∈ 𝔬 → h z z = a + c a → h w w = b + c b → h z w ∈ 𝔬 := by
  intro k R V _ _ _ _ _ c 𝔬 W hinv hcc hfix hck h𝔬 hWc hW0 hhen h hH hanis z w a b ha hb hzz hww
  rw [h𝔬]
  by_contra hlt
  have hs1 : 1 < W (h z w) := not_le.mp hlt
  have hsym : ∀ x y : V, h y x = c (h x y) := hH.symm
  have hself : ∀ x : V, c (h x x) = h x x := fun x => (hH.symm x x).symm
  have hWnorm : ∀ x : R, W (x * c x) = W x * W x := fun x => by rw [W.map_mul, hWc]
  have hWtr : ∀ x : R, W x ≤ 1 → W (x + c x) ≤ 1 := fun x hx =>
    le_trans (W.map_add x (c x)) (max_le hx (by rw [hWc]; exact hx))
  have hne : ∀ x : R, x ≠ 0 → W x ≠ 0 := fun x hx h0 => hx (hW0 x h0)
  have hnz : ∀ z w : V, 1 < W (h z w) → h z z ≠ 0 ∧ h w w ≠ 0 := by
    intro z w hs
    constructor
    · intro h0
      rw [hanis z h0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH, W.map_zero] at hs
      exact absurd hs (not_lt.mpr zero_le)
    · intro h0
      rw [hanis w h0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_right hH, W.map_zero] at hs
      exact absurd hs (not_lt.mpr zero_le)
  have core : ∀ (z w : V) (a b : R), W a ≤ 1 → W b ≤ 1 → h z z = a + c a → h w w = b + c b →
      1 < W (h z w) →
      W (a * c a * h w w) < W (h z w * c (h z w) * h z z) → False := by
    intro z w a b ha hb hzz hww hs hlt'
    obtain ⟨hA, hB⟩ := hnz z w hs
    have hs0 : W (h z w) ≠ 0 := (lt_trans zero_lt_one hs).ne'
    have hA0 : W (h z z) ≠ 0 := hne _ hA
    have hB0 : W (h w w) ≠ 0 := hne _ hB
    have ha0 : W a ≠ 0 := by
      intro h0
      apply hA
      rw [hzz, hW0 a h0, map_zero, add_zero]
    have hD : h z w * c (h z w) * h z z ≠ 0 := by
      intro h0
      have h0' := congrArg W h0
      rw [W.map_zero, W.map_mul, hWnorm] at h0'
      exact mul_ne_zero (mul_ne_zero hs0 hs0) hA0 h0'
    obtain ⟨Dinv, hDinv⟩ := hinv _ hD
    have hcD : c (h z w * c (h z w) * h z z) = h z w * c (h z w) * h z z := by
      rw [map_mul, map_mul, hcc, hself z]; ring
    have hcDinv : c Dinv = Dinv := by
      have h1 : (h z w * c (h z w) * h z z) * c Dinv = 1 := by
        rw [← hcD, ← map_mul, hDinv, map_one]
      calc c Dinv = c Dinv * ((h z w * c (h z w) * h z z) * Dinv) := by rw [hDinv, mul_one]
        _ = ((h z w * c (h z w) * h z z) * c Dinv) * Dinv := by ring
        _ = Dinv := by rw [h1, one_mul]
    have hce : c (a * c a * h w w * Dinv) = a * c a * h w w * Dinv := by
      rw [map_mul, map_mul, map_mul, hcc, hself w, hcDinv]; ring
    obtain ⟨e', he'⟩ := hfix _ hce
    have hWDD : W (h z w * c (h z w) * h z z) * W Dinv = 1 := by
      rw [← W.map_mul, hDinv, W.map_one]
    have hWDinv : 0 < W Dinv := by
      rcases (zero_le : (0 : ℝ≥0) ≤ W Dinv).lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0, mul_zero] at hWDD
        exact absurd hWDD zero_ne_one
    have hWe : W (algebraMap k R e') < 1 := by
      rw [he', W.map_mul, ← hWDD]
      exact mul_lt_mul_of_pos_right hlt' hWDinv
    obtain ⟨m, hm⟩ := hhen e' hWe
    have hM' : algebraMap k R m * algebraMap k R m + algebraMap k R m + a * c a * h w w * Dinv = 0 := by
      have hm' := congrArg (algebraMap k R) hm
      rw [map_add (f := _), map_add (f := _), map_mul, map_zero, he'] at hm'
      exact hm'
    have hcM' : c (algebraMap k R m) = algebraMap k R m := hck m
    obtain ⟨M, hMdef⟩ : ∃ M, algebraMap k R m = M := ⟨_, rfl⟩
    rw [hMdef] at hM' hcM'
    have hkey : (M * M + M) * (h z w * c (h z w) * h z z) + a * c a * h w w = 0 := by
      linear_combination (h z w * c (h z w) * h z z) * hM' - (a * c a * h w w) * hDinv
    have hv : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w)
        ((c a * h w w) • z + (h z z * M * c (h z w)) • w) = 0 := by
      simp only [GlobalTheory.CompanionTheory.KFin.EvenAniso.add_left hH, hH.add_right,
        GlobalTheory.CompanionTheory.KFin.EvenAniso.smul_left hH, hH.smul_right, map_mul, hcc, hself, hcM']
      rw [hsym z w]
      linear_combination (h z z * h w w) * hkey - (h z z * h w w * M * h z w * c (h z w)) * hzz
    have hv0 := hanis _ hv
    have e1 : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w) w = 0 := by
      rw [hv0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH]
    have e2 : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w) z = 0 := by
      rw [hv0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH]
    simp only [GlobalTheory.CompanionTheory.KFin.EvenAniso.add_left hH, GlobalTheory.CompanionTheory.KFin.EvenAniso.smul_left hH, map_mul,
      hcc, hself, hcM'] at e1 e2
    rw [hsym z w] at e2
    have hfac1 : h w w * h z w * (a + h z z * M) = 0 := by linear_combination e1
    have hfac2 : h z z * (a * h w w + M * (h z w * c (h z w))) = 0 := by linear_combination e2
    have f1 : a + h z z * M = 0 := by
      apply hW0
      have h0' := congrArg W hfac1
      rw [W.map_zero, W.map_mul, W.map_mul] at h0'
      exact (mul_eq_zero.mp h0').resolve_left (mul_ne_zero hB0 hs0)
    have f2 : a * h w w + M * (h z w * c (h z w)) = 0 := by
      apply hW0
      have h0' := congrArg W hfac2
      rw [W.map_zero, W.map_mul] at h0'
      exact (mul_eq_zero.mp h0').resolve_left hA0
    have g1 : W a = W (h z z) * W M := by
      rw [eq_neg_of_add_eq_zero_left f1, W.map_neg, W.map_mul]
    have g2 : W a * W (h w w) = W M * (W (h z w) * W (h z w)) := by
      rw [← W.map_mul a (h w w), eq_neg_of_add_eq_zero_left f2, W.map_neg, W.map_mul, hWnorm]
    have hM0 : W M ≠ 0 := fun h0 => ha0 (by rw [g1, h0, mul_zero])
    have g3 : W (h z w) * W (h z w) = W (h z z) * W (h w w) := by
      apply mul_left_cancel₀ hM0
      rw [← g2, g1]; ring
    have hAle : W (h z z) ≤ 1 := by rw [hzz]; exact hWtr a ha
    have hBle : W (h w w) ≤ 1 := by rw [hww]; exact hWtr b hb
    have hss : W (h z w) * W (h z w) ≤ 1 := by
      rw [g3]
      calc W (h z z) * W (h w w) ≤ 1 * 1 := mul_le_mul hAle hBle zero_le zero_le
        _ = 1 := one_mul 1
    exact absurd hs (not_lt.mpr (GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self hss))
  have ha1 : W a ≤ 1 := (h𝔬 a).mp ha
  have hb1 : W b ≤ 1 := (h𝔬 b).mp hb
  rcases lt_or_ge (W (a * c a * h w w)) (W (h z w * c (h z w) * h z z)) with hc1 | hc1
  · exact core z w a b ha1 hb1 hzz hww hs1 hc1
  have hs2 : 1 < W (h w z) := by rw [hsym z w, hWc]; exact hs1
  rcases lt_or_ge (W (b * c b * h z z)) (W (h w z * c (h w z) * h w w)) with hc2 | hc2
  · exact core w z b a hb1 ha1 hww hzz hs2 hc2
  obtain ⟨hA, hB⟩ := hnz z w hs1
  have hA0 : W (h z z) ≠ 0 := hne _ hA
  have hB0 : W (h w w) ≠ 0 := hne _ hB
  rw [hsym z w] at hc2
  simp only [W.map_mul, hWc] at hc1 hc2
  have hm1 : ∀ x y : ℝ≥0, x ≤ 1 → y ≤ 1 → x * y ≤ 1 := fun x y hx hy => by
    calc x * y ≤ 1 * 1 := mul_le_mul hx hy zero_le zero_le
      _ = 1 := one_mul 1
  have hprod := mul_le_mul hc1 hc2 zero_le zero_le
  have hAB : 0 < W (h z z) * W (h w w) := pos_iff_ne_zero.mpr (mul_ne_zero hA0 hB0)
  have h4 : W (h z w) * W (h z w) * (W (h z w) * W (h z w)) ≤ W a * W a * (W b * W b) := by
    refine le_of_mul_le_mul_right ?_ hAB
    calc W (h z w) * W (h z w) * (W (h z w) * W (h z w)) * (W (h z z) * W (h w w))
        = W (h z w) * W (h z w) * W (h z z) * (W (h z w) * W (h z w) * W (h w w)) := by ring
      _ ≤ W a * W a * W (h w w) * (W b * W b * W (h z z)) := hprod
      _ = W a * W a * (W b * W b) * (W (h z z) * W (h w w)) := by ring
  have h5 := le_trans h4 (hm1 _ _ (hm1 _ _ ha1 ha1) (hm1 _ _ hb1 hb1))
  have h6 := GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self (GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self h5)
  exact absurd hs1 (not_lt.mpr h6)

end GlobalTheory.CompanionTheory.KFin.EvenAniso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralLinearChangeModulus
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BZPhiPG.Scale

theorem sr1_field (k : Type) [Field k] : GlobalTheory.HaarLin.HasStableRangeOne k := by
  intro a b h
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      exact not_isCoprime_zero_zero h
    exact ⟨b⁻¹, by simp [hb]⟩
  · exact ⟨0, by simp [ha]⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isAddHaar_muD (t : ℕ) : @Measure.IsAddHaarMeasure _ _ _ (_root_.borel _) (muD k t) := by
  letI : MeasurableSpace (Fin t → k) := _root_.borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem map_muD (t : ℕ) (A : GL (Fin t) k) :
    @Measure.map _ _ (_root_.borel _) (_root_.borel _) (fun d : Fin t → k => (A⁻¹ : GL (Fin t) k).val *ᵥ d) (muD k t) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det A)) • muD k t := by
  haveI : SecondCountableTopology k := GlobalTheory.HaarScaleMatrix.secondCountable_of_localField k
  have h := GlobalTheory.HaarLin.map_mulVec_of_mem_TD k (Fin t) (A⁻¹ : GL (Fin t) k).val
    (GlobalTheory.HaarLin.Gauss.mem_TD_of_isUnit_det k (sr1_field k) (Fin t) _
      (Matrix.GeneralLinearGroup.det (A⁻¹ : GL (Fin t) k)).isUnit)
    (Matrix.GeneralLinearGroup.det (A⁻¹ : GL (Fin t) k)) rfl (muD k t) (isAddHaar_muD t)
  rw [h, map_inv, map_inv, inv_inv]

theorem val_dpow_one (t : ℕ) (A : GL (Fin t) k) :
    ((dpow t 1 A : ℂˣ) : ℂ) = ((distribHaarChar k (Matrix.GeneralLinearGroup.det A) : ℝ) : ℂ) := by
  show ((absPow k (((1 : ℝ)) : ℂ) (Matrix.GeneralLinearGroup.det A) : ℂˣ) : ℂ) = _
  rw [val_absPow, Complex.ofReal_one, Complex.cpow_one]
  rfl

theorem smInt_mulVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (A : GL (Fin t) k) (φ : (Fin t → k) → W)
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) (fun d => φ ((A⁻¹ : GL (Fin t) k).val *ᵥ d)) =
      ((dpow t 1 A : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (_root_.borel _) _ _ (muD k t) φ := by
  classical
  letI : MeasurableSpace (Fin t → k) := _root_.borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  haveI : (muD k t).IsAddHaarMeasure := isAddHaar_muD t
  set f : (Fin t → k) → (Fin t → k) := fun d => (A⁻¹ : GL (Fin t) k).val *ᵥ d with hf
  have fc : Continuous f := Continuous.matrix_mulVec continuous_const continuous_id
  have fm : Measurable f := fc.measurable
  set a : NNReal := distribHaarChar k (Matrix.GeneralLinearGroup.det A) with ha
  have hmeas : ∀ y : W, muD k t ((φ ∘ f) ⁻¹' {y}) = a • muD k t (φ ⁻¹' {y}) := by
    intro y
    have hS : MeasurableSet (φ ⁻¹' {y}) := (l.isOpen_fiber y).measurableSet
    rw [Set.preimage_comp, ← Measure.map_apply fm hS, map_muD t A]
    rfl
  let S : Finset W := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.finite_range l c).toFinset
  have hS : ∀ x, φ x ∈ S := fun x => (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩
  have e₀ : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) (id ∘ (φ ∘ f)) =
      ∑ y ∈ S, ((((muD k t) ((φ ∘ f) ⁻¹' {y})).toReal : ℝ) : ℂ) • id y :=
    GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp (muD k t) (φ ∘ f) id S (fun x => hS _)
      (fun y _ => ((l.comp_continuous fc).isOpen_fiber y).measurableSet)
      (fun y _ hy => by
        rw [hmeas y]
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top (GlobalTheory.CompanionTheory.Rodier.SmIntEl.measure_level_ne_top _ c hy))
  have e₁ : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) (id ∘ φ) =
      ∑ y ∈ S, ((((muD k t) (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • id y :=
    GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp (muD k t) φ id S hS
      (fun y _ => (l.isOpen_fiber y).measurableSet)
      (fun y _ hy => GlobalTheory.CompanionTheory.Rodier.SmIntEl.measure_level_ne_top _ c hy)
  have e₀' : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) (fun d => φ (f d)) = _ := e₀
  have e₁' : GlobalTheory.CompanionTheory.Rodier.smInt (muD k t) φ = _ := e₁
  rw [val_dpow_one]
  refine e₀'.trans ?_
  rw [e₁', Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hmeas y, ENNReal.toReal_smul, smul_smul]
  congr 1
  simp [NNReal.smul_def, ← ha]

end GlobalTheory.CompanionTheory.BZPhiPG.Scale

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterpolationLocalL2Bound
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.InterpLoc

theorem exists_finset_separating {Y : Type} (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ] :
    ∃ t : Finset Y, ∀ ψ ∈ Ψ, (∀ y ∈ t, ψ y = 0) → ψ = 0 := by
  classical
  let K : Finset Y → Submodule ℂ (Y → ℂ) := fun t =>
    { carrier := {ψ | ψ ∈ Ψ ∧ ∀ y ∈ t, ψ y = 0}
      add_mem' := fun {a b} ha hb =>
        ⟨Ψ.add_mem ha.1 hb.1, fun y hy => by simp [ha.2 y hy, hb.2 y hy]⟩
      zero_mem' := ⟨Ψ.zero_mem, fun _ _ => rfl⟩
      smul_mem' := fun c a ha =>
        ⟨Ψ.smul_mem c ha.1, fun y hy => by simp [ha.2 y hy]⟩ }
  have hKle : ∀ t, K t ≤ Ψ := fun t _ h => h.1
  haveI : ∀ t, FiniteDimensional ℂ (K t) := fun t => Submodule.finiteDimensional_of_le (hKle t)
  let f : Finset Y → ℕ := fun t => Module.finrank ℂ (K t)
  refine ⟨Function.argmin f, fun ψ hψ h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  set t := Function.argmin f with ht
  have hlt : K (insert y t) < K t := by
    refine lt_of_le_of_ne (fun a ha => ⟨ha.1, fun z hz => ha.2 z (Finset.mem_insert_of_mem hz)⟩) ?_
    intro heq
    have hmem : ψ ∈ K t := ⟨hψ, h0⟩
    rw [← heq] at hmem
    exact hy (hmem.2 y (Finset.mem_insert_self y t))
  have h1 : f (insert y t) < f t := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : f t ≤ f (insert y t) := Function.argmin_le f _
  omega

theorem bound_of_injective {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ]
    (hm : ∀ ψ ∈ Ψ, MemLp ψ 2 μ) (hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[μ] 0 → ψ = 0) (y₀ : Y) :
    ∃ C : NNReal, ∀ ψ ∈ Ψ, ‖ψ y₀‖ₑ ^ 2 ≤ C * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
  let T : Ψ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun ψ => (hm ψ.1 ψ.2).toLp ψ.1
      map_add' := fun a b => MemLp.toLp_add (hm a.1 a.2) (hm b.1 b.2)
      map_smul' := fun c a => MemLp.toLp_const_smul c (hm a.1 a.2) }
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ψ hψ
    have h0 : ψ.1 =ᵐ[μ] 0 := (MemLp.toLp_eq_toLp_iff (hm ψ.1 ψ.2) MemLp.zero).1 (by
      rw [MemLp.toLp_zero]; exact hψ)
    exact Subtype.ext (hinj ψ.1 ψ.2 h0)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hker
  let ev : Ψ →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => ψ.1 y₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ℓ : LinearMap.range T →ₗ[ℂ] ℂ := (ev ∘ₗ g).domRestrict (LinearMap.range T)
  let L : LinearMap.range T →L[ℂ] ℂ := ⟨ℓ, LinearMap.continuous_of_finiteDimensional ℓ⟩
  refine ⟨‖L‖₊ ^ 2, fun ψ hψ => ?_⟩
  let p : Ψ := ⟨ψ, hψ⟩
  have hL : L ⟨T p, LinearMap.mem_range_self T p⟩ = ψ y₀ := by
    change ev (g (T p)) = ψ y₀
    have : g (T p) = p := LinearMap.congr_fun hg p
    rw [this]; rfl
  have hb : ‖ψ y₀‖₊ ≤ ‖L‖₊ * ‖T p‖₊ := by
    rw [← hL]
    exact L.le_opNNNorm _
  have hen : ‖T p‖ₑ = eLpNorm ψ 2 μ := Lp.enorm_toLp (hm ψ hψ)
  have hb' : ‖ψ y₀‖ₑ ≤ (‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ := by
    rw [← hen]
    simp only [enorm_eq_nnnorm]
    exact_mod_cast hb
  have hsq : eLpNorm ψ 2 μ ^ 2 = ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (f := ψ) (μ := μ) (p := 2) (by norm_num)
      (hm ψ hψ).aestronglyMeasurable
    simpa using this
  calc ‖ψ y₀‖ₑ ^ 2 ≤ ((‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ) ^ 2 := by gcongr
    _ = ((‖L‖₊ ^ 2 : NNReal) : ENNReal) * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
      rw [mul_pow, hsq]; push_cast; rfl

theorem interpolation_local_L2_bound : PositivityTheory.Rg.BcB.E.E3.InterpolationL2Bound := by
  intro X Y _ _ _ _ _ ν _ _ F hF hfin
  set Ψ : Submodule ℂ (Y → ℂ) := Submodule.span ℂ (Set.range F) with hΨ
  haveI : FiniteDimensional ℂ Ψ := hfin
  have hc : ∀ ψ ∈ Ψ, Continuous ψ := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; exact hF i
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  obtain ⟨t, ht⟩ := exists_finset_separating Ψ
  choose N hNc hNn using fun y : Y => exists_compact_mem_nhds y
  have hΩ : IsCompact (⋃ y ∈ t, N y) := t.isCompact_biUnion fun y _ => hNc y
  set Ω : Set Y := ⋃ y ∈ t, N y with hΩdef
  refine ⟨Ω, hΩ, fun y₀ => ?_⟩
  haveI : IsFiniteMeasure (ν.restrict Ω) := ⟨by simpa using hΩ.measure_lt_top⟩
  have hm : ∀ ψ ∈ Ψ, MemLp ψ 2 (ν.restrict Ω) := by
    intro ψ hψ
    obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn (hc ψ hψ).continuousOn
    refine MemLp.of_bound (hc ψ hψ).aestronglyMeasurable B ?_
    have hmeas : MeasurableSet Ω := hΩ.measurableSet
    exact (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hB)
  have hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[ν.restrict Ω] 0 → ψ = 0 := by
    intro ψ hψ h0
    refine ht ψ hψ fun y hy => ?_
    have hsub : interior (N y) ⊆ Ω := interior_subset.trans (Set.subset_biUnion_of_mem (u := N) hy)
    have h1 : ψ =ᵐ[ν.restrict (interior (N y))] 0 :=
      ae_mono (Measure.restrict_mono hsub le_rfl) h0
    have h2 := Measure.eqOn_open_of_ae_eq h1 isOpen_interior (hc ψ hψ).continuousOn
      continuousOn_const
    exact h2 (mem_interior_iff_mem_nhds.2 (hNn y))
  obtain ⟨C, hC⟩ := bound_of_injective (ν.restrict Ω) Ψ hm hinj y₀
  exact ⟨C, fun x => hC (F x) (Submodule.subset_span ⟨x, rfl⟩)⟩

end GlobalTheory.CompanionTheory.InterpLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntersectionNumberPolynomial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.ChernPoly

theorem inter_add_nsmul_polynomial :
    ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv), ∃ Q : Polynomial ℝ, ∀ m : ℕ,
      ((Y.inter fun _ => Δ + m • Δ₀ : ℤ) : ℝ) = Q.eval (m : ℝ) := by
  intro Y Δ Δ₀
  classical
  refine ⟨∑ s : Finset (Fin Y.dim),
    Polynomial.C ((Y.interForm (s.piecewise (fun _ => Δ₀) (fun _ => Δ)) : ℤ) : ℝ) * Polynomial.X ^ s.card,
    fun m => ?_⟩
  have h1 : (fun _ : Fin Y.dim => Δ + m • Δ₀) = (fun _ => (m : ℤ) • Δ₀) + (fun _ => Δ) := by
    funext i
    rw [Pi.add_apply, natCast_zsmul, add_comm]
  rw [← Y.interForm_apply, h1, MultilinearMap.map_add_univ]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : (s.piecewise (fun i => (m : ℤ) • s.piecewise (fun _ => Δ₀) (fun _ => Δ) i)
      (s.piecewise (fun _ => Δ₀) (fun _ => Δ))) = s.piecewise (fun _ => (m : ℤ) • Δ₀) (fun _ => Δ) := by
    funext i
    by_cases hi : i ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ hi,
        Finset.piecewise_eq_of_mem _ _ _ hi]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi,
        Finset.piecewise_eq_of_notMem _ _ _ hi]
  have key := Y.interForm.map_piecewise_smul (fun _ => (m : ℤ)) (s.piecewise (fun _ => Δ₀) (fun _ => Δ)) s
  rw [hpw, Finset.prod_const, smul_eq_mul] at key
  rw [key]
  push_cast
  simp only [id_eq]
  push_cast
  ring

end GlobalTheory.CompanionTheory.ChernPoly
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerEqZeroOfVanishOnHighest
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem intertwiner_eq_zero_of_highest {n : ℕ} (H V : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [AddCommGroup V] [Module ℂ V]
    (G : Fin n → Fin n → Module.End ℂ H) (D : Fin n → Fin n → Module.End ℂ V)
    (hrel : Formalism.REAL.GlRel G)
    (hadj : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (R : H →ₗ[ℂ] V) (hR : ∀ a b w, R (G a b w) = D a b (R w))
    (hhigh : ∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v → R v = 0) :
    R = 0 := by
  by_contra hne
  have hKtop : LinearMap.ker R ≠ ⊤ := fun h => hne (LinearMap.ker_eq_top.mp h)
  have hN : (LinearMap.ker R)ᗮ ≠ ⊥ := fun h =>
    hKtop ((Submodule.orthogonal_eq_bot_iff).mp h)
  have hstable : ∀ a b, ∀ w ∈ (LinearMap.ker R)ᗮ, G a b w ∈ (LinearMap.ker R)ᗮ := by
    intro a b w hw
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' : G b a u ∈ LinearMap.ker R := by
      rw [LinearMap.mem_ker] at hu ⊢
      rw [hR, hu, map_zero]
    rw [← hadj]
    exact (Submodule.mem_orthogonal _ _).mp hw _ hu'
  obtain ⟨μ, v, hvN, hv0, hk⟩ := _root_.GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable H G hrel hadj _ hN hstable
  have hvK : v ∈ LinearMap.ker R := hhigh μ v hk
  exact hv0 (inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp hvN v hvK))

end GlobalTheory.CompanionTheory.RealCountG
end

