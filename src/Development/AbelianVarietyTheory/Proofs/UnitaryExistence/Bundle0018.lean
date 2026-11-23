module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHostNormModCoprimeLevelHalf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureHermitianModelOfDatum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCuspPseudoBasisAdaptedLattice
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem herm_comb_eq_zero_of_iso {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (e : Fin ρ → Fin r → E)
    (h : ∀ a b, herm G (e a) (e b) = 0) (u v : Fin ρ → E) :
    herm G (∑ i, u i • e i) (∑ j, v j • e j) = 0 := by
  have key : herm G (∑ i, u i • e i) (∑ j, v j • e j)
      = ∑ i, ∑ j, u i * cc (v j) * herm G (e i) (e j) := by
    have h1 : ∀ (y : Fin r → E), herm G (∑ i, u i • e i) y = ∑ i, u i * herm G (e i) y := by
      intro y
      simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∀ (x : Fin r → E), herm G x (∑ j, v j • e j) = ∑ j, cc (v j) * herm G x (e j) := by
      intro x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [herm, cc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin ρ)))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp only [h1, h2, Finset.mul_sum, mul_assoc]
  rw [key]
  simp [h]

theorem exists_cusp_pseudoBasis :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu₀ : FJ.CuspFD X ρ), ∃ (cu : FJ.CuspFD X ρ) (P : Matrix (Fin ρ) (Fin ρ) E) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), IsUnit P.det ∧ (∀ a, cu₀.e a = ∑ b, P a b • cu.e b) ∧ (∀ b, cc' b ≠ 0) ∧ (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) := by
  intro E _ _ _ r ρ X cu₀
  classical
  let T : (Fin ρ → E) →ₗ[E] (Fin r → E) := Fintype.linearCombination E cu₀.e
  have hT : ∀ v, T v = ∑ i, v i • cu₀.e i := fun v => Fintype.linearCombination_apply E cu₀.e v
  obtain ⟨Ψ, hΨ⟩ := FJ.exists_crdMap cu₀
  have hinj : Function.Injective T := by
    refine Function.LeftInverse.injective (g := Ψ) fun v => ?_
    rw [hT, hΨ]
  let L : Submodule (𝓞 E) (Fin ρ → E) := X.Λ.comap (T.restrictScalars (𝓞 E))
  have hL : ∀ v, v ∈ L ↔ T v ∈ X.Λ := fun v => Iff.rfl
  have hfg : L.FG := by
    refine Submodule.FG.of_le (X.Λ_fg.map (Ψ.restrictScalars (𝓞 E))) fun v hv => ?_
    refine ⟨T v, (hL v).1 hv, ?_⟩
    show Ψ (T v) = v
    rw [hT, hΨ]
  have hsp : Submodule.span E (L : Set (Fin ρ → E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨c, hc, hcw⟩ := FJ.exists_smul_mem X (T w)
    have hcE : algebraMap (𝓞 E) E c ≠ 0 := fun h =>
      hc (IsFractionRing.injective (𝓞 E) E (by rw [map_zero]; exact h))
    have hm : algebraMap (𝓞 E) E c • w ∈ L := by
      rw [hL, map_smul, algebraMap_smul]
      exact hcw
    have := Submodule.smul_mem (Submodule.span E (L : Set (Fin ρ → E))) (algebraMap (𝓞 E) E c)⁻¹
      (Submodule.subset_span hm)
    rwa [smul_smul, inv_mul_cancel₀ hcE, one_smul] at this
  obtain ⟨s, e, c, hc, hmem, -⟩ := exists_pseudoBasis_adapted E ρ L ⊤ hfg hsp
  have hsum : ∀ a : Fin ρ → E, ∑ b, a b • T (e b) = T (∑ b, a b • e b) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  refine ⟨⟨fun b => T (e b), e.linearIndependent.map' T (LinearMap.ker_eq_bot.2 hinj), ?_⟩,
    (e.toMatrix (Pi.basisFun E (Fin ρ)))ᵀ, c, ?_, ?_, hc, ?_⟩
  · intro a b
    simp only [hT]
    exact herm_comb_eq_zero_of_iso _ _ cu₀.iso _ _
  · rw [Matrix.det_transpose]
    exact e.isUnit_det _
  · intro a
    show cu₀.e a = ∑ b, e.repr (Pi.basisFun E (Fin ρ) a) b • T (e b)
    rw [hsum, e.sum_repr, hT]
    simp [Pi.single_apply]
  · intro a
    show ∑ b, a b • T (e b) ∈ X.Λ ↔ _
    rw [hsum, ← hL, hmem]
    simp only [e.repr_sum_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
section
open MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaMean

theorem mean_image {ι κ : Type} [Fintype ι] [Fintype κ] (L : (ι → ℝ) ≃L[ℝ] (κ → ℂ))
    {s : Set (ι → ℝ)} (hs : volume s = 1) (f : (κ → ℂ) → ℝ) :
    (∫ z in L '' s, f z) / (volume (L '' s)).toReal = ∫ p in s, f (L p) := by
  have hL : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have : (Measure.map L (volume : Measure (ι → ℝ))).IsAddHaarMeasure := L.isAddHaarMeasure_map _
  set c := Measure.addHaarScalarFactor (volume : Measure (κ → ℂ)) (Measure.map L volume) with hc_def
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hvol : (volume : Measure (κ → ℂ)) = c • Measure.map L volume :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hpre : L ⁻¹' (L '' s) = s := Set.preimage_image_eq s L.injective
  have h1 : (volume (L '' s)).toReal = c := by
    rw [hvol, Measure.smul_apply, hL.map_apply, hpre, hs]
    simp
  have h2 : ∫ z in L '' s, f z = c * ∫ p in s, f (L p) := by
    rw [hvol, Measure.restrict_smul, integral_smul_nnreal_measure, hL.restrict_map, hpre,
      hL.integral_map, NNReal.smul_def, smul_eq_mul]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [h2, h1, mul_div_cancel_left₀ _ hc']

def periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun p := (fun i => (p (.inl i) : ℂ)) + τ *ᵥ (fun i => (p (.inr i) : ℂ))
  map_add' p q := by
    funext i
    simp [mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r p := by
    funext i
    simp [mulVec, dotProduct, mul_add, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem periodMap_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → ℝ) :
    periodMap τ p = (fun i => (p (.inl i) : ℂ)) + τ *ᵥ (fun i => (p (.inr i) : ℂ)) := rfl

theorem im_periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → ℝ) :
    (fun i => (periodMap τ p i).im) = τ.map Complex.im *ᵥ fun i => p (.inr i) := by
  funext i
  simp [periodMap_apply, mulVec, dotProduct, Complex.im_sum]

theorem periodMap_bijective {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hp : (τ.map Complex.im).PosDef) : Function.Bijective (periodMap τ) := by
  have hinj : Function.Injective (periodMap τ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp0
    have him := im_periodMap τ p
    rw [hp0] at him
    have h2 : (fun i => p (.inr i)) = 0 := by
      refine Matrix.eq_zero_of_mulVec_eq_zero hp.det_pos.ne' ?_
      rw [← him]
      rfl
    have h1 : (fun i => (p (.inl i) : ℂ)) = 0 := by
      have := hp0
      rw [periodMap_apply] at this
      have h2' : (fun i => (p (.inr i) : ℂ)) = 0 := by
        funext i
        simp [show p (.inr i) = 0 from congrFun h2 i]
      rw [h2', mulVec_zero, add_zero] at this
      exact this
    funext x
    rcases x with i | i
    · simpa using congrFun h1 i
    · exact congrFun h2 i
  have hrank : Module.finrank ℝ (Fin g ⊕ Fin g → ℝ) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩

theorem exists_fundamentalDomain_mean_norm_sq_thetaChar :
    ∀ (g : ℕ) (τ h : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ)
      (Λ : AddSubgroup (Fin g → ℂ)), τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
      (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) →
      (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ,
        h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) →
      ∃ Fd : Set (Fin g → ℂ), MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume ∧
        (∫ z in Fd, ‖thetaChar τ c₁ c₂ (h *ᵥ z)‖ ^ 2 * Real.exp (-2 * Real.pi *
          ((fun i => ((h *ᵥ z) i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ fun i => ((h *ᵥ z) i).im)))) /
          (MeasureTheory.volume Fd).toReal =
          (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ h c₁ c₂ Λ hsym hY hh hc₁ hc₂ hΛ
  obtain ⟨a, rfl⟩ : ∃ a : Fin g → ℝ, (fun i => (a i : ℂ)) = c₁ := by
    refine ⟨fun i => (c₁ i).re, funext fun i => ?_⟩
    show ((c₁ i).re : ℂ) = c₁ i
    rcases hc₁ i with e | e <;> rw [e] <;> norm_num
  obtain ⟨b, rfl⟩ : ∃ b : Fin g → ℝ, (fun i => (b i : ℂ)) = c₂ := by
    refine ⟨fun i => (c₂ i).re, funext fun i => ?_⟩
    show ((c₂ i).re : ℂ) = c₂ i
    rcases hc₂ i with e | e <;> rw [e] <;> norm_num
  have hcancel : ∀ x : Fin g → ℂ, h⁻¹ *ᵥ (h *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]
  let Pe : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (periodMap τ) (periodMap_bijective hY)
  let Hinv : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' h⁻¹) (Matrix.toLin' h)
      (by rw [← Matrix.toLin'_mul, nonsing_inv_mul _ hh, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, mul_nonsing_inv _ hh, Matrix.toLin'_one])
  let Φ : (Fin g ⊕ Fin g → ℝ) ≃L[ℝ] (Fin g → ℂ) :=
    (Pe.trans (Hinv.restrictScalars ℝ)).toContinuousLinearEquiv
  have F1 : ∀ p, h *ᵥ Φ p = periodMap τ p := by
    intro p
    show h *ᵥ (h⁻¹ *ᵥ periodMap τ p) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ hh, one_mulVec]
  let B : Module.Basis (Fin g ⊕ Fin g) ℝ (Fin g → ℂ) :=
    (Pi.basisFun ℝ (Fin g ⊕ Fin g)).map Φ.toLinearEquiv
  have hrepr : ∀ z i, B.repr z i = Φ.symm z i := by
    intro z i
    simp [B]
  have hΛeq : Λ = (Submodule.span ℤ (Set.range B)).toAddSubgroup := by
    ext lam
    rw [hΛ lam, Submodule.mem_toAddSubgroup, Module.Basis.mem_span_iff_repr_mem]
    simp only [hrepr, Set.mem_range, algebraMap_int_eq, eq_intCast]
    constructor
    · rintro ⟨m, n, hmn⟩ i
      have hPq : periodMap τ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) =
          (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
        rw [periodMap_apply]
        simp
      have hΦq : Φ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) = lam := by
        have e : h *ᵥ Φ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) = h *ᵥ lam := by
          rw [F1, hPq, hmn]
        rw [← hcancel (Φ _), e, hcancel]
      rw [← hΦq, Φ.symm_apply_apply]
      rcases i with i | i
      · exact ⟨m i, by simp⟩
      · exact ⟨n i, by simp⟩
    · intro hk
      choose k hk using hk
      refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
      rw [← Φ.apply_symm_apply lam, F1, periodMap_apply]
      simp_rw [← hk, Complex.ofReal_intCast]
  have hFd : ZSpan.fundamentalDomain B = Φ '' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) := by
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    ext z
    simp [ZSpan.mem_fundamentalDomain, hrepr]
  have hcube : volume (Set.univ.pi fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1) = 1 := by
    simpa using Real.volume_pi_Ico (a := fun _ : Fin g ⊕ Fin g => (0 : ℝ)) (b := fun _ => 1)
  have hYu : IsUnit (τ.map Complex.im).det := hY.det_pos.ne'.isUnit
  refine ⟨ZSpan.fundamentalDomain B, by rw [hΛeq]; exact ZSpan.isAddFundamentalDomain' B _, ?_⟩
  rw [hFd, mean_image Φ hcube, ← GlobalTheory.ThetaNorm.integral_norm_sq_thetaChar g τ a b hsym hY]
  congr 1
  funext p
  rw [F1, im_periodMap, mulVec_mulVec, nonsing_inv_mul _ hYu, one_mulVec, dotProduct_comm,
    periodMap_apply]

end GlobalTheory.ThetaMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHostNormModCoprimeLevelHalfStatement
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exists_hostNorm_mod_coprime_level_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (n : ℕ) (ν : ℤ), 0 < n → IsCoprime ν (n : ℤ) → ∃ t : 𝓞 E, (n : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) ∧ (l.M ∣ n → t - 1 ∈ l.Mb) := by
  first | exact @GlobalTheory.NormMod.exists_norm_mod | exact GlobalTheory.NormMod.exists_norm_mod | (intros; apply GlobalTheory.NormMod.exists_norm_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameOfPeriodLinear
section
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePeriod

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


omit [NumberField E] [IsCMField E] in
lemma eq_of_hermC_eq (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0)
    (v w : Fin r → ℂ) (h : ∀ u, FD.hermC τ Gm v u = FD.hermC τ Gm w u) : v = w := by
  classical
  have hd : (τ.mapMatrix Gm).det ≠ 0 := by
    rw [← RingHom.map_det]; exact (map_ne_zero τ).2 hG
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_vecMul_eq_zero hd
  rw [sub_vecMul, sub_eq_zero]
  funext b
  have := h (Pi.single b 1)
  simpa [FD.hermC, Pi.single_apply, apply_ite, vecMul, dotProduct] using this

lemma loc_compare (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0) (q : ℕ)
    (M M' K : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (hM' : M'.det ≠ 0)
    (hK : ∀ a c : Fin r, ¬ ((a : ℕ) < q ↔ (c : ℕ) < q) → K a c = 0)
    (h : ∀ u, locPer τ Gm q M' u = K *ᵥ locPer τ Gm q M u) :
    (∀ a c : Fin r, (a : ℕ) < q → K a c = (M⁻¹ * M') c a) ∧
      ∀ a c : Fin r, q ≤ (a : ℕ) → K a c = (M⁻¹ * M')⁻¹ a c := by
  classical
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  constructor
  · intro a c ha
    have h1 : FD.col M' a = ∑ e, K a e • FD.col M e := by
      apply eq_of_hermC_eq τ Gm hG
      intro u
      have := congrFun (h u) a
      rw [locPer_apply, if_pos ha] at this
      rw [this, FD.hermC_sum_left, mulVec, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [FD.hermC_smul_left, locPer_apply]
      by_cases he : (e : ℕ) < q
      · rw [if_pos he]
      · rw [hK a e (by simp [ha, he])]; simp
    rw [← FD.Data.mulVec_eq_sum_col] at h1
    have h2 : M⁻¹ *ᵥ FD.col M' a = K a := by
      rw [h1, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [← h2]
    rfl
  · intro a c ha
    have ha' : ¬ (a : ℕ) < q := not_lt.2 ha
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    have h1 := congrFun (h (M *ᵥ Pi.single c 1)) a
    rw [locPer_apply, if_neg ha', mulVec_mulVec] at h1
    have h2 : (K *ᵥ locPer τ Gm q M (M *ᵥ Pi.single c 1)) a = (K *ᵥ Pi.single c 1) a := by
      rw [mulVec, mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : (e : ℕ) < q
      · rw [hK a e (by simp [ha', he])]; simp
      · rw [locPer_apply, if_neg he, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [h2] at h1
    simpa using h1.symm

lemma allPer_scale {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r)
    {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (c : Ψ → ℂ) (y : Ψ → Fin r → ℂ) (k : Fin g) :
    allPer Gm q x idx (fun τ => c τ • y τ) k =
      (if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) * allPer Gm q x idx y k := by
  rw [allPer_apply, allPer_apply, locPer_apply, locPer_apply]
  split_ifs
  · rw [FD.hermC_smul_right]
  · rw [mulVec_smul]; rfl

lemma block_of_allPer {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ)
    (x x' : FD.Frame Ψ r) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (h : Matrix (Fin g) (Fin g) ℂ)
    (hs : Function.Surjective (allPer Gm q x idx))
    (hh : ∀ y, allPer Gm q x' idx y = h *ᵥ allPer Gm q x idx y) (k k' : Fin g)
    (hk : ¬ ((idx k).1 = (idx k').1 ∧ (((idx k).2 : ℕ) < q ↔ ((idx k').2 : ℕ) < q))) : h k k' = 0 := by
  classical
  have key : ∀ c : Ψ → ℂ, ((if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) -
      (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1)) * h k k' = 0 := by
    intro c
    obtain ⟨y, hy⟩ := hs (Pi.single k' 1)
    have h1 := congrFun (hh (fun τ => c τ • y τ)) k
    rw [allPer_scale, hh, hy] at h1
    have h2 : allPer Gm q x idx (fun τ => c τ • y τ) = Pi.single k'
        (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1) := by
      funext l
      rw [allPer_scale, hy]
      by_cases hl : l = k'
      · subst hl; simp
      · simp [hl]
    rw [h2] at h1
    simp only [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, mul_one] at h1
    linear_combination h1
  by_cases h1 : (idx k).1 = (idx k').1
  · have h2 := key (fun _ => Complex.I)
    have hI : (2 * Complex.I) ≠ 0 := by simp
    by_cases ha : ((idx k).2 : ℕ) < q <;> by_cases hb : ((idx k').2 : ℕ) < q
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
    · rw [if_pos ha, if_neg hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination -h2
    · rw [if_neg ha, if_pos hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination h2
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
  · have h2 := key (Pi.single (idx k).1 1)
    simpa [Ne.symm h1] using h2

theorem frame_of_period_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∀ (P : D.La →+ (Fin g → ℂ)), ∀ x ∈ FD.GG Ψ Gm D.q, ∀ x' ∈ FD.GG Ψ Gm D.q, (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ (P' : D.La →+ (Fin g → ℂ)), (∀ v k, P' v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x' (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x' (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ h : Matrix (Fin g) (Fin g) ℂ, (∀ v, P' v = h *ᵥ P v) → ∃ b : FD.Frame Ψ r, x' = FD.rmul x b ∧ (∀ τ (a c : Fin r), (c : ℕ) < D.q → D.q ≤ (a : ℕ) → b τ a c = 0) ∧ (∀ k k', (idx k).1 = (idx k').1 → ((idx k).2 : ℕ) < D.q → ((idx k').2 : ℕ) < D.q → h k k' = b (idx k).1 (idx k').2 (idx k).2) ∧ (∀ k k', (idx k).1 = (idx k').1 → D.q ≤ ((idx k).2 : ℕ) → D.q ≤ ((idx k').2 : ℕ) → h k k' = (FD.mat b (idx k).1)⁻¹ (idx k).2 (idx k').2) ∧ ∀ k k', ty k ≠ ty k' → h k k' = 0 := by
  classical
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos ⟨hφ, hspan, hG, hdet, hEF⟩ P x hx x' hx' hP P' hP' h hh
  have hcm := cmType H Ψ hΨ
  have hloc := fun τ : Ψ => (exists_loc τ.1 Gm hG D.q (FD.mat x τ) (hx τ).1 (hx τ).2).1
  have hbij := allPer_bijective Gm D.q x idx hloc
  have hQ : ∀ v, P v = allPer Gm D.q x idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP v k
  have hQ' : ∀ v, P' v = allPer Gm D.q x' idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP' v k
  have := D.fin
  obtain ⟨b, hb⟩ := CMLattice.exists_basis_of_cmType Ψ hcm r (LinearMap.range φ)
    (Module.Finite.iff_fg.1 inferInstance) (by rw [LinearMap.coe_range]; exact hspan)
  have hall : ∀ y, allPer Gm D.q x' idx y = h *ᵥ allPer Gm D.q x idx y := by
    have : allPer Gm D.q x' idx = (h.mulVecLin.restrictScalars ℝ) ∘ₗ allPer Gm D.q x idx := by
      apply b.ext
      intro i
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := (hb (b i)).1 (Submodule.subset_span ⟨i, rfl⟩)
      rw [← hv, ← hQ', hh, hQ]
      rfl
    intro y
    rw [this]; rfl
  have hblock := block_of_allPer Gm D.q x x' idx h hbij.2 hall
  let K : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ =>
    Matrix.of fun a c => h (idx.symm (τ, a)) (idx.symm (τ, c))
  have hK0 : ∀ τ (a c : Fin r), ¬ ((a : ℕ) < D.q ↔ (c : ℕ) < D.q) → K τ a c = 0 := by
    intro τ a c hac
    apply hblock
    simpa using hac
  have hK : ∀ (τ : Ψ) u, locPer τ.1 Gm D.q (FD.mat x' τ) u =
      K τ *ᵥ locPer τ.1 Gm D.q (FD.mat x τ) u := by
    intro τ u
    funext a
    have h1 := congrFun (allPer_symm Gm D.q x' idx (fun _ => u) τ) a
    rw [← h1, hall, mulVec, mulVec, dotProduct, dotProduct, ← idx.symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single τ]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [← allPer_symm Gm D.q x idx (fun _ => u) τ]
      rfl
    · intro σ _ hσ
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hblock, zero_mul]
      simp [hσ.symm]
    · simp
  have hc := fun τ : Ψ => loc_compare τ.1 Gm hdet D.q (FD.mat x τ) (FD.mat x' τ) (K τ) (hx τ).1 (hx' τ).1
    (hK0 τ) (hK τ)
  have hhK : ∀ k k', (idx k).1 = (idx k').1 → h k k' = K (idx k).1 (idx k).2 (idx k').2 := by
    intro k k' e
    simp only [K, of_apply]
    conv_rhs => rw [Prod.mk.eta, e, Prod.mk.eta]
    simp
  refine ⟨fun τ => ((FD.mat x τ)⁻¹ * FD.mat x' τ : Matrix (Fin r) (Fin r) ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (FD.mat x τ) (FD.mat x' τ)
      (isUnit_iff_ne_zero.2 (hx τ).1)).symm
  · intro τ a c hcq ha
    exact ((hc τ).1 c a hcq).symm.trans (hK0 τ c a (by simp [hcq, ha]))
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).1 _ _ h1
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).2 _ _ h1
  · intro k k' hne
    apply hblock
    rintro ⟨e1, e2⟩
    apply hne
    rw [hty, hty, e1]
    simp only [e2]

end

end GlobalTheory.FramePeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureHermitianModelOfDatumStatement
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.signature_hermitian_model_of_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (0 < (τ ξ).im → (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn D.q (a : ℕ) : ℝ) : ℂ))) ∧ ((τ ξ).im < 0 → (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn D.p (a : ℕ) : ℝ) : ℂ))) := by
  first | exact @GlobalTheory.HermSign.signature_of_model | exact GlobalTheory.HermSign.signature_of_model | (intros; apply GlobalTheory.HermSign.signature_of_model <;> assumption)
end

