module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsGramNumberLeMajorantLengths
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.MinorBound

open GlobalTheory.PlueckerBound GlobalTheory.Amp.GramFlag

theorem norm_det_inner_le_pow {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {l : ℕ} (u v : Fin l → E)
    (s t : Matrix (Fin l) (Fin l) ℂ) (hs : s.det = 1) (ht : t.det = 1) {R R' : ℝ}
    (hu : ∀ a, ‖∑ i, s i a • u i‖ ≤ R) (hv : ∀ a, ‖∑ i, t i a • v i‖ ≤ R') :
    ‖(Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det‖ ≤ R ^ l * R' ^ l := by
  have h := norm_det_inner_le (fun a => ∑ i, s i a • u i) (fun a => ∑ i, t i a • v i)
  rw [det_inner_sum_smul, ht, mul_one] at h
  have e : (Matrix.of fun a a' => ⟪∑ i, s i a • u i, v a'⟫_ℂ) = sᴴ * Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ := by
    ext a a'
    simp [Matrix.mul_apply, sum_inner, inner_smul_left, mul_comm]
  rw [e, Matrix.det_mul, Matrix.det_conjTranspose, hs, star_one, one_mul] at h
  have h1 : ∀ {f : Fin l → E} {S : ℝ}, (∀ a, ‖f a‖ ≤ S) → ∏ a, ‖f a‖ ≤ S ^ l := fun {f S} hf => by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (fun a _ => norm_nonneg (f a)) (fun a _ => hf a)
    simpa using this
  have h0 : ∀ f : Fin l → E, 0 ≤ ∏ a, ‖f a‖ := fun f => Finset.prod_nonneg fun a _ => norm_nonneg _
  exact h.trans (mul_le_mul (h1 hu) (h1 hv) (h0 _) ((h0 _).trans (h1 hu)))

theorem exists_short (k r : ℕ) {l : ℕ} (hl : l ≤ r) (z : Fin (2 * r + k + 1) → ℂ) {x : Mat k r} (hx : x ∈ GG k r) :
    ∃ t : Matrix (Fin l) (Fin l) ℂ, t.det = 1 ∧
      ∀ a, eucl (∑ b, t b a • (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl b)))) ≤ Sg k r z x := by
  obtain ⟨u, hu, -⟩ := gramSchmidt_lengths k r z x hx
  refine ⟨(upper u).submatrix (Fin.castLE hl) (Fin.castLE hl), ?_, fun a => ?_⟩
  · rw [Matrix.det_of_upperTriangular]
    · simp [upper]
    · intro a b hab
      have hab' : b < a := hab
      have h1 : ¬ a < b := not_lt.2 hab'.le
      simp [upper, h1, hab'.ne']
  · have e : ∑ b, (upper u).submatrix (Fin.castLE hl) (Fin.castLE hl) b a • (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl b))) =
        ∑ b, upper u b (Fin.castLE hl a) • (x⁻¹ *ᵥ bvec (eI k r b)) := by
      refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun b => rfl)
      intro b hb
      have hb' : l ≤ b.val := by
        by_contra h
        exact hb ⟨⟨b.val, by omega⟩, rfl⟩
      have ha := a.isLt
      have h1 : ¬ b < Fin.castLE hl a := by
        rw [Fin.lt_def, Fin.val_castLE]; omega
      have h2 : b ≠ Fin.castLE hl a := fun h => by
        rw [h, Fin.val_castLE] at hb'; omega
      simp [upper, h1, h2]
    rw [e, (hu _).1]
    exact (Finset.le_fold_max _).2 (Or.inr ⟨_, Finset.mem_univ _, le_rfl⟩)

theorem eucl_Hpk (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : eucl (Hpk k r *ᵥ v) = eucl v := by
  rw [eucl_eq, eucl_eq, @norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_toLp_toLp, Matrix.star_mulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, (hpkFacts k r).1, (hpkFacts k r).2.1, Matrix.one_mulVec, dotProduct_comm]

theorem herm_mulVec {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem one_le_Sg (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : 1 ≤ Sg k r z x :=
  (Finset.le_fold_max _).2 (Or.inl le_rfl)

theorem norm_Dmin_le (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {γ x : Mat k r} (hγ : γ ∈ GG k r) (hx : x ∈ GG k r)
    (l : Fin (r + 1)) : ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ hH
  have hγx := hmul γ hγ x hx
  have hl : l.val ≤ r := Nat.le_of_lt_succ l.isLt
  obtain ⟨s, hs, hs'⟩ := exists_short k r hl z hγx
  obtain ⟨t, ht, ht'⟩ := exists_short k r hl z' hx
  have h := norm_det_inner_le_pow (E := EuclideanSpace ℂ (Fin (2 * r + k + 1)))
    (fun a => WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))))
    (fun a => WithLp.toLp 2 (Hpk k r *ᵥ (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))))) s t hs ht
    (R := Sg k r z (γ * x)) (R' := Sg k r z' x)
    (fun a => by
      have := hs' a
      rwa [eucl_eq, WithLp.toLp_sum] at this)
    (fun a => by
      have := ht' a
      rw [← eucl_Hpk, eucl_eq, Matrix.mulVec_sum, WithLp.toLp_sum] at this
      simpa only [Matrix.mulVec_smul, WithLp.toLp_smul] using this)
  have e : Dmin k r z z' γ l.castSucc = (Matrix.of fun a a' : Fin l.val =>
      ⟪(WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a))) : EuclideanSpace ℂ (Fin (2 * r + k + 1))),
        WithLp.toLp 2 (Hpk k r *ᵥ (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl a'))))⟫_ℂ).det := by
    unfold Dmin
    congr 1
    ext a b
    have ha : a.val < r := lt_of_lt_of_le a.isLt hl
    have hb : b.val < r := lt_of_lt_of_le b.isLt hl
    rw [Matrix.of_apply, EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.submatrix_apply, Zhat,
      ← herm_mulVec (hinv _ hγx).2, Matrix.mulVec_mulVec, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (hinv _ hγ).1, Matrix.mul_one, fvec, fvec, dite_eq_left (by exact hb), dite_eq_left (by exact ha)]
    rfl
  rw [e]
  refine h.trans ?_
  rw [← mul_pow, mul_comm]
  exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (one_le_Sg ..) (one_le_Sg ..)) hl

theorem gramProj_le (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z : Fin (2 * r + k + 1) → ℂ) {x : Mat k r} (hx : x ∈ GG k r)
    (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1)))) :
    gramProj P (fun a : Fin j => x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))) ≤ Sg k r z x ^ r := by
  obtain ⟨s, hs, hs'⟩ := exists_short k r hj z hx
  have h1 : ∀ a, ‖∑ i, s i a • P.starProjection (WithLp.toLp 2 (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj i))))‖ ≤
      Sg k r z x := fun a => by
    have := hs' a
    rw [eucl_eq, WithLp.toLp_sum] at this
    refine le_trans (le_of_eq ?_) ((P.norm_starProjection_apply_le _).trans this)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, WithLp.toLp_smul, map_smul]
  have h := norm_det_inner_le_pow _ _ s s hs hs h1 h1
  have h0 := one_le_Sg k r z x
  refine le_trans ?_ (pow_le_pow_right₀ h0 hj)
  unfold gramProj
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [sq]
  exact h

theorem minor_gram_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ l : Fin (r + 1), ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r) ∧ 0 ≤ Yj k r hj z z' γ x ∧ Yj k r hj z z' γ x ≤ Sg k r z (γ * x) ^ r / Dj k r hj z z' γ ∧ ∀ H₁ : ℝ, 1 ≤ H₁ → sgV k r z z' γ H₁ ≤ max 1 ((Sg k r z' x * Sg k r z (γ * x)) ^ r / (2 * H₁) ^ (2 * r)) := by
  intro k r j hj z z' γ _ _ hγ x hx
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hγx := (uHGroup _ _ hH).2.1 γ hγ x hx
  refine ⟨norm_Dmin_le k r z z' hγ hx, div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _), ?_, fun H₁ hH₁ => ?_⟩
  · refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    have := gramProj_le k r hj z hγx (Ppos k r z z' γ x)
    simpa only [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec] using this
  · refine (Finset.fold_max_le _).2 ⟨le_max_left _ _, fun l _ => le_max_of_le_right ?_⟩
    exact div_le_div_of_nonneg_right (norm_Dmin_le k r z z' hγ hx l) (by positivity)

end GlobalTheory.Amp.MinorBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTop
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal Pointwise

noncomputable section

namespace GlobalTheory.OrbitSumInt

theorem exists_compact_reach {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [ContinuousSMul G X] (x0 : X) (hcl : IsClosed (MulAction.orbit G x0))
    (K : Set X) (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ g : G, g • x0 ∈ K → ∃ c ∈ C, c • x0 = g • x0 := by
  let O := MulAction.orbit G x0
  have : LocallyCompactSpace O := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul G O := ⟨continuous_induced_rng.2
    (continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  let o0 : O := ⟨x0, MulAction.mem_orbit_self x0⟩
  have hopen : IsOpenMap (fun g : G => g • o0) := isOpenMap_smul_of_sigmaCompact o0
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set O) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have key : ∃ C : Set G, IsCompact C ∧ (Subtype.val ⁻¹' K : Set O) ⊆ (fun g : G => g • o0) '' C := by
    refine hK'.induction_on (p := fun s => ∃ C : Set G, IsCompact C ∧ s ⊆ (fun g : G => g • o0) '' C)
      ⟨∅, isCompact_empty, Set.empty_subset _⟩ (fun s t hst ⟨C, hC, h⟩ => ⟨C, hC, hst.trans h⟩) ?_ ?_
    · rintro s t ⟨C, hC, h⟩ ⟨D, hD, h'⟩
      exact ⟨C ∪ D, hC.union hD, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
    · rintro ⟨_, g, rfl⟩ -
      obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hg), C, hC, subset_rfl⟩
  obtain ⟨C, hC, h⟩ := key
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨c, hc, e⟩ := h (a := g • o0) hg
  exact ⟨c, hc, congrArg Subtype.val e⟩

theorem lintegral_count_lt_top {G H X S : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [MulAction G X]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (Δ : Subgroup H) [Countable Δ] (𝓕 : Set G) (𝓖 : Set H)
    (hF : IsFundamentalDomain Γ 𝓕 μ) (hG : IsFundamentalDomain Δ 𝓖 ν) (hfin : ν 𝓖 < ⊤)
    (φ : H →* G) (hφ : Continuous φ) (hinj : Function.Injective φ) (x0 : X)
    (hr : φ.range = MulAction.stabilizer G x0) (hΔ : ∀ δ ∈ Δ, φ δ ∈ Γ)
    (ι : S → X) (hι : Function.Injective ι) (γ : S → Γ) (hγ : ∀ s, (γ s : G) • x0 = ι s)
    (K : Set X) (C : Set G) (hC : IsCompact C) (hKC : ∀ g : G, g • x0 ∈ K → ∃ c ∈ C, c • x0 = g • x0) :
    ∫⁻ h in 𝓕, ∑' s, K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ∂μ < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Δ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Δ ν
  obtain ⟨U, hU, hU1⟩ := exists_compact_mem_nhds (1 : H)
  have hU0 : ν U ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hU1).ne'
  set D : Set G := (φ '' U)⁻¹ * C⁻¹ with hD
  have hDc : IsCompact D := (hU.image hφ).inv.mul hC.inv
  let f : G → ℝ≥0∞ := D.indicator 1
  have hf : Measurable f := measurable_one.indicator hDc.measurableSet
  let T : G → ℝ≥0∞ := fun g => ∫⁻ k in 𝓖, f ((φ k)⁻¹ * g) ∂ν
  have hm : Measurable fun p : G × H => f ((φ p.2)⁻¹ * p.1) :=
    hf.comp ((hφ.comp continuous_snd).inv.mul continuous_fst).measurable
  have hT : Measurable T := hm.lintegral_prod_right'
  have hfix : ∀ k, φ k • x0 = x0 := fun k => by
    have : φ k ∈ MulAction.stabilizer G x0 := hr ▸ ⟨k, rfl⟩
    exact this
  let j : S × Δ → Γ := fun p => γ p.1 * ⟨φ p.2, hΔ _ p.2.2⟩
  have hj : Function.Injective j := by
    rintro ⟨s, a⟩ ⟨t, b⟩ h
    have h1 : (γ s : G) * φ a = γ t * φ b := congrArg Subtype.val h
    have h2 : s = t := hι (by rw [← hγ, ← hγ, ← hfix a, ← mul_smul, h1, mul_smul, hfix, hfix])
    subst h2
    rw [Subtype.ext (hinj (mul_left_cancel h1))]
  have step : ∀ (h : G) (s : S), ν U * K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ≤
      ∑' δ : Δ, T ((j (s, δ))⁻¹ • h) := by
    intro h s
    by_cases hK : h⁻¹ • ι s ∈ K
    swap
    · simp [Set.indicator_of_notMem hK]
    rw [Set.indicator_of_mem hK, Pi.one_apply, mul_one]
    rw [← hγ, ← mul_smul] at hK
    obtain ⟨c, hc, e⟩ := hKC _ hK
    obtain ⟨k, hk⟩ : c⁻¹ * (h⁻¹ * γ s) ∈ φ.range := by
      rw [hr, MulAction.mem_stabilizer_iff, mul_smul, ← e, inv_smul_smul]
    have e1 := hG.lintegral_eq_tsum'' fun k' => f ((φ k')⁻¹ * ((γ s : G)⁻¹ * h))
    have e2 : ∀ δ : Δ, T ((j (s, δ))⁻¹ • h) =
        ∫⁻ k' in 𝓖, f ((φ (δ • k'))⁻¹ * ((γ s : G)⁻¹ * h)) ∂ν := fun δ => by
      refine lintegral_congr fun k' => ?_
      congr 1
      simp [j, Subgroup.smul_def, mul_assoc]
    simp only [e2]
    rw [← e1, ← measure_preimage_mul ν k U, ← lintegral_indicator_one
      ((measurable_const_mul k) hU.measurableSet)]
    refine lintegral_mono fun k' => ?_
    by_cases hk' : k' ∈ (fun x => k * x) ⁻¹' U
    swap
    · simp [Set.indicator_of_notMem hk']
    have : (φ k')⁻¹ * ((γ s : G)⁻¹ * h) ∈ D := by
      refine ⟨(φ (k * k'))⁻¹, Set.inv_mem_inv.2 ⟨_, hk', rfl⟩, c⁻¹, Set.inv_mem_inv.2 hc, ?_⟩
      simp [hk, mul_assoc]
    simp [f, Set.indicator_of_mem hk', Set.indicator_of_mem this]
  have main : ν U * ∫⁻ h in 𝓕, ∑' s, K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ∂μ ≤ μ D * ν 𝓖 := by
    rw [← lintegral_const_mul' _ _ hU.measure_lt_top.ne]
    calc _ ≤ ∫⁻ h in 𝓕, ∑' g : Γ, T (g⁻¹ • h) ∂μ := by
          refine lintegral_mono fun h => ?_
          rw [← ENNReal.tsum_mul_left]
          refine (ENNReal.tsum_le_tsum (step h)).trans ?_
          rw [← ENNReal.tsum_prod (f := fun s δ => T ((j (s, δ))⁻¹ • h))]
          exact ENNReal.tsum_comp_le_tsum_of_injective hj fun g => T (g⁻¹ • h)
      _ = ∫⁻ g, T g ∂μ := by
          rw [hF.lintegral_eq_tsum']
          exact lintegral_tsum fun g => (hT.comp (measurable_const_smul g⁻¹)).aemeasurable
      _ = ∫⁻ k in 𝓖, μ D ∂ν := by
          rw [lintegral_lintegral_swap hm.aemeasurable]
          refine lintegral_congr fun k => ?_
          rw [lintegral_mul_left_eq_self f, lintegral_indicator_one hDc.measurableSet]
      _ = μ D * ν 𝓖 := by simp
  by_contra htop
  rw [not_lt_top_iff.1 htop, ENNReal.mul_top hU0] at main
  exact (ENNReal.mul_lt_top hDc.measure_lt_top hfin).not_ge main


open GlobalTheory.GaugeEx in
theorem lintegral_orbitSum_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : F), β ≠ 0 → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → ∫⁻ h in 𝓕, ∑' x : {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β}, ‖Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))‖ₑ ∂μ < ⊤ := by
  intro F E _ _ _ _ _ σ hCM M J hJ β hβ Φ hΦ hK μ 𝓕 hμ h𝓕
  rcases isEmpty_or_nonempty {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β} with he | ⟨⟨x0, hx0⟩⟩
  · simp
  have hx0 : hE σ J (x0 0) (x0 0) = algebraMap F E β := hx0
  have hβ' : algebraMap F E β ≠ 0 := by simpa using hβ
  have hxx : hE σ J (x0 0) (x0 0) ≠ 0 := hx0 ▸ hβ'
  obtain _ | M := M
  · exact (hxx (by simp [hE, Formalism.UG.hform])).elim
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hθ : ∃ θ : E, IsUnit (θ - (σ : E →+* E) θ) := by
    by_contra hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hCM.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    have hz : σ z = z := by
      by_contra hz
      exact hc ⟨z, (sub_ne_zero.2 (Ne.symm hz)).isUnit⟩
    have := hCM.2.2.2 τ z
    rw [hz] at this
    exact this.symm
  obtain ⟨a, B, J', -, -, -, hxB, hBB, hJ'⟩ := GlobalTheory.AdelicStabUnimod.exists_stepData hCM hJ x0 hxx
  obtain ⟨φ, hφ, hinj, hr, -, hrat⟩ := GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser F E σ hCM (M + 1) M
    J J' B x0 rfl hJ hJ' hBB.symm hxB hxx
  let ν : Measure (HA (AF F) σ J') := Measure.haar
  have hν : ν.IsHaarMeasure := inferInstance
  obtain ⟨𝓖, h𝓖⟩ := (GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E σ M J' ν hν).1
  have hfin : ν 𝓖 < ⊤ := GlobalTheory.Mem.VolFin.finVol F E σ hCM M J' hJ' ν hν 𝓖 h𝓖
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hCM.2.2.1
  have horb : MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) x0) =
      {y | qR (AF F) σ J (y 0) = algebraMap F (AF F) β} := by
    ext y
    refine ⟨?_, fun hy => GlobalTheory.AdelicWitt.witt_adelic F E σ hCM _ J x0 β hJ hβ hx0 y hy⟩
    rintro ⟨g, rfl⟩
    rw [Set.mem_setOf_eq, ← GlobalTheory.AdelicWitt.qR_ratTup b (AF F) σ J x0 β hx0]
    exact congrArg (fun z => algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E) z)
      (GlobalTheory.StabOrbit.hR_act (AF F) σ J g _ _)
  have hcl : IsClosed (MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) x0)) := by
    rw [horb]
    refine isClosed_eq ?_ continuous_const
    have h1 : Continuous (Algebra.trace (AF F) (AF F ⊗[F] E)) :=
      IsModuleTopology.continuous_of_linearMap _
    have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
    unfold qR hR Formalism.UG.hform
    refine continuous_const.mul (h1.comp ?_)
    fun_prop
  obtain ⟨C, hC, hKC⟩ := exists_compact_reach _ hcl _ hK
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  let Δ : Subgroup (HA (AF F) σ J') := HFinIn (AF F) σ J'
  have : Countable Γ := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have : Countable Δ := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J'
  have hγ : ∀ s : {x : Fin 1 → Fin (M + 1) → E | hE σ J (x 0) (x 0) = algebraMap F E β},
      ∃ γ : Γ, (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) x0 = ratTup (F := F) (AF F) s.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, e⟩ := GlobalTheory.WittTransitivity.witt_transitive E (σ : E →+* E) hσ
      (fun a _ ha => ha.isUnit) two_ne_zero.isUnit three_ne_zero hθ _ J hJ.1 hJ.2.isUnit (x0 0) (x 0)
      (hx0.trans (Eq.symm hx)) hxx.isUnit
    have hm : Formalism.UG.bc (inclR (F := F) (AF F)) g ∈ HR (AF F) σ J := by
      have hg' : Formalism.UG.cT (σ : E →+* E) g.1 * J * g.1 = J := hg
      have h1 := congrArg (·.map (inclR (F := F) (AF F))) hg'
      simp only [Matrix.map_mul] at h1
      exact h1
    refine ⟨⟨(⟨_, hm⟩ : HR (AF F) σ J), ⟨g, hg, rfl⟩⟩, ?_⟩
    funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    change _ = inclR (F := F) (AF F) (x 0 i)
    rw [← e, RingHom.map_mulVec]
    rfl
  choose γ hγ using hγ
  have : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × _))
  have hι : Function.Injective fun s : {x : Fin 1 → Fin (M + 1) → E | hE σ J (x 0) (x 0) = algebraMap F E β} =>
      ratTup (F := F) (AF F) s.1 := fun s t h => Subtype.ext (funext fun k => funext fun i =>
    (inclR (F := F) (E := E) (AF F)).injective (congrFun (congrFun h k) i))
  have key := lintegral_count_lt_top μ ν Γ Δ 𝓕 𝓖 h𝓕 h𝓖 hfin φ hφ hinj (ratTup (F := F) (AF F) x0) hr
    (fun δ hδ => (hrat δ).2 hδ) _ hι γ hγ (tsupport Φ) C hC hKC
  obtain ⟨A, hA⟩ := hΦ.bounded_above_of_compact_support hK
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := A)) key)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun h => ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : h⁻¹ • ratTup (F := F) (AF F) s.1 ∈ tsupport Φ
  · rw [Set.indicator_of_mem hs, Pi.one_apply, mul_one, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hA _)
  · simp [image_eq_zero_of_notMem_tsupport hs]

end GlobalTheory.OrbitSumInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowAnalyticFactsOfFourSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  GlobalTheory.NGRow

namespace GlobalTheory.NGRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticP_of_steps : StepPinExists → StepVanishPinned → StepLocGenPinnedC → StepThmBPinnedP →
    StepAnalyticP := by
  intro hE hV hL hB Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨e₀, f₀, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨v₀, w₀, hV2⟩ := hV Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, p₀, q₀, hB2⟩ := hB Cg cb Cw cT CT C0 hcb hcT A
  refine ⟨CB, CSt, hCB, hCSt, max a₀ (max e₀ (max v₀ p₀)), max b₀ (max f₀ (max w₀ q₀)),
    fun C' Cl h1 h2 D large₂ X Y u u' hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk => ?_⟩
  have ha1 : a₀ ≤ C' := le_trans (by simp) h1
  have ha2 : b₀ ≤ Cl := le_trans (by simp) h2
  have he1 : e₀ ≤ C' := le_trans (by simp) h1
  have he2 : f₀ ≤ Cl := le_trans (by simp) h2
  have hv1 : v₀ ≤ C' := le_trans (by simp) h1
  have hv2 : w₀ ≤ Cl := le_trans (by simp) h2
  have hp1 : p₀ ≤ C' := le_trans (by simp) h1
  have hp2 : q₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨ν, hν⟩ := hE2 C' Cl he1 he2 D large₂ X Y u u' hc
  obtain ⟨s, ng, e1, hs1, hs0, hsb, he0, he3, hLoc, hGen⟩ :=
    hL2 C' Cl ha1 ha2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  exact ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    nuQOK_sc u u' s hs1 hs0 ν hν.1, hν.1, hb0, le_rfl, he0, he3,
    ampVanish_sc Y u u' s hs0 ν (hV2 C' Cl hv1 hv2 D large₂ X Y u u' hc ν hν), hLoc, hGen,
    measureInput_sc Y u u' s ν _ hsb ng,
    hB2 C' Cl hp1 hp2 D large₂ X Y u u' hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν (sc s ν) ng⟩

end GlobalTheory.NGRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSplitFiniteArchimedeanPartsOfSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  GlobalTheory.NGRow

namespace GlobalTheory.NGRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ngCut2P_of_steps (hM : StepAnalyticConstantsP) (hS : StepSizes) (hC : StepClass) (hN : StepNormals)
    (hP : StepPoints) (hH : StepHeight) : NGCut2P := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hM Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩ := hA1 (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩ := hS Cg cb Cw cT CT C0
  obtain ⟨n₀, m₀, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨p₀, q₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨h₀, j₀, hH2⟩ := hH Cg cb Cw cT CT C0
  refine ⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _,
    max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))),
    fun C' Cl h1 h2 D large₂ X Y u u' hTies h0 hs hT => ?_⟩
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' := ⟨h0, hs, hT⟩
  have e1' : a₀ ≤ C' := le_trans (by simp) h1
  have e2' : b₀ ≤ Cl := le_trans (by simp) h2
  have f1 : s₀ ≤ C' := le_trans (by simp) h1
  have f2 : t₀ ≤ Cl := le_trans (by simp) h2
  have i1 : n₀ ≤ C' := le_trans (by simp) h1
  have i2 : m₀ ≤ Cl := le_trans (by simp) h2
  have j1 : p₀ ≤ C' := le_trans (by simp) h1
  have j2 : q₀ ≤ Cl := le_trans (by simp) h2
  have k1 : h₀ ≤ C' := le_trans (by simp) h1
  have k2 : j₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨P, iP, B, Irat, Ire, hBk, νL, νB, ng, cSt, e1, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩ :=
    hA2 C' Cl e1' e2' D large₂ X Y u u' hTies hc
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk
  refine ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI,
    ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u' hc) c1 c2 c3 c4, ?_, hMeas, hSum⟩
  exact ⟨hC D X Y u u' hT νL νB ng, ampInput_of_vanish Y u u' νL νB ng hV,
    hN2 C' Cl i1 i2 D large₂ X Y u u' hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u u' hc νL νB ng, hLoc, hGen,
    hH2 C' Cl k1 k2 D large₂ X Y u u' hc νL νB ng⟩

end GlobalTheory.NGRow
end
end

