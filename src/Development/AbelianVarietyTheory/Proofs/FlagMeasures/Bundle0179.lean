module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0059
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisChangeModels
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.AdaptedMove

private theorem lamX_eq_of_snd_eq (I : AutInst) {p q : I.GA} (h : p.2 = q.2) : lamX I p = lamX I q := by
  unfold lamX
  rw [h]

private theorem GL_mulVec_injective {K : Type} [Field K] {m : ℕ} (g : GL (Fin m) K) {u v : Fin m → K}
    (h : (g : Matrix (Fin m) (Fin m) K) *ᵥ u = (g : Matrix (Fin m) (Fin m) K) *ᵥ v) : u = v := by
  have h' := congrArg (fun w => ((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ w) h
  simpa [Matrix.mulVec_mulVec] using h'

theorem lamX_move (I : AutInst) (x x' : I.Gf) (h : ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * x = x' * k) :
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      ∀ y, (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I (1, x') ↔ y ∈ lamX I (1, x) := by
  obtain ⟨γ, hγ, k, hk, hx⟩ := h
  obtain ⟨g, hgU, -, hgf⟩ := hγ
  refine ⟨g, hgU, fun y => ?_⟩
  have h1 : lamX I (γ * (1, x)) = lamX I (1, x') := by
    have e1 : lamX I (γ * (1, x)) = lamX I ((1, x') * (1, k)) :=
      lamX_eq_of_snd_eq I (by simp [hx])
    rw [e1]
    exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, x') (1, k)).1 hk
  have h2 := GlobalTheory.PointEquivariance.lamX_rat I (1, x) γ g hgf
  rw [h1, GlobalTheory.PointEquivariance.ratIso_apply] at h2
  rw [h2, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = (g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y := by
      simpa using hzy
    rwa [← GL_mulVec_injective g hzy']
  · intro hy
    exact ⟨y, hy, by simp⟩

theorem isLattice_move {E : Type} [Field E] [NumberField E] {m : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin m → E))
    (γ : GL (Fin m) E) (h : ∀ y, (γ : Matrix (Fin m) (Fin m) E) *ᵥ y ∈ Λ' ↔ y ∈ Λ)
    (hΛ : Submodule.IsFullLattice E Λ) : Submodule.IsFullLattice E Λ' := by
  have hmap : Λ' = Λ.map ((Matrix.toLin' (γ : Matrix (Fin m) (Fin m) E)).restrictScalars (𝓞 E)) := by
    ext z
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
    constructor
    · intro hz
      refine ⟨((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ z, (h _).1 ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hz
      · simp [Matrix.mulVec_mulVec]
    · rintro ⟨y, hy, rfl⟩
      exact (h y).2 hy
  have hspan : Submodule.span E (Λ : Set (Fin m → E)) ≤
      (Submodule.span E (Λ' : Set (Fin m → E))).comap
        (Matrix.toLin' (γ : Matrix (Fin m) (Fin m) E)) := by
    apply Submodule.span_le.mpr
    intro y hy
    exact Submodule.subset_span ((h y).2 hy)
  rw [hΛ.span_eq_top] at hspan
  refine { toIsLattice := ?_, span_eq_top := ?_ }
  · rw [hmap]
    exact Submodule.IsLattice.of_fg E (hΛ.fg.map _)
  · apply top_unique
    intro z _
    have hz := hspan (show ((γ⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) *ᵥ z ∈ ⊤ from trivial)
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using hz

theorem gram_mul {E : Type} [CommRing E] [StarRing E] {n p q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin n) (Fin p) E) (B : Matrix (Fin n) (Fin q) E) (P : Matrix (Fin p) (Fin p) E)
    (Q : Matrix (Fin q) (Fin q) E) : (A * P)ᴴ * J * (B * Q) = Pᴴ * (Aᴴ * J * B) * Q := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem star_dotProduct_conjTranspose_mulVec {K : Type} [Field K] [StarRing K] {m : ℕ} (N : Matrix (Fin m) (Fin m) K)
    (t u : Fin m → K) : star t ⬝ᵥ (Nᴴ *ᵥ u) = star (N *ᵥ t) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

private theorem map_mulVec_eq_mulVec_map {K₀ K : Type} [Field K₀] [Field K] {m : ℕ} (e : K₀ ≃+* K)
    (g : Matrix (Fin m) (Fin m) K₀) (y : Fin m → K₀) :
    (fun l => e ((g *ᵥ y) l)) = g.map e *ᵥ fun l => e (y l) := by
  ext l
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem adapted_move : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (Λ' : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀' : I₀.Gf), (∀ i, ∃ γ : GL (Fin (j i)) I.E, ∀ y, (γ : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ' i ↔ y ∈ Λ i) → (∃ γ ∈ I₀.GFset, ∃ k ∈ I₀.Kset, γ.2 * x₀ = x₀' * k) → ∃ U U' U₀, IsAdapted I I₀ e xf j S Λ' x₀' U U' U₀ := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ _ hA Λ' x₀' hΛ hx
  obtain ⟨he, hn, hlat, hiso, hdual, h0, hlam, hS⟩ := hA
  choose γ hγ using hΛ
  obtain ⟨g₀, hg₀, hg₀m⟩ := lamX_move I₀ x₀ x₀' hx
  have hinv : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) * I₀.J *
      (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val = I₀.J := (Formalism.UG.UJ _ _).inv_mem hg₀
  have hcT : Formalism.UG.cT (starRingEnd I₀.E) ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val) =
      ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val)ᴴ := by
    ext r s
    simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply,
      starRingEnd_apply]
  rw [hcT] at hinv
  have hc : ∀ i, ((γ i).val)ᴴ * (((γ i)⁻¹).val)ᴴ = 1 := by
    intro i
    rw [← Matrix.conjTranspose_mul, Units.inv_mul, Matrix.conjTranspose_one]
  have hG1 : ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e * (g₀.val).map e = 1 := by
    have h1 : ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val * g₀.val).map e = 1 := by
      rw [Units.inv_mul]
      exact Matrix.map_one _ (map_zero e) (map_one e)
    rw [← h1]
    ext r s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  refine ⟨fun i => T i * ((γ i)⁻¹).val, fun i => T' i * ((γ i).val)ᴴ,
    T₀ * ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e, he, hn,
    fun i => isLattice_move (Λ i) (Λ' i) (γ i) (hγ i) (hlat i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    obtain ⟨h1, h2, h3⟩ := hiso i k
    refine ⟨?_, ?_, fun hik => ?_⟩
    · rw [gram_mul, h1, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h3 hik, Matrix.mul_zero, Matrix.zero_mul]
  · intro i
    obtain ⟨h1, h2, h3⟩ := hdual i
    refine ⟨?_, ?_, ?_⟩
    · rw [gram_mul, h1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.mul_inv,
        Matrix.conjTranspose_one]
    · rw [gram_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [gram_mul, h3, Matrix.mul_zero, Matrix.zero_mul]
  · rw [gram_mul, h0]
    have key : (((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e)ᴴ * I₀.J.map e *
        ((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e =
        (((g₀⁻¹ : GL (Fin I₀.n) I₀.E).val)ᴴ * I₀.J * (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val).map e := by
      ext r s
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul, he]
    rw [key, hinv]
  · intro z
    rw [hlam z]
    constructor
    · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
      refine ⟨fun i => (γ i).val *ᵥ u i, fun i => (((γ i)⁻¹).val)ᴴ *ᵥ u' i, g₀.val *ᵥ y,
        fun i => (hγ i _).2 (hu i), fun i t ht => ?_, (hg₀m y).2 hy, ?_⟩
      · have ht' : ((γ i)⁻¹).val *ᵥ t ∈ Λ i := (hγ i _).1 (by simpa [Matrix.mulVec_mulVec] using ht)
        rw [star_dotProduct_conjTranspose_mulVec]
        exact hu' i _ ht'
      · simp only [Matrix.mulVec_mulVec, map_mulVec_eq_mulVec_map, Matrix.mul_assoc, Units.inv_mul, hc, hG1,
          Matrix.mul_one]
    · rintro ⟨w, w', y', hw, hw', hy', rfl⟩
      refine ⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => ((γ i).val)ᴴ *ᵥ w' i,
        (g₀⁻¹ : GL (Fin I₀.n) I₀.E).val *ᵥ y', fun i => (hγ i _).1 ?_, fun i t ht => ?_,
        (hg₀m _).1 ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hw i
      · rw [star_dotProduct_conjTranspose_mulVec]
        exact hw' i _ ((hγ i t).2 ht)
      · simpa [Matrix.mulVec_mulVec] using hy'
      · simp only [Matrix.mulVec_mulVec, map_mulVec_eq_mulVec_map]
  · intro k z
    rw [hS k z]
    constructor
    · rintro ⟨u, hu, hz, rfl⟩
      refine ⟨fun i => (γ i).val *ᵥ u i, fun i => (hγ i _).2 (hu i), fun i hi => ?_, ?_⟩
      · simp [hz i hi]
      · simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    · rintro ⟨w, hw, hz, rfl⟩
      refine ⟨fun i => ((γ i)⁻¹).val *ᵥ w i, fun i => (hγ i _).1 ?_, fun i hi => ?_, ?_⟩
      · simpa [Matrix.mulVec_mulVec] using hw i
      · simp [hz i hi]
      · simp only [Matrix.mulVec_mulVec]

end GlobalTheory.AdaptedMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousLimitUniformCauchy
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.RegLimit

theorem sq_le_four (a e b : ENNReal) (h : a ≤ e + b) : a ^ 2 ≤ 4 * (e ^ 2 + b ^ 2) := by
  have h1 : e + b ≤ 2 * max e b := by
    rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
  have h2 : max e b ^ 2 ≤ e ^ 2 + b ^ 2 := by
    rcases le_total e b with h | h
    · rw [max_eq_right h]; exact le_add_self
    · rw [max_eq_left h]; exact le_self_add
  calc a ^ 2 ≤ (2 * max e b) ^ 2 := pow_le_pow_left₀ zero_le (h.trans h1) 2
    _ = 4 * max e b ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (e ^ 2 + b ^ 2) := by gcongr

theorem exists_continuous_limit : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → ∀ {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp] (f : ℕ → Mat k r → Wp) (g : Mt k r → Wp), (∀ j, ContinuousOn (f j) (GG k r)) → (∀ Q : Set (Mt k r), IsCompact Q → AEStronglyMeasurable g (μ.restrict Q)) → (∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q, Matrix.of x ∈ GG k r → ‖f j (Matrix.of x) - f l (Matrix.of x)‖ ≤ ε) → (∀ Q : Set (Mt k r), IsCompact Q → Filter.Tendsto (fun j : ℕ => ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) Filter.atTop (nhds 0)) → ∃ F : Mat k r → Wp, ContinuousOn F (GG k r) ∧ ((fun x : Mt k r => F (Matrix.of x)) =ᵐ[μ] g) ∧ ∀ x ∈ GG k r, Filter.Tendsto (fun j : ℕ => f j x) Filter.atTop (nhds (F x)) := by
  intro k r μ hμ Wp _ _ _ f g hf hg hC hL
  set T : Set (Mt k r) → Set (Mat k r) := fun Q => GG k r ∩ {y | Matrix.of.symm y ∈ Q} with hT
  have hUC : ∀ Q : Set (Mt k r), IsCompact Q → UniformCauchySeqOn f Filter.atTop (T Q) := by
    intro Q hQ
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hC Q hQ (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn y hy => ?_⟩
    have := hN m hm n hn (Matrix.of.symm y) hy.2 (by rw [Matrix.of.apply_symm_apply]; exact hy.1)
    simp only [Equiv.apply_symm_apply] at this
    rw [dist_eq_norm]; linarith
  set F : Mat k r → Wp := fun y => Filter.limUnder Filter.atTop (fun j => f j y) with hFdef
  have hF : ∀ y ∈ GG k r, Filter.Tendsto (fun j => f j y) Filter.atTop (nhds (F y)) := by
    intro y hy
    have hc := (hUC {Matrix.of.symm y} isCompact_singleton).cauchySeq
      (show y ∈ T {Matrix.of.symm y} from ⟨hy, rfl⟩)
    obtain ⟨L, hL'⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨L, hL'⟩
  have hU : ∀ Q : Set (Mt k r), IsCompact Q → TendstoUniformlyOn f F Filter.atTop (T Q) :=
    fun Q hQ => (hUC Q hQ).tendstoUniformlyOn_of_tendsto (fun y hy => hF y hy.1)
  have hsymm : Continuous (fun y : Mat k r => (Matrix.of.symm y : Mt k r)) := continuous_id
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hFc : ContinuousOn F (GG k r) := by
    intro x hx
    set Q : Set (Mt k r) := Metric.closedBall (Matrix.of.symm x) 1
    have hQ : IsCompact Q := isCompact_closedBall _ _
    have h1 : ContinuousOn F (T Q) :=
      (hU Q hQ).continuousOn (Filter.Eventually.of_forall (f := Filter.atTop) fun j => (hf j).mono Set.inter_subset_left).frequently
    have hxT : x ∈ T Q := ⟨hx, show (Matrix.of.symm x : Mt k r) ∈ Q from Metric.mem_closedBall_self (x := (Matrix.of.symm x : Mt k r)) zero_le_one⟩
    refine (h1 x hxT).mono_of_mem_nhdsWithin ?_
    exact inter_mem_nhdsWithin _ (hsymm.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ zero_lt_one))

  have hGcl : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := (gg_closedSub k r).2.1.preimage hof
  have hGae : ∀ᵐ x ∂μ, Matrix.of x ∈ GG k r := ae_iff.2 hμ.2.2.1
  have hFm : AEStronglyMeasurable (fun x : Mt k r => F (Matrix.of x)) μ := by
    have h1 : ContinuousOn (fun x : Mt k r => F (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} :=
      hFc.comp hof.continuousOn (fun x hx => hx)
    have h2 := h1.aestronglyMeasurable (μ := μ) hGcl.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) hGae] at h2
  have hQae : ∀ Q : Set (Mt k r), IsCompact Q → MeasurableSet Q →
      ∀ᵐ x ∂(μ.restrict Q), F (Matrix.of x) = g x := by
    intro Q hQ hQm
    have hQfin : μ Q ≠ ⊤ := (haar_compact_lt_top hμ hQ).ne
    set a : Mt k r → ENNReal := fun x => (‖F (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 with ha
    have hbound : ∀ n : ℕ, ∫⁻ x in Q, a x ∂μ ≤
        4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q + ENNReal.ofReal (1 / ((n : ℝ) + 1))) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have e1 := Metric.tendstoUniformlyOn_iff.1 (hU Q hQ) _ hpos
      have e2 := ENNReal.tendsto_nhds_zero.1 (hL Q hQ) _ (ENNReal.ofReal_pos.2 hpos)
      obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
      calc ∫⁻ x in Q, a x ∂μ
          ≤ ∫⁻ x in Q, 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 +
              (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem hQm, ae_restrict_of_ae hGae] with x hxQ hxG
            apply sq_le_four
            have hd := hj1 (Matrix.of x) ⟨hxG, by simpa using hxQ⟩
            have htri : ‖F (Matrix.of x) - g x‖₊ ≤
                ‖F (Matrix.of x) - f j (Matrix.of x)‖₊ + ‖f j (Matrix.of x) - g x‖₊ := by
              have : F (Matrix.of x) - g x = (F (Matrix.of x) - f j (Matrix.of x)) + (f j (Matrix.of x) - g x) := by
                abel
              rw [this]; exact nnnorm_add_le _ _
            calc (‖F (Matrix.of x) - g x‖₊ : ENNReal)
                ≤ (‖F (Matrix.of x) - f j (Matrix.of x)‖₊ : ENNReal) + ‖f j (Matrix.of x) - g x‖₊ := by
                  rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.2 htri
              _ ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ‖f j (Matrix.of x) - g x‖₊ := by
                  gcongr
                  exact ENNReal.coe_le_coe.2 ((Real.le_toNNReal_iff_coe_le hpos.le).2
                    (by rw [coe_nnnorm, ← dist_eq_norm]; exact hd.le))
        _ = 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q +
              ∫⁻ x in Q, (‖f j (Matrix.of x) - g x‖₊ : ENNReal) ^ 2 ∂μ) := by
            rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left measurable_const,
              lintegral_const, Measure.restrict_apply_univ]
        _ ≤ _ := by gcongr
    have ht : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    have ht2 : Filter.Tendsto (fun n : ℕ => 4 * (ENNReal.ofReal (1 / ((n : ℝ) + 1)) ^ 2 * μ Q +
        ENNReal.ofReal (1 / ((n : ℝ) + 1)))) Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul ((ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) ht)
        (Or.inr hQfin)).add ht) (a := (4 : ENNReal)) (Or.inr (by norm_num))
      simpa using this
    have hzero : ∫⁻ x in Q, a x ∂μ = 0 := le_antisymm (ge_of_tendsto' ht2 hbound) (zero_le)
    have hm : AEStronglyMeasurable (fun x => F (Matrix.of x) - g x) (μ.restrict Q) :=
      hFm.restrict.sub (hg Q hQ)
    have hae := (lintegral_eq_zero_iff' (hm.nnnorm.aemeasurable.coe_nnreal_ennreal.pow_const 2)).1 hzero
    filter_upwards [hae] with x hx
    simpa [ha, sub_eq_zero] using hx
  refine ⟨F, hFc, ?_, hF⟩
  have hall : ∀ n : ℕ, ∀ᵐ x ∂(μ.restrict (Metric.closedBall (0 : Mt k r) n)), F (Matrix.of x) = g x :=
    fun n => hQae _ (isCompact_closedBall _ _) Metric.isClosed_closedBall.measurableSet
  have := (ae_restrict_iUnion_iff _ _).2 hall
  rwa [Metric.iUnion_closedBall_nat, Measure.restrict_univ] at this

end GlobalTheory.SgInf.RegLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDerivPhiConj
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.PhiConjDeriv

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma analyticAt_Phi (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Omega n) :
    AnalyticAt ℂ (Phi lam) z := by
  have h := GlobalTheory.PhiEigenfun.analytic_Phi lam (1 : Matrix (Fin n) (Fin n) ℂ) 1 z (by simpa using hz)
  simpa using h

lemma fderiv_Phi_single (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Omega n) {a b : Fin n}
    (hab : a < b) : fderiv ℂ (Phi lam) z (z * Matrix.single a b 1) = 0 := by
  have hne : a ≠ b := ne_of_lt hab
  have hγ : HasDerivAt (fun t : ℂ => z + t • (z * Matrix.single a b 1)) (z * Matrix.single a b 1) 0 := by
    have h0 := ((hasDerivAt_id' (0 : ℂ)).smul_const (z * Matrix.single a b 1)).const_add z
    rwa [one_smul] at h0
  have hP : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) z) (z + (0 : ℂ) • (z * Matrix.single a b 1)) := by
    rw [zero_smul, add_zero]
    exact (analyticAt_Phi lam hz).differentiableAt.hasFDerivAt
  have h1 := hP.comp_hasDerivAt (0 : ℂ) hγ
  have hc : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 := by
    have hca : ContinuousAt (fun t : ℂ => 1 + t) 0 := (continuous_const.add continuous_id).continuousAt
    exact hca.eventually_ne (by norm_num)
  have hev : (fun t : ℂ => Phi lam (z + t • (z * Matrix.single a b 1))) =ᶠ[nhds 0] fun _ => Phi lam z := by
    filter_upwards [hc] with t ht
    have hm := GlobalTheory.PhiEigenfun.Phi_mul_single lam hz hab.le ht
    rw [if_neg hne, one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at hm
    exact hm
  have h2 : HasDerivAt (fun t : ℂ => Phi lam (z + t • (z * Matrix.single a b 1))) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (Phi lam z)).congr_of_eventuallyEq hev
  exact h1.unique h2

def sgn (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

lemma star_entry {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (a b : Fin n) :
    star (Y a b) = -(sgn ε b * sgn ε a) * Y b a := by
  have h' : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 := congrFun (congrFun h' b) a
  simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h1
  unfold sgn
  rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp only [ha, hb, if_true, if_false, Bool.false_eq_true] at h1 ⊢ <;>
    first | linear_combination h1 | linear_combination -h1

lemma inG_conj {ε : Fin n → Bool} {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hX : inG ε X) :
    inG ε (k⁻¹ * X * k) := by
  obtain ⟨hu, hJ⟩ := hk
  have hkk : kᴴ * k = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
  have hJ' : Jm ε * kᴴ = kᴴ * Jm ε := by
    have h2 := congrArg Matrix.conjTranspose hJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at h2
    exact h2
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  show (k⁻¹ * X * k)ᴴ * Jm ε + Jm ε * (k⁻¹ * X * k) = 0
  rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc kᴴ * (Xᴴ * k) * Jm ε + Jm ε * (kᴴ * X * k)
      = kᴴ * Xᴴ * (k * Jm ε) + Jm ε * kᴴ * X * k := by simp only [Matrix.mul_assoc]
    _ = kᴴ * (Xᴴ * Jm ε + Jm ε * X) * k := by
        rw [hJ, hJ']; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

theorem exists_deriv_Phi_conj : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), ∃ l : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ c d z, d < c → l c d z = 0) ∧ (∀ c d, ContinuousOn (l c d) (Omega n)) ∧ ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, k⁻¹ * g * k ∈ Omega n → ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → HasDerivAt (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star)) (∑ c, ∑ d, (k⁻¹ * X * k) c d * l c d (k⁻¹ * g * k)) 0 := by
  intro n ε lam
  refine ⟨fun c d z => if d < c then 0 else
    -(sgn ε c * sgn ε d) * star (fderiv ℂ (Phi lam) z (z * Matrix.single d c 1)), ?_, ?_, ?_⟩
  · intro c d z hdc
    simp only [hdc, if_true]
  · intro c d
    by_cases hdc : d < c
    · simp only [hdc, if_true]
      exact continuousOn_const
    · simp only [hdc, if_false]
      have hA : AnalyticOnNhd ℂ (Phi lam) (Omega n) := fun z hz => analyticAt_Phi lam hz
      have hF : ContinuousOn (fderiv ℂ (Phi lam)) (Omega n) := hA.fderiv.continuousOn
      have hv : ContinuousOn (fun z : Matrix (Fin n) (Fin n) ℂ => z * Matrix.single d c 1) (Omega n) :=
        (continuous_id.matrix_mul continuous_const).continuousOn
      exact continuousOn_const.mul (hF.clm_apply hv).star
  · intro k hk g hg hw X hX
    have hkk : kᴴ * k = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hk.1
    have hkk' : k * kᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hk.1
    have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
    have hYG : inG ε (k⁻¹ * X * k) := inG_conj hk hX

    let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℂ k⁻¹).comp (LinearMap.mulRight ℂ k))
    have hL : ∀ M, L M = k⁻¹ * (M * k) := fun M => rfl
    have hcurve : HasDerivAt (fun s : ℂ => k⁻¹ * (g * NormedSpace.exp (s • X)) * k)
        ((k⁻¹ * g * k) * (k⁻¹ * X * k)) 0 := by
      have h0 := L.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (GlobalTheory.PhiEigenfun.hasDerivAt_curve g X)
      have hLgX : L (g * X) = (k⁻¹ * g * k) * (k⁻¹ * X * k) := by
        rw [hL, hinv]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc k kᴴ (X * k), hkk', Matrix.one_mul]
      refine (h0.congr_deriv hLgX).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      exact Matrix.mul_assoc _ _ _
    have hP : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) (k⁻¹ * g * k))
        (k⁻¹ * (g * NormedSpace.exp ((0 : ℂ) • X)) * k) := by
      rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
      exact (analyticAt_Phi lam hw).differentiableAt.hasFDerivAt
    have hφ := hP.comp_hasDerivAt (0 : ℂ) hcurve
    have hφ' : HasDerivAt (fun s : ℂ => Phi lam (k⁻¹ * (g * NormedSpace.exp (s • X)) * k))
        (fderiv ℂ (Phi lam) (k⁻¹ * g * k) ((k⁻¹ * g * k) * (k⁻¹ * X * k))) ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]
      exact hφ
    have hst := hφ'.comp_ofReal.star

    have hexp : ∀ (w Y : Matrix (Fin n) (Fin n) ℂ), fderiv ℂ (Phi lam) w (w * Y) =
        ∑ c, ∑ d, Y c d * fderiv ℂ (Phi lam) w (w * Matrix.single c d 1) := by
      intro w Y
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      have hs : Matrix.single c d (Y c d) = Y c d • Matrix.single c d (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, Matrix.mul_smul, map_smul, smul_eq_mul]
    have hD0 : ∀ c d : Fin n, d < c → fderiv ℂ (Phi lam) (k⁻¹ * g * k) ((k⁻¹ * g * k) * Matrix.single d c 1) = 0 :=
      fun c d h => fderiv_Phi_single lam hw h
    have hfun : (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star)) =
        fun t : ℝ => star (Phi lam (k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k)) := by
      funext t
      exact GlobalTheory.Dec.FormF.Phi_star lam _
    rw [hfun]
    refine hst.congr_deriv ?_
    rw [hexp, star_sum]
    simp only [star_sum, star_mul', star_entry hYG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rw [hD0 _ _ h]
      simp
    · ring

end GlobalTheory.PhiConjDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsQuotMeas
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgQuot

theorem isMatGroup_GG (k r : ℕ) : PI.IsMatGroup (GG k r) := by

  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact ⟨⟨_, _, h, (mul_comm _ _).trans h⟩, rfl⟩
  obtain ⟨h1, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ _ hH
  refine ⟨?_, h1, hmul, fun a ha => ⟨(hinv a ha).2, Matrix.mul_nonsing_inv a (hinv a ha).1⟩⟩

  show IsClosed {g : Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem exists_isQuotMeas : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS : Measure (Mt k r)), IsClosedSub k r S →
    IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r S μG μS hS hG hSμ hU
  obtain ⟨hSG, hcl, h1, hmul, hinv⟩ := hS

  have hSm : PI.IsMatGroup S :=
    ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ((isMatGroup_GG k r).2.2.2 a (hSG ha)).2⟩⟩

  exact GlobalTheory.QuotWeil.exists_isQuotM (2 * r + k + 1) (GG k r) S μG μS (isMatGroup_GG k r) hSm hSG hG hSμ hU.1

end GlobalTheory.SgQuot
end

