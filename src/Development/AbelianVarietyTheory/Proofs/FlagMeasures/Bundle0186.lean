module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Dec.FormF
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec

variable {n : ℕ}

theorem posDef_mem_Omega {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : x ∈ Omega n := by
  intro i
  have hsub : (x.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)).PosDef :=
    hx.submatrix (Fin.castLE_injective _)
  exact hsub.det_pos.ne'

theorem posDef_mem_kConjNonzeroMinorsSet (ε : Fin n → Bool) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : x ∈ U1 ε := by
  intro k hk
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk.1
  rw [Matrix.inv_eq_left_inv hu, Matrix.star_eq_conjTranspose]
  apply posDef_mem_Omega
  apply hx.conjTranspose_mul_mul_same
  intro v v' h
  have h2 := congrArg (fun u => (star k).mulVec u) h
  simpa only [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec] using h2

theorem continuous_leadMinor_conj (ε : Fin n → Bool) (l : ℕ) (hl : l ≤ n) :
    Continuous (fun p : KG ε × (Fin n → Fin n → ℂ) =>
      leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) l hl) := by
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k =>
    Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp ((mem_KG ε _).1 k.2).1)
  simp_rw [hinv]
  unfold leadMinor
  have hc : Continuous (fun k : KG ε => toMK k) := toMK_cont ε
  have hz : Continuous (fun p : KG ε × (Fin n → Fin n → ℂ) => Matrix.of p.2) := continuous_snd
  exact ((((hc.comp continuous_fst).matrix_conjTranspose).matrix_mul hz).matrix_mul
    (hc.comp continuous_fst)).matrix_submatrix _ _ |>.matrix_det

theorem isOpen_kConjNonzeroMinorsSet (ε : Fin n → Bool) : IsOpen {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
  have hset : {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} =
      (Prod.snd '' {p : KG ε × (Fin n → Fin n → ℂ) | ∃ i : Fin n,
        leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0})ᶜ := by
    ext z
    constructor
    · rintro hz ⟨⟨k, z'⟩, ⟨i, hi⟩, rfl⟩
      exact hz (toMK k) ((mem_KG ε _).1 k.2) i hi
    · intro hz g hg i hi
      obtain ⟨k, rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
      exact hz ⟨⟨k, z⟩, ⟨i, hi⟩, rfl⟩
  rw [hset, isOpen_compl_iff]
  refine isClosedMap_snd_of_compactSpace _ ?_
  have hu : {p : KG ε × (Fin n → Fin n → ℂ) | ∃ i : Fin n,
      leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0} =
      ⋃ i : Fin n, {p | leadMinor ((toMK p.1)⁻¹ * Matrix.of p.2 * toMK p.1) (i.val + 1) i.isLt = 0} := by
    ext p; simp
  rw [hu]
  exact isClosed_iUnion_of_finite fun i =>
    isClosed_eq (continuous_leadMinor_conj ε (i.val + 1) i.isLt) continuous_const

theorem differentiable_leadMinor_mul (a b : Matrix (Fin n) (Fin n) ℂ) (l : ℕ) (hl : l ≤ n) :
    Differentiable ℂ (fun z : Fin n → Fin n → ℂ => leadMinor (a * Matrix.of z * b) l hl) := by
  unfold leadMinor
  simp only [Matrix.det_apply', Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem IsTau.isURepOn {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w) :
    IsURepOn (Kset ε) τ := by
  obtain ⟨hfd, ⟨h1, hmul⟩, hdiff, hadj, -⟩ := h
  have hsub : ∀ g ∈ Formalism.REAL.Kset ε, g ∈ KC ε := fun g hg =>
    ⟨⟨⟨g, star g, Matrix.mem_unitaryGroup_iff.mp hg.1, Matrix.mem_unitaryGroup_iff'.mp hg.1⟩, rfl⟩, hg.2⟩
  refine ⟨⟨h1, fun a ha b hb => hmul a (hsub a ha) b (hsub b hb)⟩, ?_, ?_⟩
  · intro g hg v
    have hs : star g ∈ Formalism.REAL.Kset ε := Formalism.REAL.Kset_star ε hg
    have hgg : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hg.1
    have hc : (τ (star g)).comp (τ g) = 1 := by
      rw [← hmul _ (hsub _ hs) _ (hsub _ hg), hgg, h1]
    have hv : τ (star g) (τ g v) = v := by
      rw [← ContinuousLinearMap.comp_apply, hc, ContinuousLinearMap.one_apply]
    have hi : ⟪τ g v, τ g v⟫_ℂ = ⟪v, v⟫_ℂ := by
      rw [hadj g (hsub g hg) v (τ g v), ← Matrix.star_eq_conjTranspose, hv]
    have h2 : ‖τ g v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ) v, hi]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  · intro v
    haveI := hfd
    let bs := stdOrthonormalBasis ℂ W
    have hco : ∀ u : W, ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ g v⟫_ℂ)
        (Formalism.REAL.Kset ε) :=
      fun u => (hdiff u v).continuousOn.mono (fun g hg => hsub g hg)
    have heq : (fun g => τ g v) = fun g => ∑ i, ⟪bs i, τ g v⟫_ℂ • bs i := by
      funext g; exact (bs.sum_repr' (τ g v)).symm
    rw [heq]
    exact continuousOn_finsetSum _ fun i _ => (hco (bs i)).smul continuousOn_const

theorem psBasic : PsBasic := by
  intro n ε lam W _ _ τ w _hlam htau
  have hrep : IsURepOn (Formalism.REAL.Kset ε) τ := htau.isURepOn
  obtain ⟨hfd, -, -, -, hirr, hw, -⟩ := htau
  haveI := hfd
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hK : ∀ k : KG ε, toMK k ∈ Formalism.REAL.Kset ε := fun k => (mem_KG ε _).1 k.2
  have hinv : ∀ k : KG ε, (toMK k)⁻¹ = star (toMK k) := fun k =>
    Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp (hK k).1)
  have hτc : Continuous (fun k : KG ε => τ (toMK k) w) :=
    (hrep.2.2 w).comp_continuous (toMK_cont ε) hK
  have hPc : Continuous (fun k : KG ε => (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) := by
    have := (ContinuousLinearMap.smulRightL ℂ W W).continuous₂.comp₂ ((innerSL ℂ).continuous.comp hτc) hτc
    exact this
  refine ⟨isOpen_kConjNonzeroMinorsSet ε, fun x hx => posDef_mem_kConjNonzeroMinorsSet ε hx, ?_, ?_⟩
  · have hU := isOpen_kConjNonzeroMinorsSet ε
    have hmem : ∀ k : KG ε, ∀ z ∈ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}, ∀ i : Fin n,
        leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ≠ 0 :=
      fun k z hz i => hz (toMK k) (hK k) i
    have hcont : ContinuousOn (Function.uncurry fun (k : KG ε) (z : Fin n → Fin n → ℂ) =>
        Phi lam ((toMK k)⁻¹ * Matrix.of z * toMK k) •
          (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w))
        (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) := by
      show ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
        Phi lam ((toMK q.1)⁻¹ * Matrix.of q.2 * toMK q.1) •
          (innerSL ℂ (τ (toMK q.1) w)).smulRight (τ (toMK q.1) w)) _
      have hA : ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
          Phi lam ((toMK q.1)⁻¹ * Matrix.of q.2 * toMK q.1))
          (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) := by
        unfold Phi
        exact continuousOn_finsetProd _ fun i _ =>
          (continuous_leadMinor_conj ε (i.val + 1) i.isLt).continuousOn.zpow₀ _
            fun q hq => Or.inl (hmem q.1 q.2 hq.2 i)
      have hB : ContinuousOn (fun q : KG ε × (Fin n → Fin n → ℂ) =>
          (innerSL ℂ (τ (toMK q.1) w)).smulRight (τ (toMK q.1) w))
          (Set.univ ×ˢ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε}) :=
        (hPc.comp continuous_fst).continuousOn
      exact hA.smul hB
    have hdiff : ∀ k : KG ε, DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
        Phi lam ((toMK k)⁻¹ * Matrix.of z * toMK k) •
          (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w))
        {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
      intro k
      apply DifferentiableOn.smul_const
      unfold Phi
      have hg : ∀ i : Fin n, DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
          leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ^ (-(sInt lam i)))
          {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := fun i =>
        ((differentiable_leadMinor_mul _ _ (i.val + 1) i.isLt).differentiableOn).zpow
          (Or.inl fun z hz => hmem k z hz i)
      have hprod : ∀ s : Finset (Fin n), DifferentiableOn ℂ (fun z : Fin n → Fin n → ℂ =>
          ∏ i ∈ s, leadMinor ((toMK k)⁻¹ * Matrix.of z * toMK k) (i.val + 1) i.isLt ^ (-(sInt lam i)))
          {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · simp only [Finset.prod_empty]
          exact differentiableOn_const _
        · intro a s ha ih
          simp only [Finset.prod_insert ha]
          exact (hg a).mul ih
      exact hprod Finset.univ
    have hint := (GlobalTheory.differentiableOn_integral_of_holomorphic_of_continuousOn (μ := muK ε) hU hcont hdiff).1
    unfold ps
    exact DifferentiableOn.congr (hint.const_smul (Module.finrank ℂ W : ℂ)) fun z _ => rfl
  · have hI : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : KG ε → E), Continuous f →
        Integrable f (muK ε) := fun f hf =>
      integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
    have h1 : ∀ k : KG ε, Phi lam ((toMK k)⁻¹ * 1 * toMK k) = 1 := fun k => by
      rw [hinv, Matrix.mul_one, Matrix.mem_unitaryGroup_iff'.mp (hK k).1, Phi_at_one]
    unfold ps
    simp_rw [h1, one_smul]
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    obtain ⟨c, -, hc⟩ := avgSchur n ε W τ w hfd hrep hirr hw0
    have hnorm : ∀ k : KG ε, ‖τ (toMK k) w‖ = 1 := fun k => by rw [hrep.2.1 _ (hK k), hw]
    let b := stdOrthonormalBasis ℂ W
    have hsum : (Module.finrank ℂ W : ℂ) * c = 1 := by
      have e1 : ∀ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) = c := by
        intro i
        have hbi : ⟪b i, b i⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
        have := hc (b i) (innerSL ℂ (b i))
        simp only [show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl, hbi, mul_one] at this
        exact this
      have e2 : ∑ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) = 1 := by
        rw [← MeasureTheory.integral_finsetSum _ fun i _ => hI (fun k : KG ε => ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ)
          ((hτc.inner continuous_const).mul (continuous_const.inner hτc))]
        simp_rw [b.sum_inner_mul_inner]
        have hone : ∀ k : KG ε, ⟪τ (toMK k) w, τ (toMK k) w⟫_ℂ = 1 := fun k => by
          rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
        simp_rw [hone]
        simp
      simp_rw [e1] at e2
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using e2
    ext u
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply (hI _ hPc),
      ContinuousLinearMap.id_apply]
    simp only [ContinuousLinearMap.smulRight_apply, show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl]
    apply ext_inner_left ℂ
    intro y
    rw [inner_smul_right, ← integral_inner (hI (fun k : KG ε => ⟪τ (toMK k) w, u⟫_ℂ • τ (toMK k) w)
      ((hτc.inner continuous_const).smul hτc))]
    simp_rw [inner_smul_right]
    have := hc u (innerSL ℂ y)
    simp only [show ∀ a b : W, (innerSL ℂ a) b = ⟪a, b⟫_ℂ from fun _ _ => rfl] at this
    rw [this, ← mul_assoc, hsum, one_mul]

end GlobalTheory.Dec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevIneqTranslateCompact
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInf.SobTranslate

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_mulLeft {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => a * g) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)).contDiff

theorem inUH_mul {n : ℕ} {H a g : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hg : inUH H g) :
    inUH H (a * g) := by
  unfold inUH at *
  rw [conjTranspose_mul]
  calc gᴴ * aᴴ * H * (a * g) = gᴴ * (aᴴ * H * a) * g := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha, hg]

theorem smoothOnH_translate {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H a : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) : SmoothOnH H (fun g => f (a * g)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (a * g₀) (inUH_mul ha hg₀)
  have hc := contDiff_mulLeft a
  refine ⟨(fun g => a * g) ⁻¹' U, fun g => F (a * g), hU.preimage hc.continuous, hgU, ?_, ?_⟩
  · exact hF.comp hc.contDiffOn (fun _ h => h)
  · intro g hg hgH
    exact hfF _ hg (inUH_mul ha hgH)

end Smooth

theorem rdWord_translate {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : Matrix (Fin m) (Fin m) ℂ) (ws : List (Matrix (Fin m) (Fin m) ℂ))
    (f : Matrix (Fin m) (Fin m) ℂ → V) :
    rdWord ws (fun g => f (a * g)) = fun g => rdWord ws f (a * g) := by
  induction ws with
  | nil => rfl
  | cons X w ih =>
    funext g
    show rdM X (rdWord w _) g = rdM X (rdWord w f) (a * g)
    rw [ih]
    simp only [rdM, Matrix.mul_assoc]

variable {k r : ℕ}

theorem inv_of_mem {a : Mat k r} (ha : a ∈ GG k r) : a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 := by
  by_cases hdet : IsUnit a.det
  · exact ⟨Matrix.mul_nonsing_inv a hdet, Matrix.nonsing_inv_mul a hdet⟩
  · exfalso
    have h0 : a⁻¹ ∈ GG k r := (gg_closedSub k r).2.2.2.2 a ha
    rw [Matrix.nonsing_inv_apply_not_isUnit a hdet] at h0
    have h1 : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := h0
    let i : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩
    have h2 : Hpk k r i i = -1 := by simp [Hpk, i]
    rw [← h1] at h2
    simp at h2

theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem measurableEmbedding_lmul {a b : Mat k r} (hab : a * b = 1) (hba : b * a = 1) :
    MeasurableEmbedding (lmulM a : Mt k r → Mt k r) := by
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := lmulM a
      invFun := lmulM b
      left_inv := fun x => by
        show b * (a * Matrix.of x) = x
        rw [← Matrix.mul_assoc, hba, Matrix.one_mul]
        rfl
      right_inv := fun x => by
        show a * (b * Matrix.of x) = x
        rw [← Matrix.mul_assoc, hab, Matrix.one_mul]
        rfl
      continuous_toFun := continuous_lmul a
      continuous_invFun := continuous_lmul b }
  exact e.measurableEmbedding

theorem lintegral_translate_le {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ) {a : Mat k r}
    (ha : a ∈ GG k r) {K₀ K₂ : Set (Mt k r)} (hK : ∀ y ∈ K₀, lmulM a y ∈ K₂)
    (φ : Mt k r → ENNReal) :
    ∫⁻ y in K₀, φ (lmulM a y) ∂μ ≤ ∫⁻ y in K₂, φ y ∂μ := by
  have hemb := measurableEmbedding_lmul (inv_of_mem ha).1 (inv_of_mem ha).2
  have hmap : μ.map (lmulM a) = μ := hμ.2.2.2 a ha
  calc ∫⁻ y in K₀, φ (lmulM a y) ∂μ ≤ ∫⁻ y in lmulM a ⁻¹' K₂, φ (lmulM a y) ∂μ :=
        lintegral_mono_set hK
    _ = ∫⁻ y, φ y ∂((μ.restrict (lmulM a ⁻¹' K₂)).map (lmulM a)) :=
        (hemb.lintegral_map _).symm
    _ = ∫⁻ y in K₂, φ y ∂μ := by
        rw [← hemb.restrict_map, hmap]

theorem ofReal_integral_le {α : Type*} [MeasurableSpace α] (ν : Measure α) (g : α → ℝ)
    (hg : ∀ y, 0 ≤ g y) : ENNReal.ofReal (∫ y, g y ∂ν) ≤ ∫⁻ y, ENNReal.ofReal (g y) ∂ν := by
  by_cases h : AEStronglyMeasurable g ν
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg) h]
    exact ENNReal.ofReal_toReal_le
  · rw [integral_non_aestronglyMeasurable h]
    simp

theorem list_sum_ofReal {α : Type*} (l : List α) (u : α → ℝ) (v : α → ENNReal) (hu : ∀ a, 0 ≤ u a)
    (h : ∀ a ∈ l, ENNReal.ofReal (u a) ≤ v a) :
    0 ≤ (l.map u).sum ∧ ENNReal.ofReal (l.map u).sum ≤ (l.map v).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h0, h1⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons]
    refine ⟨add_nonneg (hu a) h0, ?_⟩
    rw [ENNReal.ofReal_add (hu a) h0]
    exact add_le_add (h a List.mem_cons_self) h1

theorem sobolev_translate : ∀ (k r : ℕ) (μ : Measure (Mt k r)) (C₀ : ℝ) (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsHaarOn (GG k r) μ → IsCompact K₀ → (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C₀ * (Ws.map fun ws => ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μ).sum) → ∀ Q : Set (Mt k r), IsCompact Q → ∃ K₂ : Set (Mt k r), IsCompact K₂ ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → (∀ ws ∈ Ws, ContinuousOn (rdWord ws f) (GG k r)) → ∀ x ∈ Q, Matrix.of x ∈ GG k r → ENNReal.ofReal (‖f (Matrix.of x)‖ ^ 2) ≤ ENNReal.ofReal |C₀| * (Ws.map fun ws => ∫⁻ y in K₂, (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2 ∂μ).sum := by
  intro k r μ C₀ Ws K₀ hμ hK₀ hS Q hQ
  let pr : Mt k r × Mt k r → Mt k r := fun p => lmulM (Matrix.of p.1) p.2
  have hpr : Continuous pr := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [pr, lmulM, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  refine ⟨pr '' (Q ×ˢ K₀), (hQ.prod hK₀).image hpr, ?_⟩
  intro B _ _ _ f hf _ x hxQ hxG
  have hsm : SmoothOnH (Hpk k r) (fun g => f (Matrix.of x * g)) :=
    smoothOnH_translate (a := Matrix.of x) hxG hf
  have hkey := hS B (fun g => f (Matrix.of x * g)) hsm
  simp only [Matrix.mul_one, rdWord_translate] at hkey
  obtain ⟨hS0, hSum⟩ := list_sum_ofReal Ws
    (fun ws => ∫ y in K₀, ‖rdWord ws f (Matrix.of x * Matrix.of y)‖ ^ 2 ∂μ)
    (fun ws => ∫⁻ y in pr '' (Q ×ˢ K₀), (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2 ∂μ)
    (fun _ => integral_nonneg fun _ => by positivity)
    (fun ws _ => by
      refine (ofReal_integral_le _ _ fun _ => by positivity).trans ?_
      have hφ := lintegral_translate_le hμ (a := Matrix.of x) hxG (K₀ := K₀)
        (K₂ := pr '' (Q ×ˢ K₀)) (fun y hy => ⟨(x, y), ⟨hxQ, hy⟩, rfl⟩)
        (fun y => (‖rdWord ws f (Matrix.of y)‖₊ : ENNReal) ^ 2)
      refine le_trans (le_of_eq ?_) hφ
      refine lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      rfl)
  calc ENNReal.ofReal (‖f (Matrix.of x)‖ ^ 2)
      ≤ ENNReal.ofReal (|C₀| * (Ws.map fun ws =>
          ∫ y in K₀, ‖rdWord ws f (Matrix.of x * Matrix.of y)‖ ^ 2 ∂μ).sum) :=
        ENNReal.ofReal_le_ofReal (hkey.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hS0))
    _ = ENNReal.ofReal |C₀| * ENNReal.ofReal (Ws.map fun ws =>
          ∫ y in K₀, ‖rdWord ws f (Matrix.of x * Matrix.of y)‖ ^ 2 ∂μ).sum :=
        ENNReal.ofReal_mul (abs_nonneg _)
    _ ≤ _ := by gcongr

end GlobalTheory.SgInf.SobTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoVolumeSublevelDivPow
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem volume_sum_sq_le_sq (d : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ s ^ 2}
      = ENNReal.ofReal (s ^ d) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have h1 : {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ s ^ 2}
      = (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) ⁻¹' Metric.closedBall 0 s := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall_zero_iff,
      EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
    rw [Real.sqrt_le_left hs]
  rw [h1, (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet, Measure.addHaar_closedBall _ _ hs]
  simp

theorem tendsto_volume_sublevel_div_pow (d : ℕ) (N : (Fin d → ℝ) → ℝ) (hc : ContinuousAt N 0)
    (h0 : N 0 = 0) (hl : ∀ x, ∑ i, x i ^ 2 ≤ N x) (hu : ∀ x, N x ≤ ∑ i, x i ^ 2 + N x ^ 2 / 4) :
    Filter.Tendsto (fun r : ℝ => volume {x : Fin d → ℝ | Real.sqrt (N x) ≤ r} /
        ENNReal.ofReal (r ^ d)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) := by
  set V := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hV
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  rw [tendsto_order]
  constructor
  · intro a ha
    have hcont : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d) * V) (nhds 1) (nhds V) := by
      have h1 : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ d)) (nhds 1) (nhds 1) := by
        have : Continuous (fun t : ℝ => ENNReal.ofReal (t ^ d)) :=
          ENNReal.continuous_ofReal.comp (continuous_pow d)
        simpa using this.tendsto 1
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hVt)
    have hev : ∀ᶠ t : ℝ in nhdsWithin 1 (Set.Iio 1), a < ENNReal.ofReal (t ^ d) * V ∧ 0 < t :=
      nhdsWithin_le_nhds ((hcont.eventually (lt_mem_nhds ha)).and (lt_mem_nhds one_pos))
    obtain ⟨t, ⟨hta, ht0⟩, ht1⟩ := (hev.and self_mem_nhdsWithin).exists
    have ht1 : t < 1 := ht1
    have hδ : 0 < 4 * (1 - t ^ 2) := by nlinarith
    have hN : ∀ᶠ x in nhds (0 : Fin d → ℝ), N x < 4 * (1 - t ^ 2) :=
      hc.eventually (gt_mem_nhds (by rw [h0]; exact hδ))
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hN
    have hr : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), r < η :=
      nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hr, self_mem_nhdsWithin] with r hrη hr0
    have hr0 : 0 < r := hr0
    refine hta.trans_le ?_
    have hp : ENNReal.ofReal (r ^ d) ≠ 0 := by
      simpa using pow_pos hr0 d
    rw [ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top)]
    have e : ENNReal.ofReal (t ^ d) * V * ENNReal.ofReal (r ^ d)
        = volume {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ (t * r) ^ 2} := by
      rw [volume_sum_sq_le_sq d (by positivity), mul_pow,
        ENNReal.ofReal_mul (by positivity), ← hV]
      ring
    rw [e]
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    have htr : t * r < η := by nlinarith
    have hx' : dist x 0 < η := by
      rw [dist_zero_right]
      refine lt_of_le_of_lt ?_ htr
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      have : x i ^ 2 ≤ (t * r) ^ 2 :=
        (Finset.single_le_sum (f := fun i => x i ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)).trans hx
      exact abs_le_of_sq_le_sq this (by positivity)
    have h1 := hball hx'
    have h2 := hu x
    have h3 : 0 ≤ N x := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans (hl x)
    rw [Real.sqrt_le_left hr0.le]
    have h4 : t ^ 2 * N x ≤ t ^ 2 * r ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1.le h3
      nlinarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with r hr0
    have hr0 : 0 < r := hr0
    refine lt_of_le_of_lt ?_ ha
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm, ← volume_sum_sq_le_sq d hr0.le]
    refine measure_mono fun x hx => ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Real.sqrt_le_left hr0.le] at hx
    exact (hl x).trans hx

end GlobalTheory
end

