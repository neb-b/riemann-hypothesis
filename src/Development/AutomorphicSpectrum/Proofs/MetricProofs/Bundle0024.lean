module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicLocalQuotientMap
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Metric.QuotHol

theorem differentiableOn_det {m n : ℕ} {A : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    {V : Set (Fin n → ℂ)} (hA : ∀ i j, DifferentiableOn ℂ (fun t => A t i j) V) :
    DifferentiableOn ℂ (fun t => (A t).det) V := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_smul ?_ _
  have hs : ∀ s : Finset (Fin m), DifferentiableOn ℂ (fun t => ∏ i ∈ s, A t (σ i) i) V := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact differentiableOn_const _
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).fun_mul ih
  exact hs Finset.univ

theorem exists_complement {k g' : ℕ} (v : Fin k → Fin (k + g') → ℂ)
    (hv : LinearIndependent ℂ v) :
    ∃ f : Fin g' → Fin (k + g') → ℂ,
      (Matrix.of fun i j => Sum.elim v f (finSumFinEquiv.symm j) i :
        Matrix (Fin (k + g')) (Fin (k + g')) ℂ).det ≠ 0 := by
  classical
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (Submodule.span ℂ (Set.range v))
  have hfr : Module.finrank ℂ W' = g' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW'
    have h2 := finrank_span_eq_card hv
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1 h2
    omega
  let bW := Module.finBasisOfFinrankEq ℂ W' hfr
  let f : Fin g' → Fin (k + g') → ℂ := fun j => (bW j : Fin (k + g') → ℂ)
  have hf : LinearIndependent ℂ f :=
    bW.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hdisj : Disjoint (Submodule.span ℂ (Set.range v)) (Submodule.span ℂ (Set.range f)) := by
    refine hW'.disjoint.mono_right ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (bW j).2
  have hs : LinearIndependent ℂ (Sum.elim v f) := hv.sum_type hf hdisj
  have hc := hs.comp _ (finSumFinEquiv.symm.injective)
  refine ⟨f, ?_⟩
  have hu := Matrix.linearIndependent_cols_iff_isUnit
    (A := (Matrix.of fun i j => Sum.elim v f (finSumFinEquiv.symm j) i :
      Matrix (Fin (k + g')) (Fin (k + g')) ℂ)) |>.1 hc
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem exists_holomorphic_quotient (g' k g n : ℕ) (U : Set (Fin n → ℂ))
    (e : Fin k → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (hU : IsOpen U) (ht₀ : t₀ ∈ U)
    (hg : k + g' = g) (he : ∀ i, DifferentiableOn ℂ (e i) U)
    (hli : LinearIndependent ℂ (fun i => e i t₀)) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ U ∧
      ∃ q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ),
        (∀ x, DifferentiableOn ℂ (fun t => q t x) V) ∧
        ∀ t ∈ V, Function.Surjective (q t) ∧
          LinearMap.ker (q t) = Submodule.span ℂ (Set.range fun i => e i t) := by
  classical
  subst hg
  obtain ⟨f, hf⟩ := exists_complement (fun i => e i t₀) hli
  let M : (Fin n → ℂ) → Matrix (Fin (k + g')) (Fin (k + g')) ℂ := fun t =>
    Matrix.of fun i j => Sum.elim (fun a => e a t) f (finSumFinEquiv.symm j) i
  have hMc : ∀ t a i, M t i (Fin.castAdd g' a) = e a t i := by
    intro t a i
    simp [M]
  have hMn : ∀ t b i, M t i (Fin.natAdd k b) = f b i := by
    intro t b i
    simp [M]
  have hMent : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) U := by
    intro i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with a | c
    · simp only [finSumFinEquiv_apply_left, hMc]
      exact (differentiableOn_pi.1 (he a)) i
    · simp only [finSumFinEquiv_apply_right, hMn]
      exact differentiableOn_const _
  have hdet : DifferentiableOn ℂ (fun t => (M t).det) U := differentiableOn_det hMent
  let V : Set (Fin n → ℂ) := U ∩ (fun t => (M t).det) ⁻¹' {0}ᶜ
  have hVo : IsOpen V := hdet.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hVU : V ⊆ U := Set.inter_subset_left
  have hinv : ∀ i j, DifferentiableOn ℂ (fun t => (M t)⁻¹ i j) V := by
    intro i j
    have h1 : DifferentiableOn ℂ (fun t => ((M t).det)⁻¹) V :=
      (hdet.mono hVU).inv (fun t ht => ht.2)
    have h2 : DifferentiableOn ℂ (fun t => (M t).adjugate i j) V := by
      simp only [Matrix.adjugate_apply]
      refine differentiableOn_det fun a b => ?_
      by_cases h : a = j
      · subst h
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne h]
        exact (hMent a b).mono hVU
    simpa [Matrix.inv_def, Ring.inverse_eq_inv'] using h1.fun_mul h2
  let q : (Fin n → ℂ) → (Fin (k + g') → ℂ) →ₗ[ℂ] (Fin g' → ℂ) := fun t =>
    LinearMap.funLeft ℂ ℂ (Fin.natAdd k) ∘ₗ ((M t)⁻¹).mulVecLin
  have hq : ∀ t x j, q t x j = ((M t)⁻¹ *ᵥ x) (Fin.natAdd k j) := by
    intro t x j
    simp [q, LinearMap.funLeft_apply]
  refine ⟨V, hVo, ⟨ht₀, hf⟩, hVU, q, ?_, ?_⟩
  · intro x
    refine differentiableOn_pi.2 fun j => ?_
    simp only [hq, Matrix.mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun l _ => (hinv _ l).mul_const _
  · intro t ht
    have hu : IsUnit (M t).det := isUnit_iff_ne_zero.2 ht.2
    have hMi : M t * (M t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    have hiM : (M t)⁻¹ * M t = 1 := Matrix.nonsing_inv_mul _ hu
    refine ⟨fun y => ?_, ?_⟩
    · refine ⟨M t *ᵥ (fun j => Sum.elim 0 y (finSumFinEquiv.symm j)), ?_⟩
      ext j
      rw [hq, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]
      simp
    · apply le_antisymm
      · intro x hx
        have hx0 : ∀ j, ((M t)⁻¹ *ᵥ x) (Fin.natAdd k j) = 0 := by
          intro j
          rw [← hq, LinearMap.mem_ker.1 hx]
          rfl
        have hxc : x = M t *ᵥ ((M t)⁻¹ *ᵥ x) := by
          rw [Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
        obtain ⟨c, hc⟩ : ∃ c, c = (M t)⁻¹ *ᵥ x := ⟨_, rfl⟩
        rw [← hc] at hx0 hxc
        have hsum : x = ∑ a, c (Fin.castAdd g' a) • e a t := by
          conv_lhs => rw [hxc]
          ext i
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, hx0, mul_zero,
            Finset.sum_const_zero, add_zero, hMc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun a _ => mul_comm _ _
        rw [hsum]
        exact Submodule.sum_mem _ fun a _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        have hcol : e a t = M t *ᵥ Pi.single (Fin.castAdd g' a) 1 := by
          ext i
          simp [hMc]
        refine LinearMap.mem_ker.2 ?_
        ext j
        rw [hq]
        show ((M t)⁻¹ *ᵥ e a t) (Fin.natAdd k j) = 0
        rw [hcol, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]
        refine Pi.single_eq_of_ne ?_ _
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        have := a.2
        omega

end GlobalTheory.CompanionTheory.Metric.QuotHol
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicSpanCoefficients
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem ip_sum_right (R : RiemLat E g Λ) {k : ℕ} (x : Fin g → ℂ) (a : Fin k → ℂ)
    (u : Fin k → Fin g → ℂ) : R.ip x (∑ j, a j • u j) = ∑ j, a j * R.ip x (u j) := by
  simp only [RiemLat.ip, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem ip_sum_left (R : RiemLat E g Λ) {k : ℕ} (a : Fin k → ℂ) (u : Fin k → Fin g → ℂ)
    (y : Fin g → ℂ) : R.ip (∑ i, a i • u i) y = ∑ i, star (a i) * R.ip (u i) y := by
  simp only [RiemLat.ip, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem star_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : star (R.ip x y) = R.ip y x := by
  have h := R.herm
  simp only [RiemLat.ip]
  rw [← star_dotProduct_star, star_mulVec, star_star, h.eq, dotProduct_comm, dotProduct_mulVec]
  exact dotProduct_comm _ _

theorem gram_comb (R : RiemLat E g Λ) {k l : ℕ} (T : Matrix (Fin l) (Fin k) ℂ)
    (u : Fin k → Fin g → ℂ) :
    R.gram (fun a => ∑ i, T a i • u i) = T.map star * R.gram u * Tᵀ := by
  ext a a'
  simp only [RiemLat.gram, Matrix.of_apply, ip_sum_left, ip_sum_right, Matrix.mul_apply,
    Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gram_comb_det (R : RiemLat E g Λ) {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ)
    (u : Fin k → Fin g → ℂ) :
    (R.gram (fun a => ∑ i, T a i • u i)).det.re = Complex.normSq T.det * (R.gram u).det.re := by
  have h1 : (T.map star).det = star T.det := by
    have : T.map star = Tᴴᵀ := by ext; simp
    rw [this, det_transpose, det_conjTranspose]
  rw [gram_comb, det_mul, det_mul, det_transpose, h1]
  have h2 : star T.det * (R.gram u).det * T.det = (Complex.normSq T.det : ℂ) * (R.gram u).det := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h2, Complex.re_ofReal_mul]

theorem sum_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ)
    (u : Fin k → V) (v : Fin k → ℂ) :
    ∑ i, v i • ∑ j, T i j • u j = ∑ j, (v ᵥ* T) j • u j := by
  simp only [Finset.smul_sum, Matrix.vecMul, dotProduct, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem det_ne_zero_of_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (T : Matrix (Fin k) (Fin k) ℂ) (u : Fin k → V)
    (hc : LinearIndependent ℂ fun i => ∑ j, T i j • u j) : T.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvT⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  funext i
  refine Fintype.linearIndependent_iff.1 hc v ?_ i
  rw [sum_comb, hvT]
  simp

theorem linearIndependent_comb {V : Type} [AddCommGroup V] [Module ℂ V] {k : ℕ}
    (T : Matrix (Fin k) (Fin k) ℂ) (u : Fin k → V) (hu : LinearIndependent ℂ u)
    (hT : T.det ≠ 0) : LinearIndependent ℂ fun i => ∑ j, T i j • u j := by
  refine Fintype.linearIndependent_iff.2 fun v hv i => ?_
  rw [sum_comb] at hv
  have h0 : v ᵥ* T = 0 := funext fun j => Fintype.linearIndependent_iff.1 hu _ hv j
  have := Matrix.eq_zero_of_vecMul_eq_zero hT h0
  simp [this]

theorem differentiableOn_det {n k : ℕ} {W : Set (Fin n → ℂ)}
    {M : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ}
    (h : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) W) :
    DifferentiableOn ℂ (fun t => (M t).det) W := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_smul ?_ _
  have h1 : ∀ s : Finset (Fin k), DifferentiableOn ℂ (fun t => ∏ i ∈ s, M t (σ i) i) W := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using differentiableOn_const (1 : ℂ)
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h _ _).mul ih
  exact h1 _

theorem gram_det_re_pos (R : RiemLat E g Λ) {k : ℕ} (u : Fin k → Fin g → ℂ)
    (hu : LinearIndependent ℂ u) : 0 < (R.gram u).det.re := by
  have hH : (R.gram u).IsHermitian := by
    ext a b
    simp only [RiemLat.gram, Matrix.conjTranspose_apply, Matrix.of_apply]
    exact star_ip R _ _
  have hq : ∀ x : Fin k → ℂ, star x ⬝ᵥ (R.gram u) *ᵥ x = R.ip (∑ i, x i • u i) (∑ i, x i • u i) := by
    intro x
    simp only [ip_sum_left, ip_sum_right, dotProduct, mulVec, RiemLat.gram, Matrix.of_apply,
      Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hP : (R.gram u).PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    rw [hq]
    set w := ∑ i, x i • u i with hw
    have hw0 : w ≠ 0 := fun h0 =>
      hx (funext (Fintype.linearIndependent_iff.1 hu x h0))
    refine Complex.pos_iff.2 ⟨R.pos w hw0, ?_⟩
    have := Complex.conj_eq_iff_im.1 (star_ip R w w)
    simpa using this.symm
  exact (Complex.pos_iff.1 hP.det_pos).1

theorem log_gram_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (n m : ℕ) (W : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (b c : Fin m → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen W → t₀ ∈ W → (∀ i, DifferentiableOn ℂ (b i) W) → (∀ i, DifferentiableOn ℂ (c i) W) → (∀ t ∈ W, LinearIndependent ℂ fun i => b i t) → (∀ t ∈ W, ∀ i, c i t ∈ Submodule.span ℂ (Set.range fun j => b j t)) → LinearIndependent ℂ (fun i => c i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧ ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G V ∧ ∀ t ∈ V, LinearIndependent ℂ (fun i => c i t) ∧ Real.log ((R t).gram fun i => c i t).det.re = Real.log ((R t).gram fun i => b i t).det.re + (G t).re := by
  intro E _ _ _ g Λ _ _ n m W R b c t₀ hW ht₀ hb hc hbi hcs hci
  have hinj : LinearMap.ker (Fintype.linearCombination ℂ fun i => b i t₀) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    rw [Fintype.linearCombination_apply] at hv
    exact funext (Fintype.linearIndependent_iff.1 (hbi t₀ ht₀) v hv)
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hφb : ∀ i, φ (b i t₀) = Pi.single i 1 := by
    intro i
    have h1 := LinearMap.congr_fun hφ (Pi.single i 1)
    simpa [Fintype.linearCombination_apply_single] using h1
  have hφd : ∀ u : (Fin n → ℂ) → Fin g → ℂ, DifferentiableOn ℂ u W →
      ∀ j, DifferentiableOn ℂ (fun t => φ (u t) j) W := by
    intro u hu j
    have h1 : DifferentiableOn ℂ (fun t => LinearMap.toContinuousLinearMap φ (u t)) W :=
      (LinearMap.toContinuousLinearMap φ).differentiable.comp_differentiableOn hu
    exact differentiableOn_pi.1 h1 j
  let Bm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ := fun t => Matrix.of fun i j => φ (b i t) j
  let Cm : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ := fun t => Matrix.of fun i j => φ (c i t) j
  have hdB : DifferentiableOn ℂ (fun t => (Bm t).det) W :=
    differentiableOn_det fun i j => hφd _ (hb i) j
  have hdC : DifferentiableOn ℂ (fun t => (Cm t).det) W :=
    differentiableOn_det fun i j => hφd _ (hc i) j
  have hT : ∀ t ∈ W, ∃ T : Matrix (Fin m) (Fin m) ℂ,
      (∀ i, c i t = ∑ j, T i j • b j t) ∧ Cm t = T * Bm t := by
    intro t ht
    have h1 := fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hcs t ht i)
    choose T hT using h1
    refine ⟨Matrix.of T, fun i => (hT i).symm, ?_⟩
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Cm, Bm, Matrix.of_apply, Matrix.mul_apply, ← hT i, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hB0 : Bm t₀ = 1 := by
    ext i j
    simp only [Bm, Matrix.of_apply, hφb, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  obtain ⟨T₀, hT₀, hCT₀⟩ := hT t₀ ht₀
  have hf₀ : (Cm t₀).det ≠ 0 := by
    rw [hCT₀, hB0, mul_one]
    have h1 : (fun i => c i t₀) = fun i => ∑ j, T₀ i j • b j t₀ := funext hT₀
    exact det_ne_zero_of_comb T₀ _ (h1 ▸ hci)
  let f₀ : ℂ := (Cm t₀).det
  let q : (Fin n → ℂ) → ℂ := fun t => (Cm t).det / (Bm t).det / f₀
  let V₁ : Set (Fin n → ℂ) := W ∩ (fun t => (Bm t).det) ⁻¹' {0}ᶜ
  have hV₁ : IsOpen V₁ := hdB.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hfd : DifferentiableOn ℂ (fun t => (Cm t).det / (Bm t).det) V₁ := by
    simp only [div_eq_mul_inv]
    have hinv : DifferentiableOn ℂ (fun t => ((Bm t).det)⁻¹) V₁ :=
      DifferentiableOn.fun_inv (hdB.mono Set.inter_subset_left) fun t ht => ht.2
    exact (hdC.mono Set.inter_subset_left).mul hinv
  have hqd : DifferentiableOn ℂ q V₁ := by
    have h1 := hfd.mul_const f₀⁻¹
    simpa only [q, div_eq_mul_inv] using h1
  let V : Set (Fin n → ℂ) := V₁ ∩ q ⁻¹' Metric.ball 1 1
  have hVo : IsOpen V := hqd.continuousOn.isOpen_inter_preimage hV₁ Metric.isOpen_ball
  have hq0 : q t₀ = 1 := by
    simp only [q, f₀, hB0, det_one, div_one]
    exact div_self hf₀
  have hslit : ∀ t ∈ V, q t ∈ Complex.slitPlane := by
    intro t ht
    have h1 : ‖q t - 1‖ < 1 := by simpa [dist_eq_norm] using ht.2
    have h2 := Complex.mem_slitPlane_of_norm_lt_one h1
    simpa using h2
  refine ⟨V, hVo, ⟨⟨ht₀, by simp [hB0]⟩, by simp [hq0]⟩, fun t ht => ht.1.1,
    fun t => 2 * Complex.log (q t) + 2 * ((Real.log ‖f₀‖ : ℝ) : ℂ), ?_, ?_⟩
  · exact (((hqd.mono Set.inter_subset_left).clog hslit).const_mul 2).add_const _
  · intro t ht
    obtain ⟨T, hTc, hCT⟩ := hT t ht.1.1
    have hBne : (Bm t).det ≠ 0 := ht.1.2
    have hqne : q t ≠ 0 := Complex.slitPlane_ne_zero (hslit t ht)
    have hdet : T.det = q t * f₀ := by
      have h1 : (Cm t).det = T.det * (Bm t).det := by rw [hCT, det_mul]
      have hf₀' : f₀ ≠ 0 := hf₀
      show T.det = (Cm t).det / (Bm t).det / f₀ * f₀
      rw [div_mul_cancel₀ _ hf₀', h1, mul_div_cancel_right₀ _ hBne]
    have hTne : T.det ≠ 0 := by
      rw [hdet]
      exact mul_ne_zero hqne hf₀
    have hcf : (fun i => c i t) = fun i => ∑ j, T i j • b j t := funext hTc
    refine ⟨hcf ▸ linearIndependent_comb T _ (hbi t ht.1.1) hTne, ?_⟩
    have hpos := gram_det_re_pos (R t) _ (hbi t ht.1.1)
    rw [hcf, gram_comb_det, Real.log_mul (by simpa using hTne) hpos.ne', add_comm, hdet]
    congr 1
    have hf₀n : ‖f₀‖ ≠ 0 := norm_ne_zero_iff.2 hf₀
    have hqn : ‖q t‖ ≠ 0 := norm_ne_zero_iff.2 hqne
    rw [Complex.normSq_eq_norm_sq, norm_mul, Real.log_pow, Real.log_mul (mul_ne_zero hqn hf₀n |> left_ne_zero_of_mul) hf₀n]
    simp [Complex.add_re, Complex.mul_re, Complex.log_re]
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyC2PullbackOfSection
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem isOpen_compl_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : s x x ≠ 0 := hx
  obtain ⟨j, hj⟩ := A.cover x
  have hleft : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' L.U x :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ L.U x
      rw [hleft]; exact L.mem_U x⟩
  have hg : ContinuousAt (s x ∘ (A.chart j).symm) (A.chart j x) :=
    (hs.1 x j _ hmem).continuousAt
  have hne : (s x ∘ (A.chart j).symm) (A.chart j x) ≠ 0 := by
    simpa [Function.comp_apply, hleft] using hx0
  have h1 : ∀ᶠ y in 𝓝 x, (s x ∘ (A.chart j).symm) (A.chart j y) ≠ 0 :=
    ((A.chart j).continuousAt hj).eventually (hg.eventually_ne hne)
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ (A.chart j).source := (A.chart j).open_source.mem_nhds hj
  have h3 : ∀ᶠ y in 𝓝 x, y ∈ L.U x := (L.isOpen_U x).mem_nhds (L.mem_U x)
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  have hsy : s x y ≠ 0 := by
    simpa [Function.comp_apply, (A.chart j).left_inv hy2] using hy1
  intro hb
  have hb0 : s y y = 0 := hb
  have heq := hs.2 x y y ⟨hy3, L.mem_U y⟩
  rw [hb0, norm_zero, zero_mul] at heq
  exact (mul_ne_zero (norm_ne_zero_iff.2 hsy) (Real.exp_ne_zero _)) heq

theorem regular_family_C2_pullback_of_open {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (s : X → X → ℂ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (hO : IsOpen (bdry s)ᶜ)
    (hph : A.SmoothOn (bdry s)ᶜ ph)
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), A.Smooth (phT t))
    (hC : IsRegFamilyC2 A s ph phT) :
    IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h) := by
  have key := GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.proof A' A h hh (bdry s)ᶜ hO phT ph
    (ph ∘ h) hph (fun _ _ => rfl) hT (fun k K hK hKs => hC k K hKs hK)
  intro j K hKs hK
  exact key j K hK hKs

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeQuotientCompat
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem riemLat_assemble_of_quot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R₁ : RiemLat E g' Λ') (D : AddSubgroup Λ) (π : Λ → Λ') (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (Hm' : Matrix (Fin g') (Fin g') ℂ) (B' : 𝓞 E →+* Module.End ℂ (Fin g' → ℂ)), (∀ x', ∃ x ∈ D, π x = x') → (∀ x ∈ D, ∀ y ∈ D, π (x + y) = π x + π y) → (∀ (a : 𝓞 E), ∀ x ∈ D, a • x ∈ D ∧ π (a • x) = a • π x) → (∀ x ∈ D, π x = 0 → q (R.P x) = 0) → (∀ a z, B' a (q z) = q (R.B a z)) → Hm'.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) → (∀ x ∈ D, ∀ y ∈ D, (q (R.P x) ⬝ᵥ Hm' *ᵥ star (q (R.P y))).im = R₁.form (π x) (π y)) → ∃ R' : RiemLat E g' Λ', R'.form = R₁.form ∧ R'.Hm = Hm' ∧ ∀ x ∈ D, R'.P (π x) = q (R.P x) := by
  intro E _ _ _ g g' Λ Λ' _ _ _ _ R R₁ D π q Hm' B' hsurj hadd hsmul hker hB hHm hpos hform
  choose s hsD hs using hsurj
  have hwd : ∀ x ∈ D, ∀ y ∈ D, π x = π y → q (R.P x) = q (R.P y) := by
    intro x hx y hy hxy
    have hxy' : x - y ∈ D := D.sub_mem hx hy
    have h1 := hadd (x - y) hxy' y hy
    rw [sub_add_cancel, hxy] at h1
    have h2 : π (x - y) = 0 :=
      calc π (x - y) = π (x - y) + π y - π y := (add_sub_cancel_right _ _).symm
        _ = π y - π y := by rw [← h1]
        _ = 0 := sub_self _
    have h3 := hker _ hxy' h2
    rwa [map_sub, map_sub, sub_eq_zero] at h3
  let P' : Λ' →+ (Fin g' → ℂ) := AddMonoidHom.mk' (fun x' => q (R.P (s x'))) (fun x' y' => by
    show q (R.P (s (x' + y'))) = q (R.P (s x')) + q (R.P (s y'))
    have hD : s x' + s y' ∈ D := D.add_mem (hsD x') (hsD y')
    have h := hwd _ (hsD (x' + y')) _ hD (by rw [hs, hadd _ (hsD x') _ (hsD y'), hs, hs])
    rw [h, map_add (f := _), map_add (f := _)])
  have hP' : ∀ x ∈ D, P' (π x) = q (R.P x) := fun x hx => hwd _ (hsD (π x)) _ hx (hs (π x))
  refine ⟨⟨R₁.1, R₁.2, R₁.3, R₁.form, R₁.5, R₁.6, R₁.7, P', Hm', hHm, hpos, ?_, B', ?_⟩, rfl, rfl, hP'⟩
  · intro x' y'
    have h := hform _ (hsD x') _ (hsD y')
    rw [hs, hs] at h
    exact h
  · intro a x'
    have hax : a • s x' ∈ D := (hsmul a _ (hsD x')).1
    have h1 : π (a • s x') = a • x' := by rw [(hsmul a _ (hsD x')).2, hs]
    calc P' (a • x') = P' (π (a • s x')) := by rw [h1]
      _ = q (R.P (a • s x')) := hP' _ hax
      _ = q (R.B a (R.P (s x'))) := by rw [R.14]
      _ = B' a (q (R.P (s x'))) := (hB a _).symm

end GlobalTheory.CompanionTheory.Ar.Cusp
end

