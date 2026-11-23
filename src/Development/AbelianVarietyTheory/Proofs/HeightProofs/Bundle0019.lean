module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealPar.KStabLie

variable {p q n : ℕ}

theorem Jm_eq (p q : ℕ) : Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem isKC_iff (X : Mat p q) : IsKC X ↔ X * Jm p q = Jm p q * X := by
  rw [Jm_eq]
  constructor
  · intro h
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases a with a | a <;> rcases b with b | b
    · simp
    · simp [h (.inl a) (.inr b) (by simp [sameBlock])]
    · simp [h (.inr a) (.inl b) (by simp [sameBlock])]
    · simp
  · intro h a b hab
    have := congrFun (congrFun h a) b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    rcases a with a | a <;> rcases b with b | b
    · simp [sameBlock] at hab
    · simp only [Sum.elim_inl, Sum.elim_inr] at this
      linear_combination (-1 / 2 : ℂ) * this
    · simp only [Sum.elim_inl, Sum.elim_inr] at this
      linear_combination (1 / 2 : ℂ) * this
    · simp [sameBlock] at hab

theorem Jm_sq (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases a <;> simp

theorem Jm_ct (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  rw [Jm_eq, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  cases a <;> simp

theorem mem_Kset {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) {x : T.G}
    (hx : x ∈ T.Kset) :
    Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ Formalism.REAL.Kset ε := by
  have h1 : Formalism.REAL.inUJ ε _ := h.cov_mem T x
  have h2 := (isKC_iff _).1 hx
  have h3 : Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := by
    rw [← h.reindex_Jm]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, h2]
  refine ⟨?_, h3⟩
  generalize Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g at h1 h3
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold Formalism.REAL.inUJ at h1
  rw [Matrix.mul_assoc, ← h3, ← Matrix.mul_assoc] at h1
  have h4 := congrArg (· * Formalism.REAL.Jm ε) h1
  simpa only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] using h4

theorem smul_mem_upq {X : Mat p q} (hX : X ∈ upq p q) (t : ℝ) : t • X ∈ upq p q := by
  have h : Xᴴ * Jm p q + Jm p q * X = 0 := hX
  change (t • X)ᴴ * Jm p q + Jm p q * (t • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h, smul_zero]

theorem expt_mem (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) (hK : IsKC X) (t : ℝ) :
    T.expt (t • X) ∈ T.Kset := by
  change IsKC _
  rw [T.expt_cov _ (smul_mem_upq hX t), isKC_iff]
  have h : Commute (t • X) (Jm p q) := Commute.smul_left ((isKC_iff X).1 hK) t
  exact h.exp_left.eq

theorem deriv_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H)
    [FiniteDimensional ℂ S] {f : ℝ → H} {y : H} (hf : HasDerivAt f y 0) (hS : ∀ t, f t ∈ S) : y ∈ S := by
  have hc : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  refine hc.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hf) (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact S.smul_of_tower_mem _ (S.sub_mem (hS t) (hS 0))

theorem exists_decomp {Z : Mat p q} (hZ : IsKC Z) :
    ∃ X Y : Mat p q, X ∈ upq p q ∧ IsKC X ∧ Y ∈ upq p q ∧ IsKC Y ∧ Z = X + Complex.I • Y := by
  have hc : IsKC Zᴴ := by
    intro a b hab
    rw [Matrix.conjTranspose_apply, hZ b a (by cases a <;> cases b <;> simp_all [sameBlock]), star_zero]
  have h1 := (isKC_iff _).1 hZ
  have h2 := (isKC_iff _).1 hc
  refine ⟨(1 / 2 : ℂ) • (Z - Zᴴ), (-Complex.I / 2) • (Z + Zᴴ), ?_, ?_, ?_, ?_, ?_⟩
  · change _ + _ = 0
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_add]
    simp
  · intro a b hab
    simp only [Matrix.smul_apply, Matrix.sub_apply, hZ a b hab, hc a b hab, sub_zero, smul_zero]
  · change _ + _ = 0
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    rw [show star (-Complex.I / 2) = Complex.I / 2 by simp]
    module
  · intro a b hab
    simp only [Matrix.smul_apply, Matrix.add_apply, hZ a b hab, hc a b hab, add_zero, smul_zero]
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
    module

theorem kstable_lie : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → (∀ S : Submodule ℂ R.U.H, FiniteDimensional ℂ S → IsKStableOn ε σ S → S ≤ LinearMap.range R.ι) ∧ ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → IsKStableOn ε σ (W.map R.ι) → KStable R.HK.act W := by
  intro p q n e ε T R σ h hσ
  refine ⟨fun S hS hK v hv => ?_, fun W hW hK => ?_⟩
  · have : KFin T R.U.π v := by
      unfold KFin
      refine Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      change R.U.π k v ∈ S
      rw [hσ]
      exact hK _ (mem_Kset h T k.2) v hv
    exact (R.ι_range v).2 this
  · have key : ∀ X ∈ upq p q, IsKC X → ∀ w ∈ W, R.HK.act X w ∈ W := by
      intro X hX hXK w hw
      have : R.ι (R.HK.act X w) ∈ W.map R.ι := by
        refine deriv_mem _ (R.der X hX w) fun t => ?_
        rw [hσ]
        exact hK _ (mem_Kset h T (expt_mem T hX hXK t)) _ (Submodule.mem_map_of_mem hw)
      obtain ⟨u, hu, hu'⟩ := this
      rw [← R.ι_inj hu']
      exact hu
    intro Z hZ w hw
    obtain ⟨X, Y, hX, hXK, hY, hYK, rfl⟩ := exists_decomp hZ
    rw [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact W.add_mem (key X hX hXK w hw) (W.smul_mem _ (key Y hY hYK w hw))

end GlobalTheory.RealPar.KStabLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
section
open Formalism.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompactDualUnique

theorem isOmegaLeb_unique {P Q : ℕ} {lam lam' : Measure (lieU P Q)}
    (h : IsOmegaLeb lam) (h' : IsOmegaLeb lam') : lam = lam' := by
  haveI : BorelSpace (lieU P Q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  haveI : LocallyCompactSpace (lieU P Q) :=
    (Submodule.closed_of_finiteDimensional (lieU P Q)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (lieU P Q) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, lam = t • lam' := ⟨_, Measure.isAddLeftInvariant_eq_smul lam lam'⟩
  have hp : lam.prod lam = (t * t) • lam'.prod lam' := by
    rw [ht, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hf : AEMeasurable (fun ab : lieU P Q × lieU P Q =>
      entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))
      (lam'.prod lam') := by
    apply Continuous.aemeasurable
    apply continuous_pi fun ij => ?_
    simp only [entries, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have hc : Continuous (fun x : lieU P Q =>
        (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
      (continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_subtype_val)
    exact (hc.comp continuous_fst).add (continuous_const.mul (hc.comp continuous_snd))
  rw [hp, Measure.map_smul _ hf, h2'] at h2
  have h3 := congrArg (fun m : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) =>
    m (Metric.ball 0 1)) h2
  simp only [Measure.smul_apply] at h3
  have hpos : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hfin : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have h4 : ((t * t : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.smul_def, smul_eq_mul] at h3
    exact (ENNReal.mul_left_inj hpos hfin).1 (h3.trans (one_mul _).symm)
  have h5 : t * t = 1 := by exact_mod_cast h4
  have h6 : t = 1 := by
    have h7 : (t : ℝ) * t = 1 := by exact_mod_cast h5
    have h8 : (0 : ℝ) ≤ t := t.2
    have : (t : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [ht, h6, one_smul]

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ℝ≥0∞}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, h1, h2⟩ := h
  obtain ⟨lam', h1', h2'⟩ := h'
  obtain rfl := isOmegaLeb_unique h1 h1'
  exact tendsto_nhds_unique h2 h2'

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ℝ≥0∞} (t : ℝ≥0)
    (h : OmegaDensity μ c) : OmegaDensity (t • μ) (t * c) := by
  obtain ⟨lam, h1, h2⟩ := h
  refine ⟨lam, h1, ?_⟩
  have := ENNReal.Tendsto.const_mul (a := (t : ℝ≥0∞)) h2 (Or.inr ENNReal.coe_ne_top)
  refine this.congr fun r => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]

theorem exists_eq_smul {P Q : ℕ} (μ ν : Measure (UpqT P Q)) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    ∃ t : ℝ≥0, μ = t • ν := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul μ ν⟩

theorem eq_cd (cd : CDHaar) (P Q : ℕ) (ν : Measure (UpqT P Q)) (νc : Measure (UpqT (P + Q) 0))
    (c : ENNReal) (hν : ν.IsHaarMeasure) (hνc : νc.IsHaarMeasure) (hp : IsProbabilityMeasure νc)
    (_h0 : c ≠ 0) (_ht : c ≠ ⊤) (h1 : OmegaDensity ν c) (h2 : OmegaDensity νc c) :
    ν = cd.cd P Q := by
  haveI := cd.haar P Q
  haveI := cd.haar (P + Q) 0
  haveI := cd.prob (P + Q)
  obtain ⟨c', h0', ht', h1', h2'⟩ := cd.trick P Q
  obtain ⟨s, hs⟩ := exists_eq_smul νc (cd.cd (P + Q) 0)
  have hs1 : s = 1 := by
    have := congrArg (fun m : Measure (UpqT (P + Q) 0) => m Set.univ) hs
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this.symm
  rw [hs1, one_smul] at hs
  rw [hs] at h2
  obtain rfl := omegaDensity_unique h2 h2'
  obtain ⟨t, ht⟩ := exists_eq_smul ν (cd.cd P Q)
  have h3 := omegaDensity_smul t h1'
  rw [← ht] at h3
  have h4 := omegaDensity_unique h3 h1
  have h5 : (t : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj h0' ht').1 (h4.trans (one_mul _).symm)
  have h6 : t = 1 := by exact_mod_cast h5
  rw [ht, h6, one_smul]

end GlobalTheory.CompactDualUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HighestWeightGeneratedWeightsBelow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.HwGen

theorem weight_of_mem_span {V ι κ : Type*} [AddCommGroup V] [Module ℂ V] (H : ι → Module.End ℂ V)
    (m : κ → V) (χ : κ → ι → ℂ) (hm : ∀ k a, H a (m k) = χ k a • m k) (ν : ι → ℂ) (w : V)
    (hw : w ∈ Submodule.span ℂ (Set.range m)) (h0 : w ≠ 0) (hν : ∀ a, H a w = ν a • w) :
    ∃ k, χ k = ν := by
  by_contra hne
  push Not at hne
  let M : Submonoid (Module.End ℂ V) :=
    Submonoid.closure {P | ∃ a c, c ≠ ν a ∧ P = H a - c • (1 : Module.End ℂ V)}
  have hM : ∀ P ∈ M, ∀ (s : V) (η : ι → ℂ), (∀ a, H a s = η a • s) →
      ∃ c : ℂ, P s = c • s ∧ (η = ν → c ≠ 0) := by
    intro P hP s η hs
    induction hP using Submonoid.closure_induction with
    | mem P hP =>
      obtain ⟨a, c, hc, rfl⟩ := hP
      refine ⟨η a - c, by simp [hs, sub_smul], ?_⟩
      rintro rfl
      exact sub_ne_zero.2 hc.symm
    | one => exact ⟨1, by simp, fun _ => one_ne_zero⟩
    | mul P Q _ _ hP hQ =>
      obtain ⟨c, hc, hc'⟩ := hP
      obtain ⟨d, hd, hd'⟩ := hQ
      exact ⟨d * c, by simp [hc, hd, mul_smul], fun h => mul_ne_zero (hd' h) (hc' h)⟩
  have key : ∀ x ∈ Submodule.span ℂ (Set.range m), ∀ Q ∈ M, ∃ P ∈ M, P (Q x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      intro Q hQ
      obtain ⟨c, hc, -⟩ := hM Q hQ (m k) (χ k) (hm k)
      obtain ⟨a, ha⟩ := Function.ne_iff.1 (hne k)
      refine ⟨H a - χ k a • 1, Submonoid.subset_closure ⟨a, _, ha, rfl⟩, ?_⟩
      rw [hc, map_smul]
      simp [hm]
    | zero => exact fun Q _ => ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro Q hQ
      obtain ⟨P, hP, h1⟩ := hx Q hQ
      obtain ⟨R, hR, h2⟩ := hy (P * Q) (mul_mem hP hQ)
      refine ⟨R * P, mul_mem hR hP, ?_⟩
      simp only [Module.End.mul_apply] at h2 ⊢
      simp [h1, h2]
    | smul c x _ hx =>
      intro Q hQ
      obtain ⟨P, hP, h1⟩ := hx Q hQ
      exact ⟨P, hP, by simp [h1]⟩
  obtain ⟨P, hP, h1⟩ := key w hw 1 (one_mem _)
  obtain ⟨c, hc, hc'⟩ := hM P hP w ν hν
  rw [Module.End.one_apply, hc] at h1
  exact h0 ((smul_eq_zero.1 h1).resolve_left (hc' rfl))

variable {p q : ℕ}

theorem isKC_Eab {a b : Ix p q} (h : posC a b) : IsKC (Eab b a) := by
  intro x y hxy
  by_contra hne
  have : b = x ∧ a = y := by
    by_contra hh
    exact hne (by simp [Eab, hh])
  obtain ⟨rfl, rfl⟩ := this
  cases a <;> cases b <;> simp_all [posC, sameBlock]

theorem isKC_mul {X Y : Mat p q} (hX : IsKC X) (hY : IsKC Y) : IsKC (X * Y) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : sameBlock a c
  · rw [hY c b (by cases a <;> cases b <;> cases c <;> simp_all [sameBlock]), mul_zero]
  · rw [hX a c h, zero_mul]

theorem isKC_sub {X Y : Mat p q} (hX : IsKC X) (hY : IsKC Y) : IsKC (X - Y) := by
  intro a b hab
  simp [hX a b hab, hY a b hab]

theorem sameBlock_cases {a b : Ix p q} (h : sameBlock a b) : a = b ∨ posC a b ∨ posC b a := by
  rcases a with a | a <;> rcases b with b | b
  · rcases lt_trichotomy a b with x | x | x
    · exact .inr (.inl x)
    · exact .inl (by rw [x])
    · exact .inr (.inr x)
  · exact h.elim
  · exact h.elim
  · rcases lt_trichotomy a b with x | x | x
    · exact .inr (.inl x)
    · exact .inl (by rw [x])
    · exact .inr (.inr x)

theorem bracket_diag (x a b : Ix p q) :
    Eab x x * Eab b a - Eab b a * Eab x x =
      (((if x = b then 1 else 0) - (if x = a then 1 else 0) : ℂ)) • Eab b a := by
  have h1 : Eab x x * Eab b a = ((if x = b then 1 else 0) : ℂ) • Eab b a := by
    by_cases h : x = b
    · subst h; simp [Eab]
    · simp [Eab, h]
  have h2 : Eab b a * Eab x x = ((if x = a then 1 else 0) : ℂ) • Eab b a := by
    by_cases h : x = a
    · subst h; simp [Eab]
    · simp [Eab, h, Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h)]
  rw [h1, h2, sub_smul]

abbrev PosRoot (p q : ℕ) := {r : Ix p q × Ix p q // posC r.1 r.2}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

noncomputable def mono (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (v : V) : List (PosRoot p q) → V
  | [] => v
  | r :: l => act (Eab r.1.2 r.1.1) (mono act v l)

noncomputable def cnt : List (PosRoot p q) → Ix p q → Ix p q → ℕ
  | [], _, _ => 0
  | r :: l, a, b => cnt l a b + if a = r.1.1 ∧ b = r.1.2 then 1 else 0

theorem posC_of_cnt (l : List (PosRoot p q)) (a b : Ix p q) (h : cnt l a b ≠ 0) : posC a b := by
  induction l with
  | nil => exact (h rfl).elim
  | cons r l ih =>
    by_cases hh : a = r.1.1 ∧ b = r.1.2
    · rw [hh.1, hh.2]; exact r.2
    · exact ih (by simpa [cnt, hh] using h)

noncomputable def drop (l : List (PosRoot p q)) (x : Ix p q) : ℝ :=
  ∑ a, ∑ b, (cnt l a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))

theorem drop_cons (r : PosRoot p q) (l : List (PosRoot p q)) (x : Ix p q) :
    drop (r :: l) x = drop l x + ((if x = r.1.1 then 1 else 0) - (if x = r.1.2 then 1 else 0)) := by
  simp only [drop, cnt, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single r.1.1, Finset.sum_eq_single r.1.2]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro a _ ha; simp [ha]
  · simp

theorem act_comm {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (X Y : Mat p q) (u : V) :
    act X (act Y u) = act Y (act X u) + act (X * Y - Y * X) u := by
  rw [h X Y]; simp

theorem mono_weight {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) (l : List (PosRoot p q)) (x : Ix p q) :
    act (Eab x x) (mono act v l) = ((((μ x : ℚ) : ℝ) - drop l x : ℝ) : ℂ) • mono act v l := by
  induction l with
  | nil => simp [mono, drop, cnt, hv]
  | cons r l ih =>
    rw [mono, act_comm h, ih, bracket_diag, map_smul, map_smul, LinearMap.smul_apply, ← add_smul, drop_cons]
    congr 1
    push_cast
    split_ifs <;> simp <;> ring

theorem mono_stable {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) (hr : ∀ a b, posC a b → act (Eab a b) v = 0) :
    KStable act (Submodule.span ℂ (Set.range (mono act v))) := by
  set W := Submodule.span ℂ (Set.range (mono act v)) with hW
  have hm : ∀ l, mono act v l ∈ W := fun l => Submodule.subset_span ⟨l, rfl⟩
  have ext : ∀ T : Module.End ℂ V, (∀ l, T (mono act v l) ∈ W) → ∀ w ∈ W, T w ∈ W := by
    intro T hT w hw
    have : W ≤ W.comap T := Submodule.span_le.2 (by rintro _ ⟨l, rfl⟩; exact hT l)
    exact this hw
  have low : ∀ r : PosRoot p q, ∀ w ∈ W, act (Eab r.1.2 r.1.1) w ∈ W :=
    fun r => ext _ fun l => hm (r :: l)
  have key : ∀ l, ∀ Z, IsKC Z → act Z (mono act v l) ∈ W := by
    intro l
    induction l with
    | nil =>
      intro Z hZ
      have hZ' : Z = ∑ a, ∑ b, Z a b • Eab a b := by
        conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
        simp [Eab]
      rw [hZ']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine W.sum_mem fun a _ => W.sum_mem fun b _ => ?_
      by_cases hab : sameBlock a b
      · refine W.smul_mem _ ?_
        rcases sameBlock_cases hab with x | x | x
        · subst x
          rw [mono, hv]; exact W.smul_mem _ (hm [])
        · rw [mono, hr a b x]; exact W.zero_mem
        · exact hm [⟨(b, a), x⟩]
      · rw [hZ a b hab, zero_smul]; exact W.zero_mem
    | cons r l ih =>
      intro Z hZ
      rw [mono, act_comm h]
      have hF := isKC_Eab r.2
      exact W.add_mem (low r _ (ih Z hZ)) (ih _ (isKC_sub (isKC_mul hZ hF) (isKC_mul hF hZ)))
  exact fun Z hZ => ext _ fun l => key l Z hZ

theorem hw_generated : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (μ : Ix p q → ℚ) (v : V), Formalism.BasicNotions.TH.IsHW act μ v → ∃ W : Submodule ℂ V, v ∈ W ∧ KStable act W ∧ (∀ W' : Submodule ℂ V, v ∈ W' → KStable act W' → W ≤ W') ∧ ∀ (ν : Ix p q → ℝ) (w : V), w ∈ W → w ≠ 0 → (∀ a, act (Eab a a) w = ((ν a : ℝ) : ℂ) • w) → ∃ c : Ix p q → Ix p q → ℕ, (∀ a b, c a b ≠ 0 → posC a b) ∧ ∀ x, ((μ x : ℚ) : ℝ) - ν x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) := by
  intro p q V _ _ act h μ v hv
  obtain ⟨-, hw, hr⟩ := hv
  have hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
    intro a
    have := (Submodule.mem_iInf _).1 hw a
    simpa [sub_eq_zero] using this
  have hr : ∀ a b, posC a b → act (Eab a b) v = 0 := by
    intro a b hab
    have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hr a) b) hab
    simpa using this
  refine ⟨Submodule.span ℂ (Set.range (mono act v)), Submodule.subset_span ⟨[], rfl⟩, mono_stable h hv hr, ?_, ?_⟩
  · intro W' hvW hW
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, rfl⟩
    induction l with
    | nil => exact hvW
    | cons r l ih => exact hW _ (isKC_Eab r.2) _ ih
  · intro ν w hw h0 hν
    obtain ⟨l, hl⟩ := weight_of_mem_span (fun a => act (Eab a a)) (mono act v) _
      (fun l x => mono_weight h hv l x) (fun a => ((ν a : ℝ) : ℂ)) w hw h0 hν
    refine ⟨cnt l, posC_of_cnt l, fun x => ?_⟩
    have := Complex.ofReal_injective (congrFun hl x)
    change _ = drop l x
    linarith

end GlobalTheory.RealPar.HwGen
end

