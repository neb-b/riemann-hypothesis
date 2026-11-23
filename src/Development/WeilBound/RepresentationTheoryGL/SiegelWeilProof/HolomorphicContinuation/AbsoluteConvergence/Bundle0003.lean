module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem projected_block_lower_sum (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, fromBlocks_multiply]
  simp

theorem lowerDiagonalBlockAsGL (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, fromBlocks_multiply]
  simp

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := by
  simp [mR]

theorem k_blocks {k : GR n} (hk : k ∈ KR n) :
    (mR k).toBlocks₂₁ = -(mR k).toBlocks₁₂ ∧ (mR k).toBlocks₂₂ = (mR k).toBlocks₁₁ := by
  have hK : InK (mR k) := hk
  have h2 : mR k * (mR k)ᴴ = 1 := mul_eq_one_comm.1 hK.2
  have h3 : JJ n * mR k = mR k * JJ n := by
    calc JJ n * mR k = (mR k * (mR k)ᴴ) * (JJ n * mR k) := by rw [h2, Matrix.one_mul]
      _ = mR k * ((mR k)ᴴ * JJ n * mR k) := by simp only [Matrix.mul_assoc]
      _ = mR k * JJ n := by rw [hK.1]
  rw [← fromBlocks_toBlocks (mR k)] at h3
  unfold JJ at h3
  rw [fromBlocks_multiply, fromBlocks_multiply] at h3
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, fromBlocks_inj] at h3
  obtain ⟨h11, h12, _, _⟩ := h3
  exact ⟨h11, h12⟩

theorem first_block_mul_compact (g : M2 n) {k : GR n} (hk : k ∈ KR n) : u1 (g * mR k) = u1 g * u1 (mR k) := by
  obtain ⟨hC, hD⟩ := k_blocks hk
  simp only [u1, projected_block_lower_sum, lowerDiagonalBlockAsGL, hC, hD]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I,
    Matrix.mul_neg, smul_add, smul_neg, neg_smul, one_smul]
  abel

theorem second_block_mul_compact (g : M2 n) {k : GR n} (hk : k ∈ KR n) : u2 (g * mR k) = u2 g * u2 (mR k) := by
  obtain ⟨h21, h22⟩ := k_blocks hk
  unfold u2
  rw [projected_block_lower_sum, lowerDiagonalBlockAsGL, h21, h22]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
    smul_neg, neg_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul, smul_add]
  abel

theorem first_block_compact_unitary {k : GR n} (hk : k ∈ KR n) : (u1 (mR k))ᴴ * u1 (mR k) = 1 := by
  obtain ⟨h21, h22⟩ := k_blocks hk
  have hK : InK (mR k) := hk
  have e := hK.2
  rw [← fromBlocks_toBlocks (mR k), h21, h22, fromBlocks_conjTranspose, fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_inj] at e
  obtain ⟨e11, e12, _, _⟩ := e
  unfold u1
  rw [h21, h22]
  simp only [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] at e11 e12
  simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_neg, Complex.star_def, Complex.conj_I,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul,
    smul_neg, neg_neg, smul_smul, neg_mul, Complex.I_mul_I, neg_smul, one_smul, neg_neg]
  rw [(add_neg_eq_zero.1 e12).symm, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, ← e11]
  abel

theorem norm_det_first_block_compact {k : GR n} (hk : k ∈ KR n) : ‖(u1 (mR k)).det‖ = 1 := by
  have h := congrArg Matrix.det (first_block_compact_unitary hk)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  have h2 : Complex.normSq (u1 (mR k)).det = 1 := by
    have : ((Complex.normSq (u1 (mR k)).det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      simpa [Complex.star_def] using h
    exact_mod_cast this
  have h3 : ‖(u1 (mR k)).det‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h2
  have h4 : 0 ≤ ‖(u1 (mR k)).det‖ := norm_nonneg _
  nlinarith [h3, h4]

theorem first_block_upper_mul (y : GR n) (g : M2 n) (hy : IsUp y) : u1 (mR y * g) = (mR y).toBlocks₂₂ * u1 g := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u1
  rw [projected_block_lower_sum, lowerDiagonalBlockAsGL, hy']
  simp [Matrix.mul_add, Matrix.mul_smul]

theorem second_block_upper_mul (y : GR n) (g : M2 n) (hy : IsUp y) : u2 (mR y * g) = (mR y).toBlocks₂₂ * u2 g := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u2
  rw [projected_block_lower_sum, lowerDiagonalBlockAsGL, hy']
  simp [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

theorem first_block_of_upper (y : GR n) (hy : IsUp y) : u1 (mR y) = (mR y).toBlocks₂₂ := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u1
  rw [hy']
  simp

theorem second_block_of_upper (y : GR n) (hy : IsUp y) : u2 (mR y) = (mR y).toBlocks₂₂ := by
  have hy' : (mR y).toBlocks₂₁ = 0 := hy
  unfold u2
  rw [hy']
  simp

theorem mult : Mult := by
  intro n p q e
  constructor
  · intro g k hk
    constructor
    · unfold F0 f0
      rw [mR_mul, first_block_mul_compact _ hk, second_block_mul_compact _ hk, det_mul, det_mul, det_mul, mul_zpow, mul_zpow, mul_zpow]
      ring
    · unfold hLoc
      rw [mR_mul, first_block_mul_compact _ hk, det_mul, norm_mul, norm_det_first_block_compact hk, mul_one]
  · intro y g hy
    constructor
    · unfold F0 f0
      rw [mR_mul, first_block_upper_mul y _ hy, second_block_upper_mul y _ hy, first_block_of_upper y hy, second_block_of_upper y hy, det_mul, det_mul, det_mul,
        mul_zpow, mul_zpow, mul_zpow]
      ring
    · unfold hLoc
      rw [mR_mul, first_block_upper_mul y _ hy, first_block_of_upper y hy, det_mul, norm_mul, mul_pow, mul_inv]

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjOp
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def ProjOp : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ → ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)],
    ∀ W : Submodule ℂ (PX m n), FiniteDimensional ℂ W → (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) →
      ∃ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν ∧ Continuous κ ∧
        (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) ∧
        ∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y

def TSGen : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)) (Λ : Set ((G → ℂ) → ℂ)), GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ →
      ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (W : Submodule ℂ (PX m n)), FiniteDimensional ℂ W →
        (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) → ∀ (ν : Measure (KR n)) (κ : KR n → ℂ), IsFiniteMeasure ν →
        Continuous κ → (∀ Q ∈ W, ∀ y : GR n, ∫ k, κ k * sL Q (y * (k : GR n)) ∂ν = sL Q y) →
        (∀ (w : ℂ) (f : GR n → ℂ), Continuous f →
          (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → f (y * g) = (hLoc y : ℂ) ^ w * F0 p q e y * f g) →
          ∃ Q ∈ W, ∀ y : GR n, ∫ k, κ k * f (y * (k : GR n)) ∂ν = (hLoc y : ℂ) ^ w * sL Q y) →
        ∀ (g : G) (y : GR n) (Q : PX m n), Q ∈ W → (∀ y', ∫ k, κ k * F0 p q e (y' * (k : GR n) * y) ∂ν = sL Q y') →
          ∫ k, κ k * I 1 (g * ι ((k : GR n) * y)) ∂ν = I Q g

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RightConn
section
noncomputable section

open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open GlobalTheory.Cont

theorem rightConn : RightConn := by
  intro U _ hU
  obtain ⟨⟨σ, hσ⟩, hR⟩ := hU
  refine isPreconnected_of_forall (((σ + 1 : ℝ)) : ℂ) fun y hy => ?_
  have hx : (((σ + 1 : ℝ)) : ℂ) ∈ rightOf σ := by
    show σ < (((σ + 1 : ℝ)) : ℂ).re
    simp
  set T : ℝ := |y.re| + |σ| + 1 with hTdef
  have hT : (y + (T : ℂ)) ∈ rightOf σ := by
    show σ < (y + (T : ℂ)).re
    simp only [Complex.add_re, Complex.ofReal_re, hTdef]
    linarith [neg_abs_le y.re, le_abs_self σ]
  have hconv : Convex ℝ (rightOf σ) := convex_halfSpace_re_gt σ
  refine ⟨segment ℝ y (y + (T : ℂ)) ∪ segment ℝ (y + (T : ℂ)) (((σ + 1 : ℝ)) : ℂ), ?_, ?_, ?_, ?_⟩
  · refine Set.union_subset ?_ ((hconv.segment_subset hT hx).trans hσ)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have heq : a • y + b • (y + (T : ℂ)) = y + ((b * T : ℝ) : ℂ) := by
      simp only [Complex.real_smul]
      push_cast
      linear_combination y * hab'
    rw [heq]
    exact hR y hy _ (mul_nonneg hb (by positivity))
  · exact Or.inr (right_mem_segment _ _ _)
  · exact Or.inl (left_mem_segment _ _ _)
  · exact IsPreconnected.union (y + (T : ℂ)) (right_mem_segment _ _ _) (left_mem_segment _ _ _)
      (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected

theorem glue : Glue := by
  intro U f h σ s₀ hUo hU hs₀ hfm hfa hσU hhd hfh
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, ∀ w, H w = if σ + 1 < w.re then h w else f w := ⟨_, fun _ => rfl⟩
  have hHf : ∀ z, H =ᶠ[𝓝[≠] z] f := by
    intro z
    by_cases hz : σ < z.re
    · filter_upwards [hfh z hz] with w hw
      rw [hH]
      split_ifs
      · exact hw.symm
      · rfl
    · have hlt : z.re < σ + 1 := by linarith [not_lt.1 hz]
      have hn : {w : ℂ | w.re < σ + 1} ∈ 𝓝 z :=
        Complex.continuous_re.continuousAt.preimage_mem_nhds (Iio_mem_nhds hlt)
      filter_upwards [nhdsWithin_le_nhds hn] with w hw
      rw [hH, if_neg (not_lt.2 (le_of_lt hw))]
  have hmer : IsMerExt h U H := by
    refine ⟨hU, fun z hz => (hfm z hz).congr (hHf z).symm, σ + 1, fun z hz => ?_⟩
    rw [hH, if_pos (show σ + 1 < z.re from hz)]
  have hext : IsExtAt h s₀ (Function.update H s₀ (f s₀)) := (hmer.isExtAt hs₀).update _
  refine ⟨_, hext, ?_, by simp⟩
  apply hfa.congr
  have h2 := eventually_nhdsWithin_iff.1 (hHf s₀)
  filter_upwards [h2] with w hw
  by_cases hw0 : w = s₀
  · subst hw0
    simp
  · rw [Function.update_of_ne hw0]
    exact (hw hw0).symm

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZeroA
section
noncomputable section

open Matrix Filter Topology Set
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

lemma JJ_mul_JJ (n : ℕ) : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]
  congr 1 <;> simp

lemma det_JJ_ne (n : ℕ) : (JJ n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (JJ_mul_JJ n)
  rw [det_mul, h, zero_mul, det_neg, det_one] at this
  simp at this

lemma exists_of_InG {M : M2 n} (h : InG M) : ∃ g : GR n, mR g = M := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have hdet : M.det ≠ 0 := by
    intro h0
    have hd := congrArg det h'
    rw [det_mul, det_mul, h0, mul_zero] at hd
    exact det_JJ_ne n hd.symm
  exact ⟨⟨GeneralLinearGroup.mkOfDetNeZero M hdet, h⟩, rfl⟩

lemma InG_JJ_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (JJ n * nU b) := by
  show (JJ n * nU b)ᴴ * JJ n * (JJ n * nU b) = JJ n
  simp [JJ, nU, fromBlocks_multiply, fromBlocks_conjTranspose, hb.eq]

lemma InG_lower (s : ℝ) : InG (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1) := by
  show (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1)ᴴ * JJ n *
    fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1 = JJ n
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose]

lemma yJyH {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h' : Mᴴ * JJ n * M = JJ n := h
  have hJ := JJ_mul_JJ n
  have h1 : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by
    have e : (-(JJ n * Mᴴ * JJ n)) * M = -(JJ n * (Mᴴ * JJ n * M)) := by
      simp [Matrix.mul_assoc]
    rw [e, h', hJ, neg_neg]
  have h2 := mul_eq_one_comm.mpr h1
  calc M * JJ n * Mᴴ = (M * (-(JJ n * Mᴴ * JJ n))) * JJ n := by
        simp [Matrix.mul_assoc, hJ]
    _ = JJ n := by rw [h2, Matrix.one_mul]

lemma lowerDiagonalBlockAsGL {M : M2 n} (h : InG M) : M.toBlocks₂₁ * M.toBlocks₂₂ᴴ = M.toBlocks₂₂ * M.toBlocks₂₁ᴴ := by
  have h2 := congrArg toBlocks₂₂ (yJyH h)
  rw [← fromBlocks_toBlocks M] at h2
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at h2
  exact (neg_add_eq_zero.mp h2).symm

end PositivityTheory.Rg.Sw.AbsSt.SZ
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SphericalCharacterInvMul
section
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem first_cayley_block_one (n : ℕ) : u1 (1 : M2 n) = 1 := by
  have h21 : toBlocks₂₁ (1 : M2 n) = 0 := by
    ext i j
    simp [toBlocks₂₁, Matrix.one_apply]
  have h22 : toBlocks₂₂ (1 : M2 n) = 1 := by
    ext i j
    simp [toBlocks₂₂, Matrix.one_apply]
  simp [u1, h21, h22]

theorem second_cayley_block_one (n : ℕ) : u2 (1 : M2 n) = 1 := by
  have h21 : toBlocks₂₁ (1 : M2 n) = 0 := by
    ext i j
    simp [toBlocks₂₁, Matrix.one_apply]
  have h22 : toBlocks₂₂ (1 : M2 n) = 1 := by
    ext i j
    simp [toBlocks₂₂, Matrix.one_apply]
  simp [u2, h21, h22]

theorem weight_factor_one (n p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  show det (1 : M2 n) ^ e * f0 p q (1 : M2 n) = 1
  simp [f0, first_cayley_block_one, second_cayley_block_one]

theorem spherical_character_inv_mul (hM : Mult) (n p q : ℕ) (e : ℤ) (k : GR n) (hk : k ∈ KR n) :
    F0 p q e k⁻¹ * F0 p q e k = 1 := by
  rw [← ((hM n p q e).1 k⁻¹ k hk).1, inv_mul_cancel, weight_factor_one]

theorem sph (hI : Iwa) (hM : Mult) : Sph := by
  intro n p q e _ _ μ _ _ y z
  obtain ⟨b, k0, hb, hk0, rfl⟩ := hI n y
  have hmul := (hM n p q e).1
  have hup := (hM n p q e).2
  have step1 : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e (b * k0 * (k : GR n) * z)
      = F0 p q e b * ((F0 p q e (k : GR n))⁻¹ * F0 p q e (k0 * (k : GR n) * z)) := by
    intro k
    rw [show b * k0 * (k : GR n) * z = b * (k0 * (k : GR n) * z) by simp only [mul_assoc],
      (hup b _ hb).1]
    ring
  simp_rw [step1]
  rw [integral_const_mul, (hmul b k0 hk0).1, mul_assoc]
  congr 1
  let k0' : KR n := ⟨k0, hk0⟩
  let f : KR n → ℂ := fun k' => (F0 p q e (k0⁻¹ * (k' : GR n)))⁻¹ * F0 p q e ((k' : GR n) * z)
  have h1 : ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e (k0 * (k : GR n) * z) ∂μ
      = ∫ k : KR n, f (k0' * k) ∂μ := by
    congr 1
    ext k
    show _ = (F0 p q e (k0⁻¹ * (k0 * (k : GR n))))⁻¹ * F0 p q e (k0 * (k : GR n) * z)
    rw [inv_mul_cancel_left]
  rw [h1, integral_mul_left_eq_self f k0']
  have h2 : ∀ k' : KR n, f k' = F0 p q e k0 * ((F0 p q e (k' : GR n))⁻¹ * F0 p q e ((k' : GR n) * z)) := by
    intro k'
    simp only [f]
    rw [(hmul k0⁻¹ k' k'.2).1, mul_inv,
      inv_eq_of_mul_eq_one_right (spherical_character_inv_mul hM n p q e k0 hk0)]
    ring
  simp_rw [h2]
  rw [integral_const_mul]

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphSt
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Ac (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  fromBlocks (diagonal fun j => Complex.exp (z * X j)) 0 0 (diagonal fun j => Complex.exp (-(z * X j)))

def holomorphicSectionExtension (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (h : GR n) (z : ℂ) : ℂ :=
  (mR h).det ^ e * (u1 (mR h * Ac X z)).det ^ (-(p : ℤ)) * (u2 (mR h * Ac X z)).det ^ (-(q : ℤ))

def HelpA : Prop :=
  (∀ (n : ℕ) (X : Fin n → ℝ), ∃ a : ℝ → GR n, ∀ s, IsDil X s (a s)) ∧
  (∀ (n : ℕ) (X : Fin n → ℝ) (s : ℝ) (a a' : GR n), IsDil X s a → IsDil X s a' → a = a') ∧
  (∀ n : ℕ, IsCompact (univ : Set (KR n))) ∧
  (∀ (n : ℕ) (h : GR n), (u1 (mR h)).det ≠ 0 ∧ (u2 (mR h)).det ≠ 0) ∧
  (∀ (n p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) → ∀ (h : GR n) (s : ℝ),
    holomorphicSectionExtension p q e X h s = F0 p q e (h * a s)) ∧
  (∀ (n p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (S : Set (GR n)), IsCompact S → ∃ V : Set ℂ, IsOpen V ∧ (∀ s : ℝ, (s : ℂ) ∈ V) ∧
    ContinuousOn (fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) (S ×ˢ V) ∧ ∀ h ∈ S, DifferentiableOn ℂ (holomorphicSectionExtension p q e X h) V) ∧
  (∀ (n p q : ℕ) (e : ℤ), Continuous (F0 (n := n) p q e) ∧ ∀ k : GR n, k ∈ KR n → F0 p q e k ≠ 0)

def HelpC : Prop :=
  (∀ (f : ℂ → ℂ) (V : Set ℂ), IsOpen V → (∀ s : ℝ, (s : ℂ) ∈ V) → DifferentiableOn ℂ f V →
    ∀ (r : ℕ) (s : ℝ), iteratedDeriv r (fun t : ℝ => f t) s = iteratedDeriv r f s) ∧
  (∀ (f : ℂ → ℂ) (V : Set ℂ), IsOpen V → (∀ s : ℝ, (s : ℂ) ∈ V) → DifferentiableOn ℂ f V →
    (∀ r : ℕ, iteratedDeriv r f 0 = 0) → ∀ s : ℝ, f s = 0)

end PositivityTheory.Rg.Sw.AbsSt
end
end

