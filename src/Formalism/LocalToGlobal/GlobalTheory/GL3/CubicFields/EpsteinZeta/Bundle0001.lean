module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Homothety
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem mem_smul_iff' (Λ : AddSubgroup ℂ) (c : ℂ) (w : ℂ) :
    w ∈ c • Λ ↔ ∃ x ∈ Λ, c * x = w := by
  rw [AddSubgroup.mem_smul_pointwise_iff_exists]
  simp only [smul_eq_mul]

def smulEquivNZ (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) :
    {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ c • Λ ∧ w ≠ 0} where
  toFun w := ⟨c * w.1, (mem_smul_iff' Λ c _).2 ⟨w.1, w.2.1, rfl⟩, mul_ne_zero hc w.2.2⟩
  invFun w := ⟨c⁻¹ * w.1, by
    obtain ⟨x, hx, hxw⟩ := (mem_smul_iff' Λ c _).1 w.2.1
    refine ⟨?_, mul_ne_zero (inv_ne_zero hc) w.2.2⟩
    rw [← hxw, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]; exact hx⟩
  left_inv w := by ext; simp [hc]
  right_inv w := by ext; simp [hc]

theorem eisG_smul (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) (k : ℕ) :
    eisG (c • Λ) k = (c ^ (2 * k))⁻¹ * eisG Λ k := by
  unfold eisG
  rw [show (∑' w : {w : ℂ // w ∈ c • Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)) =
      ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / ((smulEquivNZ Λ c hc w : ℂ)) ^ (2 * k) from
      ((smulEquivNZ Λ c hc).tsum_eq (fun w => 1 / (w : ℂ) ^ (2 * k))).symm]
  rw [← tsum_mul_left]
  congr 1
  funext w
  show 1 / (c * w.1) ^ (2 * k) = (c ^ (2 * k))⁻¹ * (1 / w.1 ^ (2 * k))
  rw [one_div, one_div, mul_pow, mul_inv]

theorem discr_smul (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) :
    discr (c • Λ) = (c ^ 12)⁻¹ * discr Λ := by
  first
  | (unfold discr; simp only [g2, g3, eisG_smul Λ c hc]; ring)
  | (unfold discr g2 g3; done)

theorem latI_eq_smul {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K))
    (δ : ℂ) : latI φ 𝔞 δ = δ • latI φ 𝔞 1 := by
  unfold latI
  rw [AddSubgroup.pointwise_smul_def]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    exact AddSubgroup.mem_map.2 ⟨φ c, AddSubgroup.subset_closure ⟨c, hc, (one_mul _).symm⟩, rfl⟩
  · refine AddSubgroup.map_le_iff_le_comap.2 ?_
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨c, hc, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, hc, show δ * (1 * φ c) = δ * φ c by rw [one_mul]⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.IdealBasis
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem ib_im_conj_mul (u v : ℂ) : ((starRingEnd ℂ) u * v).im = u.re * v.im - u.im * v.re := by
  simp [Complex.mul_im]; ring

theorem ib_mem_range {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (w : ℂ)
    (hw : w ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ)) :
    ∃ c : 𝓞 K, (φ.comp (algebraMap (𝓞 K) K)) c = w := by
  rw [← h₀] at hw
  have hle : latI φ ⊤ 1 ≤ (φ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom.range := by
    unfold latI
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, by simp⟩
  obtain ⟨c, hc⟩ := hle hw
  exact ⟨c, hc⟩

theorem ib_exists_basis {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (a₀ b₀ : ℂ)
    (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) :
    ∃ B : Module.Basis (Fin 2) ℤ (𝓞 K), (φ.comp (algebraMap (𝓞 K) K)) (B 0) = a₀ ∧
      (φ.comp (algebraMap (𝓞 K) K)) (B 1) = b₀ := by
  obtain ⟨e, he⟩ := ib_mem_range φ a₀ b₀ h₀ a₀ (AddSubgroup.subset_closure (by simp))
  obtain ⟨f, hf⟩ := ib_mem_range φ a₀ b₀ h₀ b₀ (AddSubgroup.subset_closure (by simp))
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  have hinj : Function.Injective ψ :=
    φ.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hli : LinearIndependent ℤ ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (s : ℂ) * a₀ + (t : ℂ) * b₀ = 0 := by
      have := congrArg ψ hst
      simpa [map_add (f := _), map_zsmul, he, hf, zsmul_eq_mul] using this
    rw [ib_im_conj_mul] at hab₀
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    constructor
    · have : (s : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination b₀.im * hre - b₀.re * him
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
    · have : (t : ℝ) * (a₀.re * b₀.im - a₀.im * b₀.re) = 0 := by
        linear_combination a₀.re * him - a₀.im * hre
      exact_mod_cast (mul_eq_zero.mp this).resolve_right hab₀.ne'
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![e, f]) := by
    intro c _
    have hc : ψ c ∈ AddSubgroup.closure ({a₀, b₀} : Set ℂ) := by
      rw [← h₀]
      exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, by simp [hψ]⟩
    obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hc
    have : c = m • e + n • f := hinj (by rw [← hmn]; simp [map_add (f := _), he, hf, zsmul_eq_mul])
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  refine ⟨Module.Basis.mk hli hsp, ?_, ?_⟩ <;> simp [he, hf]

theorem ib_im_det {K : Type} [Field K] [NumberField K] (ψ : 𝓞 K →+* ℂ) (a₀ b₀ : ℂ)
    (B : Module.Basis (Fin 2) ℤ (𝓞 K)) (hB0 : ψ (B 0) = a₀) (hB1 : ψ (B 1) = b₀)
    (v : Fin 2 → 𝓞 K) :
    ((starRingEnd ℂ) (ψ (v 0)) * ψ (v 1)).im = (B.det v : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  have hv : ∀ j, ψ (v j) = (B.repr (v j) 0 : ℂ) * a₀ + (B.repr (v j) 1 : ℂ) * b₀ := by
    intro j
    conv_lhs => rw [← B.sum_repr (v j)]
    simp [Fin.sum_univ_two, map_add (f := _), hB0, hB1, zsmul_eq_mul]
  rw [Module.Basis.det_apply, Matrix.det_fin_two, hv 0, hv 1]
  simp only [Module.Basis.toMatrix_apply, ib_im_conj_mul]
  push_cast
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im]
  ring

theorem latI_basis (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (φ : K →+* ℂ) (a₀ b₀ : ℂ) (hab₀ : 0 < ((starRingEnd ℂ) a₀ * b₀).im)
    (h₀ : latI φ ⊤ 1 = AddSubgroup.closure {a₀, b₀}) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ 𝔞 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = (Ideal.absNorm 𝔞 : ℝ) * ((starRingEnd ℂ) a₀ * b₀).im := by
  set ψ : 𝓞 K →+* ℂ := φ.comp (algebraMap (𝓞 K) K) with hψ
  obtain ⟨B, hB0, hB1⟩ := ib_exists_basis φ a₀ b₀ hab₀ h₀
  set bI := Ideal.selfBasis B 𝔞 h𝔞
  have hdet := Ideal.natAbs_det_basis_change B 𝔞 bI
  set D := B.det ((↑) ∘ bI) with hD
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, Int.natAbs_zero] at hdet
    exact h𝔞 (Ideal.absNorm_eq_zero_iff.mp hdet.symm)
  have hcross := ib_im_det ψ a₀ b₀ B hB0 hB1 ((↑) ∘ bI)
  rw [← hD] at hcross
  simp only [Function.comp_apply] at hcross
  have hN : (Ideal.absNorm 𝔞 : ℝ) = |(D : ℝ)| := by
    rw [← hdet, Nat.cast_natAbs, Int.cast_abs]
  have hlat : latI φ 𝔞 1 = AddSubgroup.closure {ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K)} := by
    apply le_antisymm
    · unfold latI
      rw [AddSubgroup.closure_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [one_mul, SetLike.mem_coe, AddSubgroup.mem_closure_pair]
      have hs := bI.sum_repr ⟨c, hc⟩
      have hc' : c = (bI.repr ⟨c, hc⟩ 0) • (bI 0 : 𝓞 K) + (bI.repr ⟨c, hc⟩ 1) • (bI 1 : 𝓞 K) := by
        have h2 : ((∑ i, bI.repr ⟨c, hc⟩ i • bI i : 𝔞) : 𝓞 K) = c := by rw [hs]
        rw [Fin.sum_univ_two] at h2
        exact h2.symm
      refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
      show _ = ψ c
      conv_rhs => rw [hc']
      simp [map_add (f := _)]
    · rw [AddSubgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨AddSubgroup.subset_closure ⟨_, (bI 0).2, by simp [hψ]⟩,
        AddSubgroup.subset_closure ⟨_, (bI 1).2, by simp [hψ]⟩⟩
  rcases lt_or_gt_of_ne hD0 with hneg | hpos
  · have hneg' : (D : ℝ) < 0 := by exact_mod_cast hneg
    have hsw : ((starRingEnd ℂ) (ψ (bI 1 : 𝓞 K)) * ψ (bI 0 : 𝓞 K)).im =
        -((starRingEnd ℂ) (ψ (bI 0 : 𝓞 K)) * ψ (bI 1 : 𝓞 K)).im := by
      rw [ib_im_conj_mul, ib_im_conj_mul]; ring
    refine ⟨ψ (bI 1 : 𝓞 K), ψ (bI 0 : 𝓞 K), ?_, by rw [hlat, Set.pair_comm], ?_⟩
    · rw [hsw, hcross]; nlinarith
    · rw [hsw, hcross, hN, abs_of_neg hneg']; ring
  · have hpos' : (0 : ℝ) < D := by exact_mod_cast hpos
    refine ⟨ψ (bI 0 : 𝓞 K), ψ (bI 1 : 𝓞 K), ?_, hlat, ?_⟩
    · rw [hcross]; positivity
    · rw [hcross, hN, abs_of_pos hpos']

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Jacobi
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem jac_riemannZeta_six : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (show (3 : ℕ) ≠ 0 by norm_num)
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four]
    norm_num [Nat.choose]
  have hb : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5]
    norm_num [Nat.choose]
  rw [show (6 : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h, hb]
  norm_num [Nat.factorial]
  ring

theorem jac_mem_closure (a z w : ℂ) :
    w ∈ AddSubgroup.closure ({a, a * z} : Set ℂ) ↔ ∃ v : Fin 2 → ℤ, w = a * ((v 0 : ℂ) * z + v 1) := by
  rw [AddSubgroup.mem_closure_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨![n, m], ?_⟩
    simp [zsmul_eq_mul]
    ring
  · rintro ⟨v, rfl⟩
    exact ⟨v 1, v 0, by simp [zsmul_eq_mul]; ring⟩

theorem jac_inj (z : ℂ) (hz : 0 < z.im) :
    Function.Injective (fun v : Fin 2 → ℤ => (v 0 : ℂ) * z + v 1) := by
  intro v w h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero] at him
  have h0r : ((v 0 : ℤ) : ℝ) = ((w 0 : ℤ) : ℝ) := mul_right_cancel₀ hz.ne' him
  have h0 : v 0 = w 0 := by exact_mod_cast h0r
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
    sub_zero] at hre
  rw [h0r] at hre
  have h1 : v 1 = w 1 := by
    have h2 : ((v 1 : ℤ) : ℝ) = ((w 1 : ℤ) : ℝ) := by linarith
    exact_mod_cast h2
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem jac_eisG (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) (k : ℕ) (hk : k ≠ 0) :
    eisG (AddSubgroup.closure {a, a * z}) k =
      (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ,
        EisensteinSeries.eisSummand ((2 * k : ℕ) : ℤ) v (⟨z, hz⟩ : UpperHalfPlane) := by
  unfold eisG
  have hinj := jac_inj z hz
  let f : {v : Fin 2 → ℤ // v ≠ 0} → {w : ℂ // w ∈ AddSubgroup.closure ({a, a * z} : Set ℂ) ∧ w ≠ 0} :=
    fun v => ⟨a * ((v.1 0 : ℂ) * z + v.1 1), (jac_mem_closure a z _).mpr ⟨v.1, rfl⟩,
      mul_ne_zero ha (fun h => v.2 (hinj (by simpa using h)))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      have h1 := congrArg Subtype.val h
      exact Subtype.ext (hinj (mul_left_cancel₀ ha h1))
    · rintro ⟨w, hw, hw0⟩
      obtain ⟨v, rfl⟩ := (jac_mem_closure a z w).mp hw
      refine ⟨⟨v, fun hv => hw0 (by simp [hv])⟩, rfl⟩
  rw [← (Equiv.ofBijective f hf).tsum_eq]
  have hsupp : Function.support (fun v : Fin 2 → ℤ =>
      EisensteinSeries.eisSummand ((2 * k : ℕ) : ℤ) v (⟨z, hz⟩ : UpperHalfPlane)) ⊆ {v | v ≠ 0} := by
    intro v hv
    by_contra hv0
    simp only [Set.mem_setOf_eq, not_not] at hv0
    apply hv
    subst hv0
    have hk2 : ((2 * k : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : 2 * k ≠ 0)
    simp [EisensteinSeries.eisSummand]
    exact zero_zpow _ (by omega)
  rw [← tsum_subtype_eq_of_support_subset hsupp, ← tsum_mul_left]
  refine tsum_congr fun v => ?_
  simp only [Equiv.ofBijective_apply, f, EisensteinSeries.eisSummand, UpperHalfPlane.coe_mk, zpow_natCast]
  rw [mul_pow, one_div, mul_inv, zpow_neg, zpow_natCast]

theorem E4_eq_half_eisensteinSeries (z : UpperHalfPlane) :
    ModularForm.E₄ z = 1 / 2 * _root_.eisensteinSeries (N := 1) 0 (4 : ℕ) z := rfl

theorem E6_eq_half_eisensteinSeries (z : UpperHalfPlane) :
    ModularForm.E₆ z = 1 / 2 * _root_.eisensteinSeries (N := 1) 0 (6 : ℕ) z := rfl

theorem eisenstein_G4_closure (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) :
    eisG (AddSubgroup.closure {a, a * z}) 2 =
      (a ^ 4)⁻¹ * (2 * ((Real.pi : ℂ) ^ 4 / 90) * ModularForm.E₄ (⟨z, hz⟩ : UpperHalfPlane)) := by
  rw [jac_eisG a z ha hz 2 (by norm_num)]
  have h2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 4) (by norm_num) (⟨z, hz⟩ : UpperHalfPlane)
  rw [show ((2 * 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by norm_num, h2, E4_eq_half_eisensteinSeries,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four, show a ^ (2 * 2) = a ^ 4 by norm_num]
  ring

theorem eisenstein_G6_closure (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) :
    eisG (AddSubgroup.closure {a, a * z}) 3 =
      (a ^ 6)⁻¹ * (2 * ((Real.pi : ℂ) ^ 6 / 945) * ModularForm.E₆ (⟨z, hz⟩ : UpperHalfPlane)) := by
  rw [jac_eisG a z ha hz 3 (by norm_num)]
  have h2 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries (k := 6) (by norm_num) (⟨z, hz⟩ : UpperHalfPlane)
  rw [show ((2 * 3 : ℕ) : ℤ) = ((6 : ℕ) : ℤ) by norm_num, h2, E6_eq_half_eisensteinSeries,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, jac_riemannZeta_six, show a ^ (2 * 3) = a ^ 6 by norm_num]
  ring

theorem jac_discr (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) :
    discr (AddSubgroup.closure {a, a * z}) = (2 * Real.pi / a) ^ 12 * ModularForm.eta z ^ 24 := by
  have hD := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq (⟨z, hz⟩ : UpperHalfPlane)
  have hD' : ModularForm.discriminant (⟨z, hz⟩ : UpperHalfPlane) = ModularForm.eta z ^ 24 := rfl
  rw [hD'] at hD
  rw [discr, g2, g3, eisenstein_G4_closure a z ha hz, eisenstein_G6_closure a z ha hz, hD]
  field_simp
  ring

theorem discr_closure_pair (a b : ℂ) (hab : 0 < (b / a).im) :
    discr (AddSubgroup.closure {a, b}) = (2 * Real.pi / a) ^ 12 * ModularForm.eta (b / a) ^ 24 := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  have h := jac_discr a (b / a) ha hab
  rw [show a * (b / a) = b by field_simp] at h
  exact h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
end
end

