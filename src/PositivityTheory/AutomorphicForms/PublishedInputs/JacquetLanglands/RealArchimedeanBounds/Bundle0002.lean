module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DEntryP
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.MatrixEntryBounds

theorem abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]

theorem abs_le_of_sq (t s : ℝ) (hs : 0 ≤ s) (h : t ^ 2 ≤ s ^ 2) : |t| ≤ s := by
  have := sq_le_sq.1 h
  rwa [abs_of_nonneg hs] at this

theorem core (δ C c0 x y x' y' a b c d M L R K : ℝ) (hδ : 0 < δ) (hc0 : 0 < c0) (hx : |x| ≤ C)
    (hy : c0 ≤ |y|) (hdet : |a * d - b * c| ≤ C) (hM : M * δ = 4 * C) (hL : L * c0 ^ 2 = M)
    (hR : R * c0 = C) (hK : K * (c0 ^ 2 * δ ^ 2) = 2 * C ^ 2 * δ ^ 2 + 48 * c0 ^ 2)
    (hyy : 0 < y * y') (hk : δ * ((x - x') ^ 2 + (y + y') ^ 2) ≤ 4 * (y * y'))
    (hden : y' * ((c * x + d) ^ 2 + (c * y) ^ 2) = (a * d - b * c) * y)
    (hre : x' * (c * x + d) - y' * (c * y) = a * x + b)
    (him : x' * (c * y) + y' * (c * x + d) = a * y) :
    |c| ≤ 1 + L ∧ |d| ≤ 1 + M + (1 + L) * C ∧ |a| ≤ 1 + K * M ∧ |b| ≤ (1 + K * M) * (1 + R) * |y| := by
  have hC : 0 ≤ C := (abs_nonneg x).trans hx
  have hy0 : 0 < |y| := hc0.trans_le hy
  have hy'0 : y' ≠ 0 := right_ne_zero_of_mul hyy.ne'
  have hay' : 0 < |y'| := abs_pos.2 hy'0
  have hyy' : y * y' = |y| * |y'| := by rw [← abs_mul, abs_of_pos hyy]
  have h1 : δ * y ^ 2 ≤ 4 * (y * y') := by
    linarith [mul_nonneg hδ.le (sq_nonneg (x - x')), mul_nonneg hδ.le (sq_nonneg y'), mul_pos hδ hyy]
  have h2 : δ * y' ^ 2 ≤ 4 * (y * y') := by
    linarith [mul_nonneg hδ.le (sq_nonneg (x - x')), mul_nonneg hδ.le (sq_nonneg y), mul_pos hδ hyy]
  have h3 : δ * (x - x') ^ 2 ≤ 4 * (y * y') := by
    linarith [mul_nonneg hδ.le (sq_nonneg y'), mul_nonneg hδ.le (sq_nonneg y), mul_pos hδ hyy]
  set N := (c * x + d) ^ 2 + (c * y) ^ 2 with hN
  have e : (y * y') * (δ * N) = (a * d - b * c) * (δ * y ^ 2) := by linear_combination (δ * y) * hden
  have e2 : (a * d - b * c) * (δ * y ^ 2) ≤ C * (4 * (y * y')) := by
    calc (a * d - b * c) * (δ * y ^ 2) ≤ |a * d - b * c| * (δ * y ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ C * (δ * y ^ 2) := mul_le_mul_of_nonneg_right hdet (by positivity)
      _ ≤ C * (4 * (y * y')) := mul_le_mul_of_nonneg_left h1 hC
  have hδN : δ * N ≤ 4 * C := le_of_mul_le_mul_left (by linarith [e, e2]) hyy
  have hNM : N ≤ M := le_of_mul_le_mul_right (by linarith [hδN, hM]) hδ
  have hN0 : 0 ≤ N := by positivity
  have hcy : (c * y) ^ 2 ≤ M := by linarith [sq_nonneg (c * x + d)]
  have hcxd : (c * x + d) ^ 2 ≤ M := by linarith [sq_nonneg (c * y)]
  have hc0y : c0 ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ hc0.le hy 2
  have hc2 : c ^ 2 ≤ L := by
    have : c ^ 2 * c0 ^ 2 ≤ L * c0 ^ 2 := by
      rw [hL]; linarith [mul_le_mul_of_nonneg_left hc0y (sq_nonneg c)]
    exact le_of_mul_le_mul_right this (by positivity)
  have hc : |c| ≤ 1 + L := (abs_le_one_add_sq c).trans (by linarith)
  have hcxd' : |c * x + d| ≤ 1 + M := (abs_le_one_add_sq _).trans (by linarith)
  have hcx : |c * x| ≤ (1 + L) * C := by
    rw [abs_mul]; exact mul_le_mul hc hx (abs_nonneg _) ((abs_nonneg c).trans hc)
  have hd : |d| ≤ 1 + M + (1 + L) * C := by
    have a1 := abs_le.1 hcxd'
    have a2 := abs_le.1 hcx
    exact abs_le.2 ⟨by linarith [a1.1, a2.2], by linarith [a1.2, a2.1]⟩

  have hy' : δ * |y'| ≤ 4 * |y| := by
    have : |y'| * (δ * |y'|) ≤ |y'| * (4 * |y|) := by
      calc |y'| * (δ * |y'|) = δ * y' ^ 2 := by rw [← sq_abs y']; ring
        _ ≤ 4 * (y * y') := h2
        _ = |y'| * (4 * |y|) := by rw [hyy']; ring
    exact le_of_mul_le_mul_left this hay'
  have A2 : δ ^ 2 * y' ^ 2 ≤ 16 * y ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hy' 2
    rw [mul_pow, mul_pow, sq_abs, sq_abs] at this
    linarith
  have A1 : δ ^ 2 * (x - x') ^ 2 ≤ 16 * y ^ 2 := by
    have h4 : δ * (δ * (x - x') ^ 2) ≤ δ * (4 * (y * y')) := mul_le_mul_of_nonneg_left h3 hδ.le
    have h5 : δ * (4 * (y * y')) ≤ 16 * y ^ 2 := by
      rw [hyy']
      linarith [mul_le_mul_of_nonneg_left hy' (abs_nonneg y), sq_abs y]
    linarith
  have A3 : c0 ^ 2 * x ^ 2 ≤ C ^ 2 * y ^ 2 := by
    have hx2 : x ^ 2 ≤ C ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    have := mul_le_mul hc0y hx2 (sq_nonneg _) (sq_nonneg _)
    linarith
  have hW : x' ^ 2 + y' ^ 2 ≤ K * y ^ 2 := by
    have hp : 0 < c0 ^ 2 * δ ^ 2 := by positivity
    refine le_of_mul_le_mul_right ?_ hp
    have : K * y ^ 2 * (c0 ^ 2 * δ ^ 2) = (2 * C ^ 2 * δ ^ 2 + 48 * c0 ^ 2) * y ^ 2 := by rw [← hK]; ring
    rw [this]
    linarith [mul_le_mul_of_nonneg_left A1 (sq_nonneg c0), mul_le_mul_of_nonneg_left A2 (sq_nonneg c0),
      mul_le_mul_of_nonneg_left A3 (sq_nonneg δ), mul_nonneg (sq_nonneg (c0 * δ)) (sq_nonneg (2 * x - x'))]
  have E : (a * x + b) ^ 2 + (a * y) ^ 2 = (x' ^ 2 + y' ^ 2) * N := by rw [hN, ← hre, ← him]; ring
  have hKM : (x' ^ 2 + y' ^ 2) * N ≤ K * y ^ 2 * M :=
    mul_le_mul hW hNM hN0 ((add_nonneg (sq_nonneg _) (sq_nonneg _)).trans hW)
  have hy2 : 0 < y ^ 2 := by rw [← sq_abs]; positivity
  have hKM0 : 0 ≤ K * M := by
    have : 0 ≤ K * M * y ^ 2 := by linarith [sq_nonneg (a * x + b), sq_nonneg (a * y)]
    exact nonneg_of_mul_nonneg_left this hy2
  have ha2 : a ^ 2 ≤ K * M := by
    have : a ^ 2 * y ^ 2 ≤ K * M * y ^ 2 := by linarith [sq_nonneg (a * x + b)]
    exact le_of_mul_le_mul_right this hy2
  have ha : |a| ≤ 1 + K * M := (abs_le_one_add_sq a).trans (by linarith)
  have hb1 : |a * x + b| ≤ (1 + K * M) * |y| := by
    apply abs_le_of_sq _ _ (by positivity)
    rw [mul_pow, sq_abs]
    linarith [sq_nonneg (a * y), mul_le_mul_of_nonneg_right (show K * M ≤ (1 + K * M) ^ 2 by linarith [sq_nonneg (K * M)])
      (sq_nonneg y)]
  have hR0 : 0 ≤ R := by
    by_contra h
    have := mul_neg_of_neg_of_pos (not_le.1 h) hc0
    linarith
  have hxR : |x| ≤ R * |y| := hx.trans (by rw [← hR]; exact mul_le_mul_of_nonneg_left hy hR0)
  have hax : |a * x| ≤ (1 + K * M) * (R * |y|) := by
    rw [abs_mul]; exact mul_le_mul ha hxR (abs_nonneg _) (by linarith)
  refine ⟨hc, hd, ha, ?_⟩
  have b1 := abs_le.1 hb1
  have b2 := abs_le.1 hax
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [b1.1, b1.2, b2.1, b2.2]

end UpperTheory.Esk.MatrixEntryBounds

namespace UpperTheory.Esk.MatrixEntryBounds

theorem main : ∀ δ C c : ℝ, 0 < δ → 0 < c → ∃ B : ℝ, ∀ (g : GL (Fin 2) ℝ) (z : P), |z.1.re| ≤ C → c ≤ |z.1.im| →
    |g.val.det| ≤ C → δ ≤ kap z (g • z) → |g 1 0| ≤ B ∧ |g 0 0| ≤ B ∧ |g 1 1| ≤ B ∧ |g 0 1| ≤ B * |z.1.im| := by
  intro δ C c0 hδ hc0
  have hM : (4 * C / δ) * δ = 4 * C := div_mul_cancel₀ _ hδ.ne'
  have hL : (4 * C / δ / c0 ^ 2) * c0 ^ 2 = 4 * C / δ := div_mul_cancel₀ _ (by positivity)
  have hR : (C / c0) * c0 = C := div_mul_cancel₀ _ hc0.ne'
  have hK : (2 * C ^ 2 / c0 ^ 2 + 48 / δ ^ 2) * (c0 ^ 2 * δ ^ 2) = 2 * C ^ 2 * δ ^ 2 + 48 * c0 ^ 2 := by
    field_simp
  refine ⟨max (max (1 + 4 * C / δ / c0 ^ 2) (1 + 4 * C / δ + (1 + 4 * C / δ / c0 ^ 2) * C))
    (max (1 + (2 * C ^ 2 / c0 ^ 2 + 48 / δ ^ 2) * (4 * C / δ))
      ((1 + (2 * C ^ 2 / c0 ^ 2 + 48 / δ ^ 2) * (4 * C / δ)) * (1 + C / c0))), ?_⟩
  intro g z hx hy hdet hk
  unfold kap at hk
  split_ifs at hk with hyy
  swap
  · exact absurd hk (not_le.2 hδ)
  have hn : ‖z.1 - (starRingEnd ℂ) (g • z).1‖ ^ 2 = (z.1.re - (g • z).1.re) ^ 2 + (z.1.im + (g • z).1.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hpos : 0 < (z.1.re - (g • z).1.re) ^ 2 + (z.1.im + (g • z).1.im) ^ 2 := by
    nlinarith [sq_nonneg (z.1.re - (g • z).1.re), sq_nonneg (z.1.im - (g • z).1.im)]
  rw [hn, le_div_iff₀ hpos] at hk
  have hns : Complex.normSq (den g z.1) = (g 1 0 * z.1.re + g 1 1) ^ 2 + (g 1 0 * z.1.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp [den]; ring
  have hne : Complex.normSq (den g z.1) ≠ 0 := (Complex.normSq_pos.2 (den_ne g z.2)).ne'
  have hden : (g • z).1.im * ((g 1 0 * z.1.re + g 1 1) ^ 2 + (g 1 0 * z.1.im) ^ 2) =
      (g 0 0 * g 1 1 - g 0 1 * g 1 0) * z.1.im := by
    rw [← hns, coe_smul, im_div, det_eq, div_mul_cancel₀ _ hne]
  have hW : (g • z).1 * den g z.1 = num g z.1 := by rw [coe_smul, div_mul_cancel₀ _ (den_ne g z.2)]
  have hre := congrArg Complex.re hW
  have him := congrArg Complex.im hW
  simp [num, den, Complex.mul_re, Complex.mul_im] at hre him
  obtain ⟨h1, h2, h3, h4⟩ := core δ C c0 z.1.re z.1.im (g • z).1.re (g • z).1.im (g 0 0) (g 0 1) (g 1 0) (g 1 1)
    _ _ _ _ hδ hc0 hx hy (by rwa [det_eq] at hdet) hM hL hR hK hyy hk hden
    (by linear_combination hre) (by linear_combination him)
  refine ⟨h1.trans ((le_max_left _ _).trans (le_max_left _ _)), h3.trans ((le_max_left _ _).trans (le_max_right _ _)),
    h2.trans ((le_max_right _ _).trans (le_max_left _ _)),
    h4.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (abs_nonneg _))⟩

end UpperTheory.Esk.MatrixEntryBounds

theorem UpperTheory.Esk.dEntry : UpperTheory.Esk.DEntry := UpperTheory.Esk.MatrixEntryBounds.main
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DGoodP
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.GoodOperatorConjugation

variable {F : Type} [Field F] [NumberField F]

theorem v_lt_of_max {w : Pl F} {y : w.adicCompletionIntegers F}
    (hy : y ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F)) : Valued.v (y : w.adicCompletion F) < 1 := by
  refine lt_of_le_of_ne y.2 fun h1 => mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hy) ?_
  have h0 : (y : w.adicCompletion F) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  have hi : (y : w.adicCompletion F)⁻¹ ∈ w.adicCompletionIntegers F := by
    show Valued.v ((y : w.adicCompletion F)⁻¹) ≤ 1
    rw [map_inv₀, h1, inv_one]
  exact ⟨⟨y, ⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0), Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩

theorem congruence_subgroup_entry_valuations_alt {w : Pl F} {c : ℕ} (hc : c ≠ 0) {g : GL (Fin 2) (w.adicCompletion F)} (hg : g ∈ K1 w c) :
    (∀ a b, Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) a b) ≤ 1) ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 0) < 1 ∧
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1) < 1 := by
  obtain ⟨k, hk, rfl⟩ := hg
  have hk' := Subgroup.mem_comap.1 hk
  change ![(0 : (w.adicCompletionIntegers F) ⧸ (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)), 1] ᵥ* _ =
    ![0, 1] at hk'
  rw [funext_iff, Fin.forall_fin_two] at hk'
  simp [Matrix.vecMul, dotProduct] at hk'
  obtain ⟨h1, h2⟩ := hk'
  have hle : IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.pow_le_self hc
  refine ⟨fun a b => (k a b).2, v_lt_of_max (hle ?_), ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  · have : k 1 1 - 1 ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) :=
      hle (Ideal.Quotient.eq.1 (by rw [h2, map_one]))
    have h3 := v_lt_of_max this
    simpa using h3

theorem tr_conj {R : Type} [CommRing R] (X : GL (Fin 2) R) (T : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (((X⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * T * (X : Matrix (Fin 2) (Fin 2) R)) = Matrix.trace T := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem det_conj' {R : Type} [CommRing R] (X : GL (Fin 2) R) (T : Matrix (Fin 2) (Fin 2) R) :
    Matrix.det (((X⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * T * (X : Matrix (Fin 2) (Fin 2) R)) = Matrix.det T := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_mul]

variable [IsTotallyReal F]

theorem good_of {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ) {W : List (Pl F)} {n : ℕ}
    {a : Fin n → GF F} (ha : IsReps c W a) : (mkDat c χ).Good a := by
  intro f hf x h
  have hf' : ∀ g (h : Hc c), f (g * h) = χ h * f g := hf
  have hzc : ∀ z, zc F z ∈ Hc c := fun z => Subgroup.mem_sup_right ⟨z, rfl⟩
  have hχz : ∀ z, χ ⟨zc F z, hzc z⟩ = ω.1 (finId F z) := fun z =>
    (hχ ⟨zc F z, hzc z⟩).2 1 (Subgroup.one_mem _) z (one_mul _).symm
  have hK : f ∈ Hi.fixd (Hi.rtr ℂ (GF F) ℂ) (Kc c) := by
    intro u hu
    funext g
    have hu' : u ∈ Hc c := Subgroup.mem_sup_left hu
    have h1 : χ ⟨u, hu'⟩ = 1 := by
      rw [(hχ ⟨u, hu'⟩).2 u hu 1 (by rw [map_one, mul_one]), map_one, map_one]
    rw [Hi.rtr_apply, hf' g ⟨u, hu'⟩, h1, Units.val_one, one_mul]
  have hs := (ha.act (GF F → ℂ) (Hi.rtr ℂ (GF F) ℂ) f hK).1
  obtain ⟨k, hk, z, hz⟩ := (hχ h).1
  have hfix := congrFun (hs k hk) x
  simp only [Hi.rtr_apply, Finset.sum_apply] at hfix
  change ∑ i, f (x * (h : GF F) * a i) = (χ h : ℂ) * ∑ i, f (x * a i)
  rw [(hχ h).2 k hk z hz, ← hχz z, ← hfix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hz, ← hf' (x * k * a i) ⟨zc F z, hzc z⟩]
  have hc := Subgroup.mem_center_iff.1 (zc_center z) (a i)
  congr 1
  simp only [mul_assoc]
  rw [hc]

theorem reg_of {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ) {W : List (Pl F)} {n : ℕ}
    {a : Fin n → GF F} (ha : IsReps c W a) {w : Pl F} (hw : w ∈ W) (hc : c w ≠ 0) : (mkDat c χ).Reg a := by
  classical
  intro γ x i hmem
  obtain ⟨k, hk, z, hz⟩ := (hχ ⟨_, hmem⟩).1
  have hz' : (a i)⁻¹ * (x⁻¹ * jF F γ * x) = k * zc F z := hz
  have e : x⁻¹ * jF F γ * x = a i * (k * zc F z) := by rw [← hz', mul_inv_cancel_left]
  obtain ⟨u, hu⟩ := ha.loc i w hc
  let φ : GF F →* GL (Fin 2) (w.adicCompletion F) := Matrix.GeneralLinearGroup.map (pLoc F w)
  let ψ : F →+* w.adicCompletion F := (pLoc F w).comp (algebraMap F (Af F))
  let r : ℕ := W.count w
  have hr : 0 < r := List.count_pos_iff.2 hw
  let p : w.adicCompletion F := ((atFin w (unif w) ^ r : (w.adicCompletion F)ˣ) : w.adicCompletion F)
  let zw : w.adicCompletion F := pLoc F w (z : Af F)
  have e2 := congrArg (fun g => ((φ g : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F))) e
  simp only [map_mul, map_inv, Units.val_mul] at e2
  obtain ⟨M, hMk⟩ : ∃ M : Matrix (Fin 2) (Fin 2) (w.adicCompletion F),
      ((φ k : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) = M := ⟨_, rfl⟩
  rw [hMk] at e2
  have hA : ((φ (a i) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![p, (u : w.adicCompletion F); 0, 1] := by
    rw [show φ (a i) = _ from hu]; rfl
  have hZ : ((φ (zc F z) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![zw, 0; 0, zw] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [φ, zw, zc, Matrix.GeneralLinearGroup.map]
  have hT : ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) =
      !![ψ (γ 0 0), ψ (γ 0 1); ψ (γ 1 0), ψ (γ 1 1)] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have htr : ψ (γ.val.trace) = zw * (p * M 0 0 + u * M 1 0 + M 1 1) := by
    have := tr_conj (φ x) ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)))
    rw [e2, hA, hZ, hT, Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.trace_fin_two_of,
      Matrix.trace_fin_two_of] at this
    rw [Matrix.trace_fin_two, map_add (f := _)]
    change ψ (γ 0 0) + ψ (γ 1 1) = _
    rw [← this]; ring
  have hdet : ψ (γ.val.det) = zw ^ 2 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) := by
    have := det_conj' (φ x) ((φ (jF F γ) : GL (Fin 2) (w.adicCompletion F)))
    rw [e2, hA, hZ, hT, Matrix.eta_fin_two M, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.det_fin_two_of,
      Matrix.det_fin_two_of] at this
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
    change ψ (γ 0 0) * ψ (γ 1 1) - ψ (γ 0 1) * ψ (γ 1 0) = _
    rw [← this]; ring

  have hkl : φ k ∈ K1 w (c w) := Subgroup.mem_iInf.1 hk w
  obtain ⟨hM, hM10, hM11⟩ := congruence_subgroup_entry_valuations_alt hc hkl
  simp only [hMk] at hM hM10 hM11
  have hp : Valued.v p < 1 := by
    have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      unif_spec w
    have h2 : WithZero.exp (-1 : ℤ) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    show Valued.v (((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) ^ r) < 1
    rw [map_pow, h1]
    exact pow_lt_one₀ zero_le h2 hr.ne'
  have hu1 : Valued.v (u : w.adicCompletion F) ≤ 1 := u.2
  have ht : Valued.v (p * M 0 0 + u * M 1 0 + M 1 1) = 1 := by
    have h1 : Valued.v (p * M 0 0 + u * M 1 0 + (M 1 1 - 1)) < 1 := by
      refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ ?_) hM11
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' (hM 0 0)) hp
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hu1) hM10
    rw [show p * M 0 0 + u * M 1 0 + M 1 1 = 1 + (p * M 0 0 + u * M 1 0 + (M 1 1 - 1)) by ring]
    exact Valuation.map_one_add_of_lt _ h1
  have hzw : zw ≠ 0 := (Units.map (pLoc F w).toMonoidHom z).ne_zero
  have ht0 : p * M 0 0 + u * M 1 0 + M 1 1 ≠ 0 := fun e => by rw [e, map_zero] at ht; exact zero_ne_one ht
  refine ⟨fun h0 => ?_, fun h4 => ?_⟩
  · rw [h0, map_zero] at htr
    exact mul_ne_zero hzw ht0 htr.symm
  · have h5 := congrArg ψ h4
    rw [map_pow, map_mul, htr, hdet, map_ofNat] at h5
    have h6 : (p * M 0 0 + u * M 1 0 + M 1 1) ^ 2 = 4 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0)) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hzw)
      linear_combination h5
    have h7 := congrArg Valued.v h6
    rw [map_pow, ht, one_pow] at h7
    have h4v : Valued.v (4 : w.adicCompletion F) ≤ 1 := by
      have := natCast_mem (w.adicCompletionIntegers F) 4
      rw [Nat.cast_ofNat] at this
      exact this
    have hd : Valued.v (M 0 0 * M 1 1 - M 0 1 * M 1 0) ≤ 1 := by
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (hM _ _) (hM _ _)
    have : Valued.v (4 * (p * (M 0 0 * M 1 1 - M 0 1 * M 1 0))) < 1 := by
      rw [map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' h4v) (lt_of_le_of_lt (mul_le_of_le_one_right' hd) hp)
    exact absurd h7 (ne_of_gt this)

end UpperTheory.Esk.GoodOperatorConjugation

namespace UpperTheory.Esk

theorem dGood : AMem → DGood := by
  intro _ F _ _ _ c ω χ hχ W n a ha
  exact ⟨GoodOperatorConjugation.good_of hχ ha, fun ⟨w, hw, hc⟩ => GoodOperatorConjugation.reg_of hχ ha hw hc⟩

end UpperTheory.Esk
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DNormalP
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

namespace UnipotentNormalization

def up {F : Type} [Field F] (u t : F) (hu : u ≠ 0) : GL (Fin 2) F :=
  ⟨!![u, t; 0, 1], !![u⁻¹, -t * u⁻¹; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu] <;> field_simp <;> ring,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu] <;> field_simp <;> ring⟩

theorem up_mem (hM : AMem) {F : Type} [Field F] [NumberField F] (u t : F) (hu : u ≠ 0)
    (h1 : IsIntegral ℤ u) (h2 : IsIntegral ℤ u⁻¹) (h3 : IsIntegral ℤ t) : jF F (up u t hu) ∈ K0 F := by
  have hI : ∀ g : GL (Fin 2) F, (∀ i j, IsIntegral ℤ (g.val i j)) → ∀ i j, (jF F g).val i j ∈ Ohat F := by
    intro g hg i j
    change algebraMap F (Af F) (g.val i j) ∈ Ohat F
    exact ((hM F).2.2.2.2.2.1 _).1 (hg i j)
  refine ((hM F).1 _).2 ⟨hI _ ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [up, h1, h3, isIntegral_zero, isIntegral_one]
  · rw [← map_inv]
    refine hI _ ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp [up, h2, isIntegral_zero, isIntegral_one, h3.mul h2]

theorem ht01 {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf) (z : X I) (x : Gf) :
    D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

theorem ht_inv {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)
    (h2 : ∀ s : Fin 2 → F, s ≠ 0 → ∀ γ x, D.hf s (D.j γ * x) * ∏ v, |D.σ v γ.val.det| = D.hf (s ᵥ* γ.val) x)
    (h3 : ∀ s : Fin 2 → F, s ≠ 0 → ∀ a : F, a ≠ 0 → ∀ x, D.hf (a • s) x = D.hf s x * ∏ v, D.σ v a ^ 2)
    (b : GL (Fin 2) F) (hb : b 1 0 = 0) (z : X I) (x : Gf) :
    D.Ht ![0, 1] (D.act b z) (D.j b * x) = D.Ht ![0, 1] z x := by
  have hs : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  have hdb : b.val.det = b 0 0 * b 1 1 := by
    rw [Matrix.det_fin_two]; simp [hb]
  have hdet : b.val.det ≠ 0 := b.det_ne_zero
  have hd : b 1 1 ≠ 0 := fun e => hdet (by rw [hdb, e, mul_zero])
  have hv : (![0, 1] : Fin 2 → F) ᵥ* b.val = b 1 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb]
  have key := h2 _ hs b x
  rw [hv, h3 _ hs _ hd] at key
  have him : ∀ v, ((D.act b z v).1).im = D.σ v (b 0 0) / D.σ v (b 1 1) * (z v).1.im := by
    intro v
    have hσ : D.σ v (b 1 1) ≠ 0 := (map_ne_zero _).2 hd
    simp only [Dat.act, coe_smul]
    rw [im_div, det_eq]
    simp [den, Dat.r, hb, Complex.normSq_ofReal]
    field_simp
  rw [ht01, ht01]
  simp_rw [him]
  have hpd : ∏ v, |D.σ v b.val.det| ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => abs_ne_zero.2 ((map_ne_zero _).2 hdet)
  apply mul_right_cancel₀ hpd
  have e : (∏ v, |D.σ v (b 0 0) / D.σ v (b 1 1) * (z v).1.im|) * ∏ v, D.σ v (b 1 1) ^ 2 =
      (∏ v, |(z v).1.im|) * ∏ v, |D.σ v b.val.det| := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hσ : D.σ v (b 1 1) ≠ 0 := (map_ne_zero _).2 hd
    rw [hdb, map_mul, abs_mul, abs_mul, abs_div, ← sq_abs (D.σ v (b 1 1))]
    have : |D.σ v (b 1 1)| ≠ 0 := abs_ne_zero.2 hσ
    field_simp
  rw [mul_assoc, key]
  linear_combination D.hf ![0, 1] x * e

theorem act_up {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (c : Pl F → ℕ) (χ : Hc c →* ℂˣ)
    (u t : F) (hu : u ≠ 0) (z : X (InfinitePlace F)) (v : InfinitePlace F) :
    (((mkDat c χ).act (up u t hu) z) v).1 = (sg v u : ℂ) * (z v).1 + (sg v t : ℂ) := by
  simp [Dat.act, coe_smul, num, den, Dat.r, up, mkDat]

theorem low {ι : Type} [Fintype ι] (y : ι → ℝ) {C c₀ M : ℝ} (hC : 0 < C) (hM : 0 < M)
    (hy : ∀ v v', |y v| ≤ C * |y v'|) (h : c₀ ≤ (∏ v, |y v|) * M) (v : ι) : min 1 (c₀ / M) / C ≤ |y v| := by
  rw [div_le_iff₀ hC, mul_comm]
  have ha : 0 ≤ C * |y v| := by positivity
  rcases le_or_gt 1 (C * |y v|) with h1 | h1
  · exact (min_le_left _ _).trans h1
  · have : Nonempty ι := ⟨v⟩
    have hp : ∏ v', |y v'| ≤ (C * |y v|) ^ Fintype.card ι := by
      rw [← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun v' _ => hy v' v
    have hpow := pow_le_of_le_one ha h1.le (Fintype.card_ne_zero (α := ι))
    have hcm : c₀ / M ≤ C * |y v| := by
      rw [div_le_iff₀ hM]
      exact h.trans (mul_le_mul_of_nonneg_right (hp.trans hpow) hM.le)
    exact (min_le_right _ _).trans hcm

end UnipotentNormalization

open UnipotentNormalization in
theorem dNormal : AMem → ABnfH → AOrb → AUnit → ATrans → DHt → DMul → DNormal := by
  intro hM hB hO hU hT hH hMu F _ _ _ c hc χ c₀ hc₀
  classical
  obtain ⟨S0, hS0⟩ := hB F c hc
  choose S' hS' using fun x1 : GF F => hO F c hc x1
  obtain ⟨CU, hCU, hU'⟩ := hU F
  obtain ⟨CT, hCT, hT'⟩ := hT F
  obtain ⟨-, h2, h3⟩ := hH F c hc χ
  obtain ⟨hm, -⟩ := hMu F c hc χ
  have hs : (![0, 1] : Fin 2 → F) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  set S := S0.biUnion S' with hSdef
  set M : ℝ := 1 + ∑ x' ∈ S, |(mkDat c χ).hf ![0, 1] x'| with hMdef
  have hM0 : 0 < M := by positivity
  have hMS : ∀ x' ∈ S, (mkDat c χ).hf ![0, 1] x' ≤ M := fun x' hx' =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun x' => |(mkDat c χ).hf ![0, 1] x'|)
      (fun _ _ => abs_nonneg _) hx').trans (le_add_of_nonneg_left zero_le_one))
  refine ⟨S, max CU CT, min 1 (c₀ / M) / CU, by positivity, fun z x hz => ?_⟩
  obtain ⟨b1, hb1, x1, hx1, h1, hh1, e1⟩ := hS0 x
  obtain ⟨u, hu0, hui, hui', hu⟩ := hU' (fun v => (((mkDat c χ).act b1 z) v).1.im) (fun v => (((mkDat c χ).act b1 z) v).2)
  obtain ⟨t, hti, ht⟩ := hT' (fun v => sg v u * (((mkDat c χ).act b1 z) v).1.re)
  obtain ⟨x', hx', h2', hh2, e2⟩ := hS' x1 _ (up_mem hM u t hu0 hui hui' hti)
  have hb : (up u t hu0 * b1) 1 0 = 0 := by
    simp [up, Matrix.mul_apply, Fin.sum_univ_two, hb1]
  have hact : (mkDat c χ).act (up u t hu0 * b1) z = (mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z) := by
    funext v; simp only [Dat.act, map_mul, mul_smul]
  have hj : (mkDat c χ).j (up u t hu0 * b1) * x = x' * (h2' * h1) := by
    change jF F (up u t hu0 * b1) * x = _
    rw [map_mul, mul_assoc, e1, ← mul_assoc, e2, mul_assoc]
  have hH' : h2' * h1 ∈ (mkDat c χ).H := Subgroup.mem_sup_left (mul_mem hh2 hh1)
  have hx'S : x' ∈ S := Finset.mem_biUnion.2 ⟨x1, hx1, hx'⟩
  refine ⟨up u t hu0 * b1, hb, ⟨x', hx'S, h2' * h1, hH', hj⟩, ?_⟩
  have e := ht_inv (mkDat c χ) h2 h3 _ hb z x
  rw [← e, hj, hact, ht01, hm _ hs _ _ hH'] at hz
  rw [hact]
  have hre : ∀ v, (((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.re =
      sg v u * (((mkDat c χ).act b1 z) v).1.re + sg v t := by
    intro v; rw [act_up]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have him : ∀ v, (((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im =
      sg v u * (((mkDat c χ).act b1 z) v).1.im := by
    intro v; rw [act_up]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hy : ∀ v v', |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im| ≤
      CU * |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v').1.im| := by
    intro v v'; rw [him, him]; exact hu v v'
  have hprod : c₀ ≤ (∏ v, |(((mkDat c χ).act (up u t hu0) ((mkDat c χ).act b1 z)) v).1.im|) * M :=
    hz.trans (mul_le_mul_of_nonneg_left (hMS x' hx'S) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
  intro v
  refine ⟨?_, low _ hCU hM0 hy hprod v, fun v' => ?_⟩
  · rw [hre]; exact (ht v).trans (le_max_right _ _)
  · exact (hy v v').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

end UpperTheory.Esk
end
end

