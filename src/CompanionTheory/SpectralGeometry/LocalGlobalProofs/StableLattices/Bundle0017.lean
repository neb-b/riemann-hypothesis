module

public import Mathlib
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExpMemUJ
section
open Matrix Finset Filter Topology Set

noncomputable section

namespace GlobalTheory.CompanionTheory.DSStabLink

open PI.UpqRep CompanionTheory.D.DSIC

theorem flow_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (T : ℝ → (H →L[ℂ] H)) (h0 : ∀ v, T 0 v = v)
    (hadd : ∀ s t v, T (s + t) v = T s (T t v)) (hiso : ∀ t v, ‖T t v‖ = ‖v‖)
    (hder : ∀ w ∈ W, ∃ z ∈ W, HasDerivAt (fun t => T t w) z 0) (u : H) (hu : u ∈ W) :
    T 1 u ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have hQn : ∀ x, ‖Q x‖ ≤ ‖x‖ := fun x => Submodule.norm_starProjection_apply_le _ x
  have hcont : Continuous fun t => T t u := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨z, -, hz⟩ := hder u hu
    have h1 : ContinuousAt (fun s : ℝ => T (s - t) u) t := by
      have h2 : ContinuousAt (fun s : ℝ => s - t) t := by fun_prop
      exact ContinuousAt.comp_of_eq (g := fun t => T t u) hz.continuousAt h2 (by simp)
    have h3 : ContinuousAt (fun s : ℝ => T t (T (s - t) u)) t :=
      (T t).continuous.continuousAt.comp h1
    convert h3 using 2 with s
    rw [← hadd]; simp
  have key : ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → ‖Q (T x u)‖ ≤ 0 := by
    refine image_le_of_liminf_slope_right_le_deriv_boundary (f := fun t => ‖Q (T t u)‖)
      (B := fun _ => 0) (B' := fun _ => 0) ?_ ?_ continuousOn_const
      (fun x _ => hasDerivWithinAt_const _ _ _) ?_
    · exact ((Q.continuous.comp hcont).norm).continuousOn
    · simp [h0, hQW u hu]
    · intro x _ r hr
      set w := T x u - Q (T x u) with hw
      obtain ⟨z, hzW, hz⟩ := hder w (hQs _)
      have hg : HasDerivAt (fun t => Q (T t w)) 0 0 := by
        have := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
        simpa [hQW z hzW, Function.comp_def] using this
      have hg2 : HasDerivAt (fun s : ℝ => Q (T (s - x) w)) 0 x := by
        have h2 : HasDerivAt (fun s : ℝ => s - x) 1 x := (hasDerivAt_id x).sub_const x
        have := HasDerivAt.scomp_of_eq (g₁ := fun t => Q (T t w)) x hg h2 (by simp)
        simpa [Function.comp_def] using this
      have hsl := (hasDerivAt_iff_tendsto_slope.1 hg2).norm
      rw [norm_zero] at hsl
      have hev : ∀ᶠ s in 𝓝[>] x, ‖slope (fun s : ℝ => Q (T (s - x) w)) x s‖ < r :=
        (hsl.eventually (gt_mem_nhds hr)).filter_mono (nhdsWithin_mono _ fun s hs => ne_of_gt hs)
      refine (hev.and self_mem_nhdsWithin).frequently.mono ?_
      rintro s ⟨hs, hsx⟩
      have hpos : 0 < s - x := sub_pos.2 hsx
      refine lt_of_le_of_lt ?_ hs
      rw [slope_def_field, slope_def_module, norm_smul, sub_self, h0, hQW w (hQs _), sub_zero,
        Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hpos).le
      have e : Q (T s u) = Q (T (s - x) w) + Q (T (s - x) (Q (T x u))) := by
        rw [← map_add (f := _), ← map_add (f := _), hw, sub_add_cancel, ← hadd, sub_add_cancel]
      have e2 : ‖Q (T (s - x) (Q (T x u)))‖ ≤ ‖Q (T x u)‖ := (hQn _).trans (hiso _ _).le
      have e3 := norm_add_le (Q (T (s - x) w)) (Q (T (s - x) (Q (T x u))))
      rw [← e] at e3
      linarith
  have h1 := norm_le_zero_iff.1 (key (x := 1) ⟨zero_le_one, le_rfl⟩)
  simpa [h1] using hQs (T 1 u)

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (c : ℝ → H) (z : H) (hc : ∀ t, c t ∈ W) (hz : HasDerivAt c z 0) :
    z ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have h1 : HasDerivAt (fun t => Q (c t)) (Q z) 0 :=
    (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
  have h2 : (fun t => Q (c t)) = fun _ => 0 := funext fun t => hQW _ (hc t)
  rw [h2] at h1
  have h3 : Q z = 0 := h1.unique (hasDerivAt_const _ _)
  simpa [h3] using hQs z

variable {n : ℕ}

theorem inK_iff (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ (∀ c d, ε c ≠ ε d → X c d = 0) ∧ ∀ c d, star (X d c) = -X c d := by
  unfold inK inG Jm
  simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Matrix.zero_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ∀ c d, ε c ≠ ε d → X c d = 0 := by
      intro c d h
      have := h2 c d
      cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this <;>
        first | linear_combination this / 2 | linear_combination -this / 2
    refine ⟨h3, fun c d => ?_⟩
    have := h1 c d
    by_cases h : ε c = ε d
    · cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this ⊢ <;>
        first | linear_combination this | linear_combination -this
    · simp [h3 c d h, h3 d c (Ne.symm h)]
  · rintro ⟨h1, h2⟩
    constructor
    · intro c d
      by_cases h : ε c = ε d
      · rw [h2, h]; ring
      · simp [h1 c d h, h1 d c (Ne.symm h)]
    · intro c d
      by_cases h : ε c = ε d
      · rw [h]; ring
      · simp [h1 c d h]

theorem inK_smul (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  rw [inK_iff] at hX ⊢
  refine ⟨fun c d h => by simp [hX.1 c d h], fun c d => ?_⟩
  have := hX.2 c d
  simp only [Matrix.smul_apply, smul_eq_mul, star_mul', this]
  simp

theorem exp_mem_K (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε :=
  (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (inK_smul ε hX t)

theorem exp_mem_UJ (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε :=
  Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t

theorem stabLink : KExp → StabLink := by
  intro hK n ε H _ _ σ S E hσ hS U hU
  constructor
  · intro hst g hg v hv
    obtain ⟨X, hX, rfl⟩ := hK n ε g hg
    have := flow_mem (U.map S.subtype) (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)))
      ?_ ?_ ?_ ?_ v hv
    · simpa using this
    · intro v
      simp [hσ.1.1]
    · intro s t v
      have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
      simp only [Complex.ofReal_add, add_smul]
      rw [Matrix.exp_add_of_commute _ _ hc,
        hσ.1.2 _ (exp_mem_UJ ε hX.1 s) _ (exp_mem_UJ ε hX.1 t)]
      rfl
    · intro t v
      exact hσ.2.1 _ (exp_mem_UJ ε hX.1 t) v
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨_, ?_, hS.real X hX.1 w⟩
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      by_cases h : ε a = ε b
      · exact Submodule.smul_mem _ _ ⟨_, hst a b h w hw, rfl⟩
      · simp [((inK_iff ε X).1 hX).1 a b h]
  · intro hst a b hab v hv
    have hL : ∀ X, inK ε X → ∑ c, ∑ d, X c d • (E c d v : H) ∈ U.map S.subtype := fun X hX =>
      deriv_mem _ _ _ (fun t => hst _ (exp_mem_K ε hX t) _ ⟨v, hv, rfl⟩) (hS.real X hX.1 v)
    have hs : ∀ (p q : Fin n) (z : ℂ),
        ∑ c, ∑ d, (Matrix.single p q z) c d • (E c d v : H) = z • (E p q v : H) := by
      intro p q z
      simp [Matrix.single_apply, ite_and]
    have hoff : ∀ (p q : Fin n) (z : ℂ), ε p = ε q → ∀ c d, ε c ≠ ε d →
        Matrix.single p q z c d = 0 := by
      intro p q z h c d hcd
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hcd h
    have hZ : ∀ z : ℂ, z • (E a b v : H) - star z • (E b a v : H) ∈ U.map S.subtype := by
      intro z
      have hin : inK ε (Matrix.single a b z - Matrix.single b a (star z)) := by
        rw [inK_iff]
        refine ⟨fun c d h => by simp [hoff a b z hab c d h, hoff b a _ hab.symm c d h], fun c d => ?_⟩
        simp only [Matrix.sub_apply, Matrix.single_apply, star_sub, apply_ite star, star_star,
          star_zero, neg_sub, and_comm]
      have := hL _ hin
      simpa only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hs] using this
    have h1 := hZ 1
    have h2 := hZ Complex.I
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ (1 / 2 : ℂ) h1)
      (Submodule.smul_mem _ (-Complex.I / 2 : ℂ) h2)
    have e : (1 / 2 : ℂ) • ((1 : ℂ) • (E a b v : H) - star (1 : ℂ) • (E b a v : H)) +
        (-Complex.I / 2 : ℂ) • (Complex.I • (E a b v : H) - star Complex.I • (E b a v : H)) =
        (E a b v : H) := by
      simp only [star_one, Complex.star_def, Complex.conj_I]
      match_scalars
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
    rw [e] at h3
    obtain ⟨y, hy, hye⟩ := h3
    have : y = E a b v := Subtype.ext hye
    exact this ▸ hy

end GlobalTheory.CompanionTheory.DSStabLink
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExpMul
section
open Matrix Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.WtLinkPf

open PI.UpqRep

variable {n : ℕ}

def tor (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

lemma tor_add (θ η : Fin n → ℝ) : tor (θ + η) = tor θ * tor η := by
  unfold tor
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  ring

lemma tor_zero : tor (0 : Fin n → ℝ) = 1 := by
  unfold tor
  simp

lemma star_exp_mul (x : ℝ) : star (Complex.exp ((x : ℂ) * Complex.I)) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

lemma tor_mem_UJ (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ UJset ε := by
  show (tor θ).conjTranspose * PI.UpqRep.Jm ε * tor θ = PI.UpqRep.Jm ε
  unfold tor PI.UpqRep.Jm
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [Pi.star_apply, mul_right_comm, star_exp_mul, one_mul]

lemma tor_mem_K (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ Kset ε := by
  show tor θ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ tor θ * PI.UpqRep.Jm ε = PI.UpqRep.Jm ε * tor θ
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    unfold tor
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      show (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun _ => 1) from Matrix.diagonal_one.symm]
    congr 1
    funext a
    rw [Pi.star_apply]
    exact star_exp_mul (θ a)
  · unfold tor PI.UpqRep.Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

lemma diag_inG (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inG ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  show (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I).conjTranspose * PI.UpqRep.Jm ε +
      PI.UpqRep.Jm ε * Matrix.diagonal (fun a => (θ a : ℂ) * Complex.I) = 0
  unfold PI.UpqRep.Jm
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add, ← Matrix.diagonal_zero]
  congr 1
  funext a
  rw [Pi.star_apply, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma exp_diag (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) = tor (t • θ) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  unfold tor
  congr 1
  funext a
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma deriv_zero {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ S} (h : CompanionTheory.D.DSIC.IsSmMod ε σ S E) (θ : Fin n → ℝ) (v : S) :
    HasDerivAt (fun t : ℝ => σ (tor (t • θ)) v) (∑ a, ((θ a : ℂ) * Complex.I) • (E a a v : H)) 0 := by
  have h1 := h.real (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) (diag_inG ε θ) v
  simp only [exp_diag] at h1
  convert h1 using 1
  simp [Matrix.diagonal_apply]

lemma hasDerivAt_exp_mul (c : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) (Complex.exp ((s : ℂ) * c) * c) s := by
  have := ((hasDerivAt_id s).ofReal_comp.mul_const c).cexp
  simpa using this

lemma one_param (φ : ℝ → (H →L[ℂ] H)) (hadd : ∀ s t, φ (s + t) = φ s * φ t) (h0 : φ 0 = 1) (v : H) (c : ℂ)
    (hd : HasDerivAt (fun t => φ t v) (c • v) 0) : φ 1 v = Complex.exp c • v := by
  have hder : ∀ s : ℝ, HasDerivAt (fun t => φ t v) (c • φ s v) s := by
    intro s
    have h1 : HasDerivAt (fun u => φ s (φ u v)) (φ s (c • v)) 0 := by
      have := ((φ s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun u => φ s (φ u v)) (φ s (c • v)) (s - s) := by
      rwa [sub_self]
    have h3 := HasDerivAt.comp_sub_const s s h2
    rw [map_smul] at h3
    convert h3 using 1
    funext t
    show φ t v = φ s (φ (t - s) v)
    rw [← ContinuousLinearMap.mul_apply, ← hadd, show s + (t - s) = t by ring]
  have hg : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • φ t v) 0 s := by
    intro s
    have := (hasDerivAt_exp_mul (-c) s).smul (hder s)
    convert (preTransparency := .reducible) this using 1
    · funext t
      rfl
    · rw [smul_smul, ← add_smul]
      simp
  have hdiff : Differentiable ℝ (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • φ t v) :=
    fun s => (hg s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (hg s).deriv) 1 0
  have hfinal : Complex.exp (-c) • φ 1 v = v := by
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, Complex.exp_zero, one_smul, h0,
      ContinuousLinearMap.one_apply] at hconst
    exact hconst
  calc φ 1 v = Complex.exp c • (Complex.exp (-c) • φ 1 v) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp c • v := by rw [hfinal]

end

theorem wtLink : CompanionTheory.D.DSIC.WtLink := by
  intro n ε H _ _ σ S E hrep h μ v
  have hG : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, σ (a * b) = σ a * σ b := by
    intro a ha b hb
    rw [ContinuousLinearMap.mul_def]
    exact hrep.1.2 a ha b hb
  have h1 : σ 1 = 1 := hrep.1.1
  constructor
  · intro hw θ _
    have hw' : ∀ a, E a a v = (μ a : ℂ) • v := hw
    let φ : ℝ → (H →L[ℂ] H) := fun t => σ (tor (t • θ))
    have hadd : ∀ s t, φ (s + t) = φ s * φ t := by
      intro s t
      show σ (tor ((s + t) • θ)) = σ (tor (s • θ)) * σ (tor (t • θ))
      rw [add_smul, tor_add]
      exact hG _ (tor_mem_UJ ε _) _ (tor_mem_UJ ε _)
    have hz : φ 0 = 1 := by
      show σ (tor ((0 : ℝ) • θ)) = 1
      rw [zero_smul, tor_zero]
      exact h1
    have hd : HasDerivAt (fun t => φ t (v : H))
        ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H)) 0 := by
      have := deriv_zero h θ v
      convert this using 1
      simp only [hw', Submodule.coe_smul, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    have key := one_param φ hadd hz (v : H) _ hd
    show σ (tor θ) (v : H) = _
    rw [show tor θ = tor ((1 : ℝ) • θ) by rw [one_smul]]
    exact key
  · intro hK a
    apply Subtype.ext
    rw [Submodule.coe_smul]
    let θ : Fin n → ℝ := Pi.single a 1
    have hf : (fun t : ℝ => σ (tor (t • θ)) (v : H)) =
        fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
      funext t
      have ht := hK (t • θ) (tor_mem_K ε _)
      rw [show tor (t • θ) = Matrix.diagonal (fun b => Complex.exp ((((t • θ) b : ℝ) : ℂ) * Complex.I)) from rfl, ht]
      congr 2
      simp [θ, Pi.single_apply]
      try (push_cast; ring)
    have d1 := deriv_zero h θ v
    rw [hf] at d1
    have d2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H))
        (((μ a : ℂ) * Complex.I) • (v : H)) 0 := by
      have := (hasDerivAt_exp_mul ((μ a : ℂ) * Complex.I) 0).smul_const (v : H)
      simpa using this
    have hu := d1.unique d2
    have hsum : ∑ b, ((θ b : ℂ) * Complex.I) • (E b b v : H) = Complex.I • (E a a v : H) := by
      rw [Finset.sum_eq_single a]
      · simp [θ]
      · intro b _ hb
        simp [θ, Pi.single_apply, hb]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [hsum] at hu
    calc (E a a v : H) = (-Complex.I * Complex.I) • (E a a v : H) := by
          rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
      _ = (-Complex.I) • (Complex.I • (E a a v : H)) := by rw [smul_smul]
      _ = (-Complex.I) • (((μ a : ℂ) * Complex.I) • (v : H)) := by rw [hu]
      _ = (μ a : ℂ) • (v : H) := by
          rw [smul_smul]
          congr 1
          rw [show -Complex.I * ((μ a : ℂ) * Complex.I) = (μ a : ℂ) * -(Complex.I * Complex.I) by ring,
            Complex.I_mul_I, neg_neg, mul_one]

end GlobalTheory.CompanionTheory.WtLinkPf
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KsetSubsetUjset
section
open Matrix

namespace GlobalTheory.CompanionTheory.DSKType

open CompanionTheory.D.DSIC PI.UpqRep

theorem kset_subset_ujset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨h1, h2⟩ := hg
  have h3 : gᴴ * g = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.1 h1)
  show inUJ ε g
  unfold inUJ
  rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem typeOfHW (hL : LowSpan) (hS : StabLink) (hW : WtLink) : TypeOfHW := by
  intro n ε H _ _ σ S E hσ hM μ x hx0 hfin hhw
  obtain ⟨S₀, hfd, hxS, hst⟩ := hfin
  have hinj : Function.Injective S.subtype := S.injective_subtype
  have := hfd
  have hU : FiniteDimensional ℂ (S₀.comap S.subtype) := by
    refine FiniteDimensional.of_injective
      (LinearMap.codRestrict S₀ (S.subtype ∘ₗ (S₀.comap S.subtype).subtype) (fun y => y.2)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : S₀ => (y : H)) hab
  have hUst : KStab ε E (S₀.comap S.subtype) := by
    refine (hS n ε H σ S E hσ hM _ hU).2 ?_
    rintro g hg _ ⟨v, hv, rfl⟩
    exact ⟨⟨σ g v, hM.stab g (kset_subset_ujset hg) v v.2⟩, hst g hg v hv, rfl⟩
  have hrel : KRel ε E := fun a b c d _ _ => hM.gl a b c d
  have hun : KUnit ε E := by
    intro a b hab y z
    have := hM.unit a b y z
    simpa [Formalism.REAL.sgn, hab] using this
  obtain ⟨L, hLU, hxL, hLst, hirr, hdom, -⟩ := hL n ε S E μ x _ hrel hun hx0 hhw hU hUst hxS
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLU
  refine ⟨L.map S.subtype, inferInstance, (hS n ε H σ S E hσ hM L hLfd).1 hLst, ?_, ?_, ?_⟩
  · intro S' hle hS'
    have hle' : S'.comap S.subtype ≤ L := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := hle hy
      rwa [← hinj hzy]
    have hmap : (S'.comap S.subtype).map S.subtype = S' := by
      apply Submodule.map_comap_eq_of_le
      exact hle.trans LinearMap.map_le_range
    have hst' : KStab ε E (S'.comap S.subtype) := by
      refine (hS n ε H σ S E hσ hM _ (Submodule.finiteDimensional_of_le hle')).2 ?_
      rwa [hmap]
    rcases hirr _ hle' hst' with h | h
    · left; rw [← hmap, h, Submodule.map_bot]
    · right; rw [← hmap, h]
  · exact ⟨x, ⟨x, hxL, rfl⟩, fun h => hx0 (Subtype.ext h), (hW n ε H σ S E hσ hM μ x).1 hhw.1⟩
  · rintro ν _ ⟨v, hv, rfl⟩ hv0 hwt
    exact hdom ν v hv (fun h => hv0 (by rw [h]; rfl)) ((hW n ε H σ S E hσ hM ν v).2 hwt)

end GlobalTheory.CompanionTheory.DSKType
end

