module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormSqNonnegGaussianTorus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CardChoiceLe
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Count
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

theorem c_le_DF (j : Fin nb) (hi : 1 ≤ (bs j).i) : (bs j).c ≤ DF bs := by
  unfold DF
  exact le_trans (Nat.le_mul_of_pos_left _ hi)
    (Finset.single_le_sum (f := fun j => (bs j).i * (bs j).c) (fun j _ => Nat.zero_le _) (Finset.mem_univ j))

theorem card_choice_le (r : ℕ) (hr : ∀ j, (bs j).i ≤ r) :
    Fintype.card (Choice bs) ≤ r ^ DF bs := by
  unfold DF
  rw [Fintype.card_pi, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
  intro j _
  rw [Fintype.card_fun, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin, pow_mul]
  exact Nat.pow_le_pow_left (le_trans (Nat.factorial_le_pow _) (Nat.pow_le_pow_left (hr j) _)) _

theorem prod_two_pow :
    ∏ p : (Σ j : Fin nb, Fin (bs j).i), (2 : ℝ) ^ (bs p.1).c = 2 ^ DF bs := by
  rw [Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  unfold DF
  congr 1
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem card_pos_le : Fintype.card (Σ j : Fin nb, Fin (bs j).i) ≤ DF bs := by
  rw [Fintype.card_sigma]
  unfold DF
  exact Finset.sum_le_sum (fun j _ => by rw [Fintype.card_fin]; exact Nat.le_mul_of_pos_right _ (bs j).hc)

theorem card_pos_pos (h : 1 ≤ DF bs) : 1 ≤ Fintype.card (Σ j : Fin nb, Fin (bs j).i) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  by_contra hc
  push_neg at hc
  have h0 : ∀ j, (bs j).i = 0 := by
    intro j
    have := Finset.single_le_sum (f := fun j => (bs j).i) (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  unfold DF at h
  simp [h0] at h

theorem prod_det_ge (d : ∀ j : Fin nb, ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hd : ∀ j, 1 ≤ (bs j).i → δ ≤ d j) (hd1 : ∀ j, (bs j).i = 0 → d j = 1) :
    δ ^ DF bs ≤ ∏ j, d j ^ (bs j).c := by
  unfold DF
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun j _ => pow_nonneg hδ0 _)
  intro j _
  by_cases hi : (bs j).i = 0
  · rw [hi, zero_mul, pow_zero, hd1 j hi, one_pow]
  · have hi1 : 1 ≤ (bs j).i := Nat.one_le_iff_ne_zero.mpr hi
    calc δ ^ ((bs j).i * (bs j).c) ≤ δ ^ (bs j).c :=
          pow_le_pow_of_le_one hδ0 hδ1 (Nat.le_mul_of_pos_left _ hi1)
      _ ≤ d j ^ (bs j).c := pow_le_pow_left₀ hδ0 (hd j hi1) _

end Count

section Data
variable [IsCMField E] (X : PT E) (bs : Fin nb → Block E n X.dim)

open Classical in
theorem block_data_all (hx : Ext.All) (hc : CharStatement) (ht : ColTorusStatement)
    (ha : ColAbelStatement) (P : Par X (DF bs)) (I : Submodule ℤ (Vsp X.dim)) (hI : IsSplit P I)
    (j : Fin nb) :
    ∃ (y : Fin (bs j).i → Vsp X.dim) (s : Fin (bs j).i → (Fin 1 → Vsp X.dim) → ℂ)
      (μ : Fin (bs j).i → ℂ),
      (∀ b, s b ∈ X.Sec P.q 1) ∧
      (∀ b (xs : Fin (bs j).c → Vsp X.dim), (∀ k, InPart (bs j).τ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 (s b) (bs j).c xs - μ b * ∏ k, Hf (xs k) (y b)‖ ≤ P.eps1 * ‖μ b‖) ∧
      (∀ b, P.K6⁻¹ * Real.exp (-(2 * Real.pi * Cchi (E := E) P.m * P.ph / P.q)) * X.l2 P.q (s b) ≤
        ‖μ b‖ ^ 2) ∧
      (∀ b, ‖y b‖ ≤ 2) ∧
      (2 : ℝ) ^ (-(X.r : ℝ) / 2) / 2 ≤
        ‖(Matrix.of fun a b => Hf (EuclideanSpace.single
          (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx X.dim) (1 : ℂ)) (y b)).det‖ ∧
      (∀ b, μ b ≠ 0) := by
  rcases Nat.eq_zero_or_pos (bs j).i with h0 | hpos
  · haveI : IsEmpty (Fin (bs j).i) := by rw [h0]; infer_instance
    refine ⟨isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, fun b => isEmptyElim b,
      isEmptyElim, isEmptyElim, ?_, isEmptyElim⟩
    rw [Matrix.det_isEmpty, norm_one]
    have h1 : (2 : ℝ) ^ (-(X.r : ℝ) / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
        have := Nat.cast_nonneg (α := ℝ) X.r; linarith)
    linarith
  · exact block_data hx hc ht ha X P I hI (bs j).τ (bs j).i (bs j).hi (bs j).c (c_le_DF bs j hpos)

end Data

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelC
section
namespace ReciprocityTheory.ChartRestriction.G.I2

section

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E}

theorem cab_emb_sep {σ τ : E →+* ℂ} (h : σ ≠ τ) : ∃ α : 𝓞 E, σ (α : E) ≠ τ (α : E) := by
  by_contra hc
  push Not at hc
  apply h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hc x)

omit [IsCMField E] in
theorem cab_conjugate_ne [_root_.NumberField.IsTotallyComplex E] (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ≠ σ := by
  intro h
  have hr : ComplexEmbedding.IsReal σ := ComplexEmbedding.isReal_iff.2 h
  have hc := IsTotallyComplex.isComplex (InfinitePlace.mk σ)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

theorem cab_actE_inPart {σ : E →+* ℂ} {v : Vsp X.dim} (hv : InPart σ v) (β : E) :
    actE β v = σ β • v := by
  ext j
  simp only [actE_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : j.1 = σ
  · rw [h]
  · rw [hv j h, mul_zero, mul_zero]

theorem cab_Hf_K (K : Submodule ℝ (Vsp X.dim)) (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    (v u : Vsp X.dim) (hu : u ∈ K) : Hf v u = ∑ j, Col.z K j u * Col.z K j v := by
  conv_lhs => rw [← Col.proj_one_of_mem hK hu]
  simp only [Col.p1, Col.Hf_sum_r, Col.Hf_smul_r]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hr : (starRingEnd ℂ) (Col.z K j u) = Col.z K j u := by
    apply Complex.conj_eq_iff_im.mpr
    exact hK u hu _ (Col.e_mem K j)
  rw [hr]; rfl

theorem cab_S_zero (K : Submodule ℝ (Vsp X.dim)) (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    (hst : ∀ (α : 𝓞 E) a, a ∈ K → act α a ∈ K) (σ : E →+* ℂ) (v : Vsp X.dim) (hv : InPart σ v) :
    Col.S K v = 0 := by
  obtain ⟨α, hα⟩ := cab_emb_sep (σ := σ) (τ := ComplexEmbedding.conjugate σ) (cab_conjugate_ne σ).symm
  set a : E := (α : E) with ha
  set b : E := IsCMField.complexConj E a with hb
  have hba : IsCMField.complexConj E b = a := by simp [hb]
  have hKa : ∀ u ∈ K, actE a u ∈ K := fun u hu => hst α u hu
  have hKb : ∀ u ∈ K, actE b u ∈ K := fun u hu =>
    hst (IsCMField.ringOfIntegersComplexConj E α) u hu
  have hσb : σ b = (starRingEnd ℂ) (σ a) := by
    simp [hb, IsCMField.complexEmbedding_complexConj]

  have hent : ∀ j k, Col.z K j (actE b (Col.e K k)) = Col.z K k (actE a (Col.e K j)) := by
    intro j k
    simp only [Col.z]
    rw [Hf_actE, hba, Col.Hf_swap (actE a (Col.e K j))]
    apply Complex.conj_eq_iff_im.mpr
    exact hK _ (hKa _ (Col.e_mem K j)) _ (Col.e_mem K k)
  have h1 : σ a * Col.S K v =
      ∑ k, ∑ j, Col.z K j (actE b (Col.e K k)) * Col.z K j v * Col.z K k v := by
    have : ∀ k, Col.z K k (actE a v) = ∑ j, Col.z K j (actE b (Col.e K k)) * Col.z K j v := by
      intro k
      simp only [Col.z]
      rw [Hf_actE, ← hb]
      exact cab_Hf_K K hK v _ (hKb _ (Col.e_mem K k))
    have h2 : ∀ k, Col.z K k (actE a v) = σ a * Col.z K k v := by
      intro k; simp only [Col.z]; rw [cab_actE_inPart hv, Col.Hf_smul_l]
    simp only [Col.S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, ← this k, h2 k]; ring
  have h3 : (starRingEnd ℂ) (σ a) * Col.S K v =
      ∑ j, ∑ k, Col.z K k (actE a (Col.e K j)) * Col.z K k v * Col.z K j v := by
    have : ∀ j, Col.z K j (actE b v) = ∑ k, Col.z K k (actE a (Col.e K j)) * Col.z K k v := by
      intro j
      simp only [Col.z]
      rw [Hf_actE, hba]
      exact cab_Hf_K K hK v _ (hKa _ (Col.e_mem K j))
    have h2 : ∀ j, Col.z K j (actE b v) = (starRingEnd ℂ) (σ a) * Col.z K j v := by
      intro j; simp only [Col.z]; rw [cab_actE_inPart hv, Col.Hf_smul_l, hσb]
    simp only [Col.S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← this j, h2 j]; ring
  have h4 : σ a * Col.S K v = (starRingEnd ℂ) (σ a) * Col.S K v := by
    rw [h1, h3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hent]; ring
  have hne : σ a - (starRingEnd ℂ) (σ a) ≠ 0 := by
    rw [sub_ne_zero]
    simpa [ComplexEmbedding.conjugate_coe_eq] using hα
  have h5 : (σ a - (starRingEnd ℂ) (σ a)) * Col.S K v = 0 := by rw [sub_mul, h4, sub_self]
  exact (mul_eq_zero.mp h5).resolve_left hne

end

end

section

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] {X : PT E}

def cabVP {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : Submodule ℂ (Vsp dim) where
  carrier := {v | InPart σ v}
  add_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

theorem cab_Hf_IR {I : Submodule ℤ (Vsp X.dim)} {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0) :
    ∀ a ∈ IR I, Hf ξ a = 0 := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact hξ x hx
  | zero => simp [Hf]
  | add x y _ _ hx hy => rw [Col.Hf_add_r, hx, hy, add_zero]
  | smul r x _ hx => rw [Col.Hf_rsmul_r, hx, mul_zero]

theorem cab_z_xi {I : Submodule ℤ (Vsp X.dim)} {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0)
    (k : Fin (Col.dK (IR I))) : Col.z (IR I) k ξ = 0 :=
  cab_Hf_IR hξ _ (Col.e_mem _ k)

theorem cab_Hf_wmap_xi {I : Submodule ℤ (Vsp X.dim)} (hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0)
    {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0) (x : Vsp X.dim) : Hf (Col.wmap (IR I) x) (Col.wmap (IR I) ξ) = Hf x ξ := by
  have hp1 : Col.p1 (IR I) ξ = 0 := by
    simp [Col.p1, cab_z_xi hξ]
  have hp2 : Col.p2 (IR I) ξ = ξ := by rw [Col.p2, hp1, sub_zero]
  rw [Col.Hf_wmap hK, hp2, Col.p2, Col.Hf_sub_l]
  have : Hf (Col.p1 (IR I) x) ξ = 0 := by
    simp only [Col.p1, Col.Hf_sum_l, Col.Hf_smul_l]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Col.Hf_swap, ← Col.z, cab_z_xi hξ, map_zero, mul_zero]
  rw [this, sub_zero]

theorem cab_norm_wmap_xi {I : Submodule ℤ (Vsp X.dim)} (hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0)
    {ξ : Vsp X.dim} (hξ : ∀ a ∈ I, Hf ξ a = 0) :
    ‖Col.wmap (IR I) ξ‖ = ‖ξ‖ := by
  have hp1 : Col.p1 (IR I) ξ = 0 := by
    simp [Col.p1, cab_z_xi hξ]
  rw [Col.norm_wmap hK, Col.p2, hp1, sub_zero]

theorem cab_main {I : Submodule ℤ (Vsp X.dim)} (hK : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0)
    {c : ℕ} (σ : E →+* ℂ) {ξ : Vsp X.dim}
    (hξ : ∀ a ∈ I, Hf ξ a = 0) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ)
    (hβ : Differentiable ℂ β) {inst : DecidableEq (Fin (Col.gB (IR I)))}
    (hjet : ∀ α : Fin (Col.gB (IR I)) →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => @EuclideanSpace.single _ ℂ _ inst i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => @EuclideanSpace.single _ ℂ _ inst i 1)
          (fun t : EuclideanSpace ℂ (Fin (Col.gB (IR I))) =>
            MvPolynomial.eval (fun i => t i) (cabPoly (Col.wmap (IR I) ξ) c)) 0)
    (F0 : Vsp X.dim → ℂ) (hF0d : Differentiable ℂ F0)
    (hF0 : ∀ v, InPart σ v → F0 v = β (Col.wmap (IR I) v))
    (xs : Fin c → Vsp X.dim) (hxs : ∀ k, InPart σ (xs k)) :
    iteratedFDeriv ℂ c F0 0 xs = (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ := by
  set W := Col.wmap (IR I)
  set η := W ξ
  have hg : Differentiable ℂ (β ∘ W) := hβ.comp W.differentiable
  have h1 : iteratedFDeriv ℂ c F0 0 xs = iteratedFDeriv ℂ c (β ∘ W) 0 xs :=
    cab_restrict (cabVP σ) (contDiff_of_differentiable_fd hF0d c) (contDiff_of_differentiable_fd hg c)
      (fun v hv => hF0 v hv) xs hxs
  have hβc : ContDiff ℂ (⊤ : WithTop ℕ∞) β := cab_contDiff_top hβ
  have h2 : iteratedFDeriv ℂ c (β ∘ W) 0 xs = iteratedFDeriv ℂ c β 0 (fun k => W (xs k)) := by
    rw [W.iteratedFDeriv_comp_right (hβc.of_le le_top) 0 (by exact_mod_cast le_top)]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  let ℓ : EuclideanSpace ℂ (Fin (Col.gB (IR I))) →L[ℂ] ℂ := innerSL ℂ η
  have hℓ : ∀ t, ℓ t = Hf t η := by
    intro t; rw [Col.Hf_eq_inner]; rfl
  have hP : (fun t : EuclideanSpace ℂ (Fin (Col.gB (IR I))) =>
      MvPolynomial.eval (fun i => t i) (cabPoly η c)) = fun t => (ℓ t) ^ c := by
    funext t; rw [cabPoly_eval, hℓ]
  have hPd : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun t : EuclideanSpace ℂ (Fin (Col.gB (IR I))) =>
      MvPolynomial.eval (fun i => t i) (cabPoly η c)) := by
    rw [hP]; exact cab_contDiff_top (ℓ.differentiable.pow c)
  let _ := inst
  have h3 := cab_jet_eq hβc hPd hjet
  rw [h1, h2, h3, hP, cab_iter_pow]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hℓ]; exact cab_Hf_wmap_xi hK hξ (xs k)

end

end

section

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E] {X : PT E}

theorem cab_IR_stable {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) :
    ∀ (α : 𝓞 E) a, a ∈ IR I → act α a ∈ IR I := by
  intro α a ha
  rw [act_eq_actE]
  exact actE_mem_of_span (α : E) (I : Set (Vsp X.dim)) (IR I)
    (fun v hv => Submodule.subset_span (hI.stable α v hv)) a ha

theorem cab_z_diff (K : Submodule ℝ (Vsp X.dim)) (k : Fin (Col.dK K)) :
    Differentiable ℂ (fun v => Col.z K k v) := by
  have : (fun v => Col.z K k v) = fun v => innerSL ℂ (Col.e K k) v := by
    funext v; simp only [Col.z]; rw [Col.Hf_eq_inner]; rfl
  rw [this]; exact (innerSL ℂ (Col.e K k)).differentiable

theorem differentiable_zeroModeLift (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ)
    (hβ : Differentiable ℂ β) : Differentiable ℂ (Col.F0 I q β) := by
  have hS : Differentiable ℂ (fun v => Col.S (IR I) v) := by
    have : (fun v => Col.S (IR I) v) = fun v => ∑ k, (Col.z (IR I) k v) ^ 2 := rfl
    rw [this]
    exact Differentiable.fun_sum fun k _ => (cab_z_diff _ k).pow 2
  have : Col.F0 I q β = fun v => cexp ((q * Real.pi / 2 : ℂ) * Col.S (IR I) v) * β (Col.wmap (IR I) v) := rfl
  rw [this]
  exact ((hS.const_mul _).cexp).mul (hβ.comp (Col.wmap (IR I)).differentiable)

theorem zeroModeLift_on_part [IsCMField E] {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I)
    (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (σ : E →+* ℂ) (v : Vsp X.dim)
    (hv : InPart σ v) : Col.F0 I q β v = β (Col.wmap (IR I) v) := by
  have h0 := cab_S_zero (IR I) (Col.hK_of hI) (cab_IR_stable hI) σ v hv
  simp only [Col.F0, h0, mul_zero, Complex.exp_zero, one_mul]

end

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

theorem lemmaN (_hd : DimStatement) : NStatement := thetaBasis_holds

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PrjMemOfSpan
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def Zs {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) : Submodule ℝ (Vsp dim) :=
  Submodule.span ℝ {x | ∃ α : 𝓞 E, ∃ y ∈ Xg L I, ‖y‖ ≤ μ ∧ x = act α y}

lemma Zs_mono {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ μ' : ℝ} (h : μ ≤ μ') :
    Zs L I μ ≤ Zs L I μ' := Submodule.span_mono fun _ ⟨α, y, hy, hyμ, hx⟩ => ⟨α, y, hy, hyμ.trans h, hx⟩

lemma Zs_self {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ : ℝ} {y : Vsp dim}
    (hy : y ∈ Xg L I) (hμ : ‖y‖ ≤ μ) : y ∈ Zs L I μ := by
  refine Submodule.subset_span ⟨1, y, hy, hμ, ?_⟩
  ext i
  simp [act]

private lemma act_add_lemma {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (x y : Vsp dim) :
    act β (x + y) = act β x + act β y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_smul_lemma_2 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (r : ℝ) (x : Vsp dim) :
    act β (r • x) = r • act β x := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_zero_lemma_4 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) : act β (0 : Vsp dim) = 0 := by
  ext i
  simp [act]

private lemma act_mul_lemma_5 {dim : (E →+* ℂ) → ℕ} (β α : 𝓞 E) (y : Vsp dim) :
    act β (act α y) = act (β * α) y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_span_lemma_3 {dim : (E →+* ℂ) → ℕ} (S : Set (Vsp dim)) (β : 𝓞 E)
    (hS : ∀ y ∈ S, act β y ∈ Submodule.span ℝ S) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : act β a ∈ Submodule.span ℝ S := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [act_zero_lemma_4]; exact zero_mem _
  | add x y _ _ hx hy => rw [act_add_lemma]; exact add_mem hx hy
  | smul r x _ hx => rw [act_smul_lemma_2]; exact Submodule.smul_mem _ r hx

lemma Zs_act {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) (β : 𝓞 E)
    {x : Vsp dim} (hx : x ∈ Zs L I μ) : act β x ∈ Zs L I μ := by
  refine act_span_lemma_3 _ β ?_ hx
  rintro _ ⟨α, y, hy, hyμ, rfl⟩
  exact Submodule.subset_span ⟨β * α, y, hy, hyμ, act_mul_lemma_5 β α y⟩

lemma Zs_IR {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (μ : ℝ) : Zs L I μ ≤ IR I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨α, y, hy, -, rfl⟩
  obtain ⟨x, -, hu⟩ : ∃ x ∈ L, IsU I x y := hy
  exact act_span_lemma_3 _ α (fun z hz => Submodule.subset_span (hIs α z hz)) hu.1

lemma prj_rsmul {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (r : ℝ) (x : Vsp dim) :
    prj σ (r • x) = r • prj σ x := by
  simp only [prj]
  exact LinearMap.map_smul_of_tower _ r x

private lemma prj_add_lemma_6 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (x y : Vsp dim) :
    prj σ (x + y) = prj σ x + prj σ y := by
  simp only [prj]
  exact map_add _ x y

private lemma prj_zero_lemma_7 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : prj σ (0 : Vsp dim) = 0 := by
  simp only [prj]
  exact map_zero _

lemma prj_mem_of_span {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim))
    (S : Set (Vsp dim)) (hS : ∀ y ∈ S, prj σ y ∈ W) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : prj σ a ∈ W := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [prj_zero_lemma_7]; exact zero_mem _
  | add x y _ _ hx hy => rw [prj_add_lemma_6]; exact add_mem hx hy
  | smul r x _ hx => rw [prj_rsmul]; exact W.smul_of_tower_mem r hx

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

