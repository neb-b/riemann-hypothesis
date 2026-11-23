module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AevalSingleZero
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem UpperTheory.ConvolutionTheory.FX.aeval_single_zero {ι ι' : Type} (q : ι → MvPolynomial ι' ℂ)
    (p : MvPolynomial ι ℂ) :
    aeval (fun i => (AddMonoidAlgebra.single 0 (q i) : EP ι')) p
      = (AddMonoidAlgebra.single 0 (aeval q p) : EP ι') := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, aeval_C]
    rfl
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr, AddMonoidAlgebra.single_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]

private theorem UpperTheory.ConvolutionTheory.FX.lin_delta {ι ι' : Type} [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (i : ι) :
    lin (fun j => if δ i = j then (1 : ℝ) else 0) = (X (δ i) : MvPolynomial ι' ℂ) := by
  unfold lin
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem UpperTheory.ConvolutionTheory.FX.lin_push {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) :
    lin (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0)) = rename δ (lin v) := by
  unfold lin
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, map_mul, rename_C, rename_X,
    Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (δ i)]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem UpperTheory.ConvolutionTheory.FX.ren_single {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι'] (δ : ι → ι')
    (v : ι → ℝ) (p : MvPolynomial ι ℂ) :
    ren δ (AddMonoidAlgebra.single v p : EP ι) =
      (AddMonoidAlgebra.single (Matrix.vecMul v (Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0))
        (rename δ p) : EP ι') := by
  have h1 : (fun i => (C ((0 : ι → ℂ) i) + lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i) :
      MvPolynomial ι' ℂ)) = X ∘ δ := by
    funext i
    have := UpperTheory.ConvolutionTheory.FX.lin_delta δ i
    simp only [Pi.zero_apply, map_zero, zero_add, Function.comp]
    exact this
  unfold ren aff lift
  rw [AddMonoidAlgebra.liftNCRingHom_single]
  change aeval (fun i => (AddMonoidAlgebra.single 0 (C ((0 : ι → ℂ) i) +
      lin ((Matrix.of fun i j => if δ i = j then (1 : ℝ) else 0) i)) : EP ι')) p *
    (AddMonoidAlgebra.single (Matrix.vecMul v _) (C (expChar 0 (Multiplicative.ofAdd v))) : EP ι') = _
  rw [UpperTheory.ConvolutionTheory.FX.aeval_single_zero, h1, AddMonoidAlgebra.single_mul_single, zero_add]
  have h2 : expChar (0 : ι → ℂ) (Multiplicative.ofAdd v) = 1 := by simp [expChar]
  rw [h2, map_one, mul_one, rename_eq_aeval]

theorem UpperTheory.ConvolutionTheory.FX.piece_ren :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (δ : ι → ι') (k : ℕ), piece k (ren δ f) = rename δ (piece k f) := by
  intro ι _ f ι' _ _ δ k
  obtain ⟨ha, h0, hs⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι k
  obtain ⟨ha', h0', hs'⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι' k
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, h0, h0', map_zero]
  | add f g hf hg => rw [map_add (f := _), ha, ha', map_add (f := _), hf, hg]
  | single v p =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [UpperTheory.ConvolutionTheory.FX.ren_single, hs, hs', map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, map_pow, rename_C, UpperTheory.ConvolutionTheory.FX.lin_push, rename_homogeneousComponent]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.HasSumSingle
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem hasSum_comp {ι : Type} (p : MvPolynomial ι ℂ) (Λ : ι → ℂ) :
    HasSum (fun k => eval Λ (homogeneousComponent k p)) (eval Λ p) ∧
      Summable (fun k => ‖eval Λ (homogeneousComponent k p)‖) := by
  have h0 : ∀ k ∉ Finset.range (p.totalDegree + 1), eval Λ (homogeneousComponent k p) = 0 := by
    intro k hk
    rw [homogeneousComponent_eq_zero k p (by simpa using hk), map_zero]
  refine ⟨?_, summable_of_ne_finset_zero (s := Finset.range (p.totalDegree + 1))
    fun k hk => by rw [h0 k hk, norm_zero]⟩
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) h0
  rwa [← map_sum, sum_homogeneousComponent] at h

private theorem hasSum_single' {ι : Type} [Fintype ι] (v : ι → ℝ) (p : MvPolynomial ι ℂ) (Λ : ι → ℂ) :
    HasSum (fun k => ∑ b ∈ Finset.range (k + 1),
      ((b.factorial : ℂ)⁻¹ * eval Λ (lin v) ^ b) * eval Λ (homogeneousComponent (k - b) p))
      (Complex.exp (eval Λ (lin v)) * eval Λ p) := by
  obtain ⟨h1, h2⟩ := hasSum_comp p Λ
  set z := eval Λ (lin v)
  have e1 : HasSum (fun b : ℕ => (b.factorial : ℂ)⁻¹ * z ^ b) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp z
  have e2 : Summable (fun b : ℕ => ‖(b.factorial : ℂ)⁻¹ * z ^ b‖) := e1.summable.norm
  have s := (summable_norm_sum_mul_range_of_summable_norm e2 h2).of_norm
  have t := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm e2 h2
  rw [e1.tsum_eq, h1.tsum_eq] at t
  rw [t]
  exact s.hasSum

theorem UpperTheory.ConvolutionTheory.FX.piece_sum :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (Λ : ι → ℂ), HasSum (fun k => eval Λ (piece k f)) (ev Λ f) := by
  intro ι _ f Λ
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
    simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.1, map_zero]
    exact hasSum_zero
  | add f g hf hg =>
    simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).1 f g, map_add (f := _)]
    exact hf.add hg
  | single v p =>
    have hv : ev Λ (AddMonoidAlgebra.single v p : EP ι) = Complex.exp (eval Λ (lin v)) * eval Λ p := by
      simp [ev, PositivityTheory.Rg.Fx.lift, expChar, lin, mul_comm, aeval_eq_eval]
    rw [hv]
    convert hasSum_single' v p Λ using 2 with k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.2 v p, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, map_pow, eval_C]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.IntMvPolynomialCoeffAbsSumAddLe
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem weightAbsEntrySum_nonneg {ι : Type} (p : MvPolynomial ι ℂ) : 0 ≤ l1 p := Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem intMvPolynomialCoeffAbsSum_add_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p + q) ≤ l1 p + l1 q := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).1

private theorem intMvPolynomialCoeffAbsSum_mul_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p * q) ≤ l1 p * l1 q := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).2.1

private theorem intMvPolynomialCoeffAbsSum_sum_le {ι κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι ℂ) : l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (intMvPolynomialCoeffAbsSum_add_le _ _).trans (by linarith)

private theorem intMvPolynomialCoeffAbsSum_pow_le {ι : Type} (p : MvPolynomial ι ℂ) (b : ℕ) : l1 (p ^ b) ≤ l1 p ^ b := by
  induction b with
  | zero =>
    have := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι 0 0).2.2.2.1 (0 : ι →₀ ℕ) 1
    simp only [monomial_zero', C_1, norm_one] at this
    simpa [l1] using this.le
  | succ b ih => rw [pow_succ, pow_succ]; exact (intMvPolynomialCoeffAbsSum_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (weightAbsEntrySum_nonneg _))

theorem UpperTheory.ConvolutionTheory.FX.piece_size :
    ∀ (ι : Type) [Fintype ι] (f : EP ι), ∃ K : ℝ, ∀ k, l1 (piece k f) ≤ K ^ (k + 1) / k.factorial := by
  intro ι _ f
  suffices h : ∃ K : ℝ, 0 ≤ K ∧ ∀ k, l1 (piece k f) ≤ K ^ (k + 1) / k.factorial from h.imp fun _ h => h.2
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, le_rfl, fun k => by simp [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.1, l1]⟩
  | add f g hf hg =>
    obtain ⟨K, hK, h⟩ := hf
    obtain ⟨K', hK', h'⟩ := hg
    refine ⟨K + K', by positivity, fun k => ?_⟩
    rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).1]
    refine (intMvPolynomialCoeffAbsSum_add_le _ _).trans ((add_le_add (h k) (h' k)).trans ?_)
    rw [← add_div]
    gcongr
    exact pow_add_pow_le hK hK' (Nat.succ_ne_zero k)
  | single v p =>
    set D : ℝ := ((p.totalDegree.factorial : ℕ) : ℝ) with hDd
    set y := l1 (lin v)
    have hy : 0 ≤ y := weightAbsEntrySum_nonneg _
    have hp := weightAbsEntrySum_nonneg p
    have hD : 0 ≤ D := Nat.cast_nonneg _
    refine ⟨l1 p * D + (y + 1), by positivity, fun k => ?_⟩
    rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.2]
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    have t : ∀ b ∈ Finset.range (k + 1), l1 (homogeneousComponent (k - b) p * (C ((b.factorial : ℂ)⁻¹) * lin v ^ b)) ≤
        l1 p * D / k.factorial * (y ^ b * 1 ^ (k - b) * k.choose b) := by
      intro b hb
      have hbk : b ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      by_cases hd : p.totalDegree < k - b
      · rw [homogeneousComponent_eq_zero _ p hd, zero_mul]
        simp only [l1, support_zero, Finset.sum_empty]
        exact mul_nonneg (div_nonneg (mul_nonneg hp hD) hk.le) (by positivity)
      · have h1 : l1 (homogeneousComponent (k - b) p) ≤ l1 p := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p p).2.2.2.2.1 _
        have h2 : l1 (C ((b.factorial : ℂ)⁻¹) * lin v ^ b) ≤ (b.factorial : ℝ)⁻¹ * y ^ b := by
          have e : l1 (C ((b.factorial : ℂ)⁻¹) * lin v ^ b) = ‖(b.factorial : ℂ)⁻¹‖ * l1 (lin v ^ b) :=
            (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι (lin v ^ b) p).2.2.1 _
          rw [e, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (intMvPolynomialCoeffAbsSum_pow_le _ _) (by positivity)
        have h3 : ((k - b).factorial : ℝ) ≤ D := Nat.cast_le.2 (Nat.factorial_le (not_lt.1 hd))
        have h4 : (k.factorial : ℝ) = k.choose b * b.factorial * (k - b).factorial := by
          exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hbk).symm
        have hb0 : (0 : ℝ) < b.factorial := by exact_mod_cast b.factorial_pos
        have hc0 : (0 : ℝ) < k.choose b := by exact_mod_cast Nat.choose_pos hbk
        have he0 : (0 : ℝ) < (k - b).factorial := by exact_mod_cast (k - b).factorial_pos
        refine (intMvPolynomialCoeffAbsSum_mul_le _ _).trans ((mul_le_mul h1 h2 (weightAbsEntrySum_nonneg _) hp).trans ?_)
        calc l1 p * ((b.factorial : ℝ)⁻¹ * y ^ b)
            = l1 p * (k - b).factorial / k.factorial * (y ^ b * 1 ^ (k - b) * k.choose b) := by
              rw [h4]; field_simp; simp
          _ ≤ _ := by gcongr
    refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ((Finset.sum_le_sum t).trans ?_)
    rw [← Finset.mul_sum, ← add_pow, div_mul_eq_mul_div, pow_succ']
    have : 0 ≤ l1 p * D := mul_nonneg hp hD
    refine div_le_div_of_nonneg_right (mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) k) (by positivity) (by linarith)) hk.le
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.KillLiftSingle
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

namespace UpperTheory.ConvolutionTheory.FX

private theorem kill_lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A)
    (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ) (p : MvPolynomial ι ℂ) :
    PositivityTheory.Rg.Fx.lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [PositivityTheory.Rg.Fx.lift]

private theorem kill_ev_X {ι : Type} [Fintype ι] (Λ : ι → ℂ) (i : ι) :
    ev Λ (AddMonoidAlgebra.single 0 (X i)) = Λ i := by
  rw [ev, kill_lift_single]
  simp

private theorem kill_aff_id {ι : Type} [Fintype ι] [DecidableEq ι] (f : EP ι) :
    aff (0 : ι → ℂ) (1 : Matrix ι ι ℝ) f = f := by
  have hx : ∀ p : MvPolynomial ι ℂ,
      aeval (fun i : ι => (AddMonoidAlgebra.single 0
        (C ((0 : ι → ℂ) i) + lin ((1 : Matrix ι ι ℝ) i)) : EP ι)) p = AddMonoidAlgebra.single 0 p := by
    intro p
    have h1 : ∀ i : ι, C ((0 : ι → ℂ) i) + lin ((1 : Matrix ι ι ℝ) i) = (X i : MvPolynomial ι ℂ) := by
      intro i
      simp [lin, Matrix.one_apply, apply_ite]
    simp only [h1]
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add (f := _), hp, hq, AddMonoidAlgebra.single_add]
    | mul_X p i hp => rw [map_mul, hp, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add (f := _), hf, hg]
  | single v p =>
    rw [aff, kill_lift_single, hx]
    simp [affChar, expChar, AddMonoidAlgebra.single_mul_single]

private theorem kill_ren_id {ι : Type} [Fintype ι] [DecidableEq ι] (f : EP ι) :
    ren (id : ι → ι) f = f := by
  have : (Matrix.of fun i j : ι => if id i = j then (1 : ℝ) else 0) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [ren, this, kill_aff_id]

private theorem kill_ren_ren {ι : Type} [Fintype ι] [DecidableEq ι] (δ δ' : ι → ι) (f : EP ι) :
    ren δ' (ren δ f) = ren (δ' ∘ δ) f := by
  rw [ren, ren, ren, (subst ι ι _ _ f).2]
  congr 2
  · funext i
    simp
  · ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (δ i)]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp

private theorem kill_ev_ren {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → ι) (Λ : ι → ℂ) (f : EP ι) :
    ev Λ (ren δ f) = ev (Λ ∘ δ) f := by
  rw [ren, (subst ι ι _ _ f).1]
  congr 2
  funext i
  simp [apply_ite]

private theorem kill_evK_ren {ι κ : Type} [Fintype ι] [DecidableEq ι] (δ : ι → ι) (Λ : ι → ℂ) (h : κ → ℂ)
    (G : KF ι κ) : evK Λ h (map (ren δ) G) = evK (Λ ∘ δ) h G := by
  have : (ev Λ).comp (ren δ) = ev (Λ ∘ δ) := RingHom.ext (kill_ev_ren δ Λ)
  rw [evK, evK, coe_eval₂Hom, coe_eval₂Hom, eval₂_map, this]

private theorem kill_mem_of_ker {ι κ : Type} [Fintype ι] (b : Fam ι κ) (Λ : ι → ℂ) (h : κ → ℂ)
    (H : RingHom.ker b.sub ≤ RingHom.ker (evK Λ h)) : b.Mem Λ h := by
  classical
  let Λ₁ : Fin b.r → ℂ := fun j => - ∑ i, (b.pr j i : ℂ) * b.Λ i
  let lam : Fin b.r → ℂ := fun j => Λ₁ j + ∑ i, (b.pr j i : ℂ) * Λ i
  have hret : ∀ y : EP (Fin b.r), aff b.Λ b.emb (aff Λ₁ b.pr y) = y := by
    intro y
    rw [(subst _ _ _ _ y).2, b.pr_emb]
    have : (fun j => Λ₁ j + ∑ i, (b.pr j i : ℂ) * b.Λ i) = 0 := by
      funext j
      simp [Λ₁]
    rw [this, kill_aff_id]
  have key : ∀ F : KF ι κ, evK Λ h F = ev lam (b.sub F) := by
    intro F
    have h1 : F - C (aff Λ₁ b.pr (b.sub F)) ∈ RingHom.ker b.sub := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      generalize b.sub F = y
      rw [Fam.sub, eval₂Hom_C, hret]
    have h2 := H h1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h2
    rw [h2, evK, eval₂Hom_C, (subst _ _ _ _ _).1]
  refine ⟨lam, fun i => ?_, fun k => ?_⟩
  · have := key (C (AddMonoidAlgebra.single 0 (X i)))
    rw [evK, Fam.sub, eval₂Hom_C, eval₂Hom_C, (subst _ _ _ _ _).1, kill_ev_X, kill_ev_X] at this
    exact this
  · have := key (X k)
    rw [evK, Fam.sub, eval₂Hom_X', eval₂Hom_X'] at this
    exact this

end UpperTheory.ConvolutionTheory.FX

open UpperTheory.ConvolutionTheory.FX in
theorem UpperTheory.ConvolutionTheory.FX.killing0 :
    ∀ (ι κ B : Type) [Fintype ι] [DecidableEq ι] [Fintype B] (W : Subgroup (Equiv.Perm ι)) (b : B → Fam ι κ) (Λ₀ : ι → ℂ) (h₀ : κ → ℂ), (∀ w ∈ W, ∀ i, ¬ (b i).Mem (Λ₀ ∘ w) h₀) → ∃ F : KF ι κ, (∀ w ∈ W, map (ren (w : ι → ι)) F = F) ∧ (∀ i, (b i).sub F = 0) ∧ evK Λ₀ h₀ F ≠ 0 := by
  intro ι κ B _ _ _ W b Λ₀ h₀ hW
  classical
  haveI : Fintype W := Fintype.ofFinite W
  have hG : ∀ i, ∃ G : KF ι κ, (b i).sub G = 0 ∧ ∀ w : W, evK (Λ₀ ∘ (w : Equiv.Perm ι)) h₀ G ≠ 0 := by
    intro i
    by_contra hc
    push Not at hc
    have hsub : ((RingHom.ker (b i).sub : Ideal (KF ι κ)) : Set (KF ι κ)) ⊆
        ⋃ w ∈ (↑(Finset.univ : Finset W) : Set W),
          ((RingHom.ker (evK (Λ₀ ∘ (w : Equiv.Perm ι)) h₀) : Ideal (KF ι κ)) : Set (KF ι κ)) := by
      intro G hG
      obtain ⟨w, hw⟩ := hc G hG
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ w)) hw
    obtain ⟨w, -, hw⟩ := (Ideal.subset_union_prime (1 : W) 1
      (fun w _ _ _ => RingHom.ker_isPrime _)).1 hsub
    exact hW w w.2 i (kill_mem_of_ker _ _ _ hw)
  choose G hG0 hG1 using hG
  refine ⟨∏ i, ∏ w : W, map (ren ((w : Equiv.Perm ι) : ι → ι)) (G i), ?_, ?_, ?_⟩
  · intro w' hw'
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨w', hw'⟩ : W)) _ _ fun w => ?_
    have hc : (ren (w' : ι → ι)).comp (ren ((w : Equiv.Perm ι) : ι → ι)) =
        ren (((w' * (w : Equiv.Perm ι) : Equiv.Perm ι)) : ι → ι) := by
      rw [Equiv.Perm.coe_mul]
      exact RingHom.ext fun f => by rw [RingHom.comp_apply, kill_ren_ren]
    rw [MvPolynomial.map_map, hc, Equiv.coe_mulLeft, Subgroup.coe_mul]
  · intro i
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ (1 : W)) ?_
    have : ren (((1 : W) : Equiv.Perm ι) : ι → ι) = RingHom.id _ := by
      rw [Subgroup.coe_one, Equiv.Perm.coe_one]
      exact RingHom.ext fun f => by rw [kill_ren_id, RingHom.id_apply]
    rw [this, MvPolynomial.map_id, hG0]
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [kill_evK_ren]
    exact hG1 i w
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingle
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ)
    (p : MvPolynomial ι ℂ) : lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem shift_sum (g : ℕ → ℕ → ℂ) (s : ℕ → ℂ) (d : ℕ) (h0 : ∀ a, d < a → ∀ b, g a b = 0) (h : ∀ a, HasSum (g a) (s a)) :
    HasSum (fun k => ∑ b ∈ Finset.range (k + 1), g (k - b) b) (∑ a ∈ Finset.range (d + 1), s a) := by
  have h1 : ∀ a, HasSum (fun k => if a ≤ k then g a (k - a) else 0) (s a) := fun a => by
    rw [← hasSum_nat_add_iff' a, Finset.sum_eq_zero fun i hi => if_neg (not_le.2 (Finset.mem_range.1 hi)), sub_zero]
    simpa using h a
  convert hasSum_sum (s := Finset.range (d + 1)) fun a _ => h1 a using 2 with k
  rw [← Finset.sum_range_reflect, ← Finset.sum_filter]
  have e : ∀ j ∈ Finset.range (k + 1), g (k - (k + 1 - 1 - j)) (k + 1 - 1 - j) = g j (k - j) := fun j hj => by
    have := Finset.mem_range.1 hj
    congr 1
    omega
  rw [Finset.sum_congr rfl e]
  symm
  refine Finset.sum_subset (fun a ha => ?_) fun a ha hn => h0 a ?_ _
  · simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  · simp only [Finset.mem_filter, Finset.mem_range] at ha hn
    omega

private theorem exp_sum {A M : Type} [CommRing A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    (φ : M →ₗ[ℂ] ℂ) (l : A) (c s : ℂ) (m : M) (h : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * φ (l ^ k • m)) s) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * φ ((algebraMap ℂ A c + l) ^ k • m)) (Complex.exp c * s) := by
  have e1 : HasSum (fun b : ℕ => (b.factorial : ℂ)⁻¹ * c ^ b) (Complex.exp c) := by
    rw [Complex.exp_eq_exp_ℂ]
    simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp c
  have s1 := (summable_norm_sum_mul_range_of_summable_norm e1.summable.norm h.summable.norm).of_norm
  have t := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm e1.summable.norm h.summable.norm
  rw [e1.tsum_eq, h.tsum_eq] at t
  rw [t]
  refine (congrArg (HasSum · _) (funext fun k => ?_)).mpr s1.hasSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, Finset.sum_smul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbk : b ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
  have e : algebraMap ℂ A c ^ b * l ^ (k - b) * (k.choose b : A) = (c ^ b * k.choose b : ℂ) • l ^ (k - b) := by
    rw [Algebra.smul_def, map_mul, map_pow, map_natCast]
    ring
  have h4 : (k.factorial : ℂ) = k.choose b * b.factorial * (k - b).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hbk).symm
  have hb0 : (b.factorial : ℂ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  have hc0 : (k.choose b : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hbk).ne'
  have he0 : ((k - b).factorial : ℂ) ≠ 0 := by exact_mod_cast (k - b).factorial_ne_zero
  rw [e, smul_assoc, map_smul, smul_eq_mul, h4]
  field_simp

theorem UpperTheory.ConvolutionTheory.FX.rearrange :
    PositivityTheory.Rg.Fx.Rearrange := by
  intro ι κ _ b A M _ _ _ _ _ _ D τ φ hT F m
  set ξ : ι → A := fun i => algebraMap ℂ A (b.Λ i) + ∑ j, (b.emb i j : ℂ) • D j with hξ
  have hA : ∀ (f : EP ι) (m : M), HasSum (fun k => φ (aeval ξ (piece k f) • m)) (φ (lift D τ (aff b.Λ b.emb f) • m)) := by
    intro f m
    induction f using AddMonoidAlgebra.induction_linear with
    | zero =>
      simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.1, map_zero, zero_smul]
      exact hasSum_zero
    | add f g hf hg =>
      simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).1 f g, map_add (f := _), add_smul]
      exact hf.add hg
    | single v p =>
      set c : ℂ := ∑ i, (v i : ℂ) * b.Λ i with hc
      set t := τ (Multiplicative.ofAdd (Matrix.vecMul v b.emb)) with ht
      have hl : aeval ξ (lin v) = algebraMap ℂ A c + ∑ j, ((Matrix.vecMul v b.emb j : ℝ) : ℂ) • D j := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [lin, map_sum, map_mul, aeval_C, aeval_X, hξ, hc, mul_add, Finset.sum_add_distrib, Matrix.vecMul, dotProduct,
          Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul, Finset.mul_sum, Algebra.smul_def, mul_assoc]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul, mul_assoc]
      have hp : ∀ q : MvPolynomial ι ℂ, lift D τ (aeval (fun i => (AddMonoidAlgebra.single 0 (C (b.Λ i) + lin (b.emb i)) : EP (Fin b.r))) q) =
          aeval ξ q := fun q => by
        induction q using MvPolynomial.induction_on with
        | C a => simp [AddMonoidAlgebra.coe_algebraMap, lift_single]
        | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
        | mul_X p j hp =>
          rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, lift_single]
          simp [hξ, lin, Algebra.smul_def]
      have hv : lift D τ (aff b.Λ b.emb (AddMonoidAlgebra.single v p)) = aeval ξ p * (Complex.exp c • t) := by
        rw [aff, lift_single, map_mul, hp]
        simp [affChar, expChar, lift_single, Algebra.smul_def, hc, ht]
      have h1 := shift_sum (fun a k => (k.factorial : ℂ)⁻¹ * φ (aeval ξ (lin v) ^ k • aeval ξ (homogeneousComponent a p) • m))
        (fun a => Complex.exp c * φ (t • aeval ξ (homogeneousComponent a p) • m)) p.totalDegree
        (fun a ha k => by rw [homogeneousComponent_eq_zero a p ha]; simp)
        (fun a => by rw [hl]; exact exp_sum φ _ c _ _ (hT _ _))
      convert h1 using 1
      · funext k
        set_option synthInstance.maxHeartbeats 100000 in
          rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.2, map_sum, Finset.sum_smul, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul, aeval_C, map_pow, mul_comm, ← Algebra.smul_def, smul_mul_assoc, smul_assoc, map_smul, mul_smul,
          smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [hv, ← Finset.mul_sum, ← map_sum, ← Finset.smul_sum, ← Finset.sum_smul, ← map_sum, sum_homogeneousComponent,
          mul_comm, smul_mul_assoc, smul_assoc, map_smul, mul_smul, smul_eq_mul]
  have h2 := hasSum_sum (s := F.support) fun β _ => hA (F.coeff β) ((β.prod fun k e => lift D τ (b.h k) ^ e) • m)
  convert (preTransparency := .reducible) h2 using 1
  · funext k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pieceK, eval₂_sum, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [eval₂_monomial, mul_smul]
    rfl
  · conv_lhs => rw [F.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_smul, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Fam.sub, eval₂Hom_monomial, map_mul, mul_smul, map_finsuppProd]
    simp only [map_pow]
end

