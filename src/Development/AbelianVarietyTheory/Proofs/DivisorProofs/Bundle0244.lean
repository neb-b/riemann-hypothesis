module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChange
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.LocAcyc

theorem isZModTorsor_baseChange : ∀ (B B' D : Type) [CommRing B] [CommRing B'] [CommRing D]
    [Algebra B B'] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.LocAcyc.IsZModTorsor B D q act →
    ∃ act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)),
      (∀ (g : Multiplicative (ZMod q)) (b : B') (x : D), act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x) ∧
      GlobalTheory.LocAcyc.IsZModTorsor B' (B' ⊗[B] D) q act' := by
  intro B B' D _ _ _ _ _ q hq act hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  haveI : NeZero q := ⟨hq.ne'⟩
  let act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)) :=
    { toFun := fun g => Algebra.TensorProduct.congr (AlgEquiv.refl : B' ≃ₐ[B'] B') (act g)
      map_one' := by
        apply AlgEquiv.ext; intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      map_mul' := by
        intro g h
        apply AlgEquiv.ext; intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x => simp [Algebra.TensorProduct.congr_apply, AlgEquiv.mul_apply]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy] }
  have hact : ∀ (g : Multiplicative (ZMod q)) (b : B') (x : D),
      act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x := by
    intro g b x
    simp [act', Algebra.TensorProduct.congr_apply]
  refine ⟨act', hact, inferInstance, inferInstance, inferInstance, ?_⟩
  let Φ := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))
  let e := (LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B'
  let dBC := TensorProduct.AlgebraTensorModule.distribBaseChange B B' D D
  let pR := TensorProduct.piRight B B' B' (fun _ : Multiplicative (ZMod q) => D)
  have key : ∀ z, (Algebra.TensorProduct.productMap
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun _ => AlgHom.id B' _))
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun g => (act' g).toAlgHom)))
      (dBC z) = pR (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        funext g
        simp [dBC, pR, e, Φ, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          Algebra.TensorProduct.productMap_apply_tmul, hact, Algebra.TensorProduct.tmul_mul_tmul,
          LinearEquiv.ofBijective_apply]
        rfl
      | add s t hs ht => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]
    | add s t hs ht => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]
  have hfun : ⇑(Algebra.TensorProduct.productMap
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun _ => AlgHom.id B' _))
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun g => (act' g).toAlgHom)))
      = fun w => pR (e (dBC.symm w)) := by
    funext w
    rw [← key, dBC.apply_symm_apply]
  rw [hfun]
  exact pR.bijective.comp (e.bijective.comp dBC.symm.bijective)

end GlobalTheory.LocAcyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformBound
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo.TermBoundDeriv

theorem rpow_le_add_inv_pow {t r : ℝ} {s : ℕ} (ht : 0 < t) (hr : |r| ≤ s) :
    t ^ r ≤ (t + t⁻¹) ^ s := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have hM1 : 1 ≤ t + t⁻¹ := by
    rcases le_total 1 t with h | h
    · linarith
    · have : 1 ≤ t⁻¹ := one_le_inv_iff₀.mpr ⟨ht, h⟩
      linarith
  have hsr : (t + t⁻¹) ^ (s : ℝ) = (t + t⁻¹) ^ s := Real.rpow_natCast _ _
  rw [← hsr]
  rcases le_total 0 r with h0 | h0
  · calc t ^ r ≤ (t + t⁻¹) ^ r := Real.rpow_le_rpow ht.le (by linarith) h0
      _ ≤ (t + t⁻¹) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (le_trans (le_abs_self r) hr)
  · have e : t ^ r = t⁻¹ ^ (-r) := by
      rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv]
    rw [e]
    calc t⁻¹ ^ (-r) ≤ (t + t⁻¹) ^ (-r) := Real.rpow_le_rpow hti.le (by linarith) (by linarith)
      _ ≤ (t + t⁻¹) ^ (s : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (le_trans (neg_le_abs r) hr)

end GlobalTheory.HeckeTwo.TermBoundDeriv

namespace GlobalTheory.HeckeTwo.TermBoundDeriv

theorem iteratedDeriv_hTrans_bound :
    (∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y) → (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N := by
  intro hder hint K hK hKH j
  obtain ⟨S, P, hS, hEq⟩ := hder j
  obtain ⟨R, hR⟩ : ∃ R, ∀ σ ∈ K, ‖σ‖ ≤ R := hK.isBounded.exists_norm_le
  refine ⟨⌈1 + (j : ℝ) + 2 * R⌉₊, fun N => ?_⟩
  have hCex : ∀ p : ℕ × ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ (p ∈ S → ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖ ≤
        C * |y| ^ ((p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re) / (1 + |ν * y|) ^ N) := by
    intro p
    by_cases hp : p ∈ S
    · obtain ⟨C, hC⟩ := hint K hK hKH p.1 p.2.1 p.2.2 (hS p hp).1 N
      refine ⟨max C 0, le_max_right _ _, fun _ σ hσ ν y hν hy => (hC σ hσ ν y hν hy).trans ?_⟩
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
    · exact ⟨0, le_rfl, fun h => absurd h hp⟩
  choose Cp hCp0 hCp using hCex
  have hBex : ∀ p : ℕ × ℕ × ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ σ ∈ K, ‖(P p).eval σ‖ ≤ B := by
    intro p
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (P p).continuous.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun σ hσ => (hB σ hσ).trans (le_max_left _ _)⟩
  choose B hB0 hB using hBex
  refine ⟨∑ p ∈ S, B p * Cp p, fun σ hσ ν y hν hy => ?_⟩
  have hy' : 0 < |y| := abs_pos.mpr hy
  have hD : 0 < (1 + |ν * y|) ^ N := by positivity
  have hre : |σ.re| ≤ R := (Complex.abs_re_le_norm σ).trans (hR σ hσ)
  rw [hEq σ (hKH hσ) ν y hy]
  calc ‖∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖
      ≤ ∑ p ∈ S, ‖(P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ S, B p * (Cp p * (|y| + |y|⁻¹) ^ ⌈1 + (j : ℝ) + 2 * R⌉₊ / (1 + |ν * y|) ^ N) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [norm_mul]
        apply mul_le_mul (hB p σ hσ) _ (norm_nonneg _) (hB0 p)
        refine (hCp p hp σ hσ ν y hν hy).trans ?_
        apply div_le_div_of_nonneg_right _ hD.le
        apply mul_le_mul_of_nonneg_left _ (hCp0 p)
        apply rpow_le_add_inv_pow hy'
        have hc : (p.1 : ℝ) + 2 * p.2.1 = p.2.2 + 2 + j := by exact_mod_cast (hS p hp).2
        have he : (p.2.2 : ℝ) + 1 - p.1 - 2 * p.2.1 - 2 * σ.re = -(1 + j + 2 * σ.re) := by
          linarith
        rw [he, abs_neg]
        refine le_trans ?_ (Nat.le_ceil _)
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        calc |1 + (j : ℝ) + 2 * σ.re| ≤ |1 + (j : ℝ)| + |2 * σ.re| := abs_add_le _ _
          _ = 1 + j + 2 * |σ.re| := by
              rw [abs_of_nonneg (by linarith), abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          _ ≤ 1 + j + 2 * R := by linarith
    _ = (∑ p ∈ S, B p * Cp p) * (|y| + |y|⁻¹) ^ ⌈1 + (j : ℝ) + 2 * R⌉₊ / (1 + |ν * y|) ^ N := by
        rw [Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

end GlobalTheory.HeckeTwo.TermBoundDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformRepr
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwo.TermSmooth

theorem sum_pushforward_eval (σ : ℂ) (F : ℕ × ℕ × ℕ → ℂ) (g : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ)
    (c : ℕ × ℕ × ℕ → Polynomial ℂ) (U S' : Finset (ℕ × ℕ × ℕ)) (hU : ∀ p ∈ U, g p ∈ S') :
    ∑ q ∈ S', (∑ p ∈ U, if g p = q then c p else 0).eval σ * F q = ∑ p ∈ U, (c p).eval σ * F (g p) := by
  simp_rw [Polynomial.eval_finsetSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp_rw [apply_ite (Polynomial.eval σ), Polynomial.eval_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hU p hp)]

theorem iteratedDeriv_hTrans_repr : ∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y := by
  intro j
  induction j with
  | zero =>
    refine ⟨{(2, 0, 0)}, fun _ => 1, ?_, ?_⟩
    · intro p hp; rw [Finset.mem_singleton] at hp; subst hp; norm_num
    · intro σ hσ ν y hy
      simp [iteratedDeriv_zero, hTrans_eq σ ν hy]
  | succ j ih =>
    obtain ⟨S, P, hS, hP⟩ := ih
    let f1 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1 + 1, p.2.1, p.2.2)
    let f2 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1, p.2.1 + 1, p.2.2 + 1)
    let f3 : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (p.1, p.2.1, p.2.2 - 1)
    let T := S.filter (fun p => 1 ≤ p.2.2)
    let c1 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p => Polynomial.C (-(p.1 : ℂ) * I) * P p
    let c2 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p =>
      Polynomial.C 2 * (-Polynomial.X - Polynomial.C (p.2.1 : ℂ)) * P p
    let c3 : ℕ × ℕ × ℕ → Polynomial ℂ := fun p => Polynomial.C (p.2.2 : ℂ) * P p
    let S' := S.image f1 ∪ S.image f2 ∪ T.image f3
    refine ⟨S', fun q => (∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0)
        + ∑ p ∈ T, if f3 p = q then c3 p else 0, ?_, ?_⟩
    · intro q hq
      simp only [S', Finset.mem_union, Finset.mem_image, T, Finset.mem_filter] at hq
      rcases hq with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, ⟨hp, hm⟩, rfl⟩ <;>
        have := hS p hp <;> simp only [f1, f2, f3] <;> omega
    · intro σ hσ ν y hy
      have hev : iteratedDeriv j (hTrans σ ν) =ᶠ[nhds y]
          fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y :=
        Filter.eventually_of_mem (isOpen_ne.mem_nhds hy) fun z hz => hP σ hσ ν z hz
      have hd : HasDerivAt (fun y => ∑ p ∈ S, (P p).eval σ * intT σ ν p.1 p.2.1 p.2.2 y)
          (∑ p ∈ S, (P p).eval σ * (-(p.1 : ℂ) * I * intT σ ν (p.1 + 1) p.2.1 p.2.2 y
            + 2 * (-σ - (p.2.1 : ℂ)) * intT σ ν p.1 (p.2.1 + 1) (p.2.2 + 1) y
            + (p.2.2 : ℂ) * intT σ ν p.1 p.2.1 (p.2.2 - 1) y)) y :=
        HasDerivAt.fun_sum fun p hp => (hasDerivAt_intT σ hσ ν p.2.2 (hS p hp).1 hy).const_mul _
      rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]
      set F : ℕ × ℕ × ℕ → ℂ := fun q => intT σ ν q.1 q.2.1 q.2.2 y with hF
      have e1 := sum_pushforward_eval σ F f1 c1 S S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
      have e2 := sum_pushforward_eval σ F f2 c2 S S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
      have e3 := sum_pushforward_eval σ F f3 c3 T S' fun p hp => by
        simp only [S', Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨p, hp, rfl⟩
      have e3' : ∑ p ∈ T, (c3 p).eval σ * F (f3 p) = ∑ p ∈ S, (c3 p).eval σ * F (f3 p) := by
        refine Finset.sum_filter_of_ne fun p _ hne => ?_
        by_contra h
        have h0 : p.2.2 = 0 := by omega
        apply hne
        simp [c3, h0]
      have split : ∀ q, ((∑ p ∈ S, if f1 p = q then c1 p else 0) + (∑ p ∈ S, if f2 p = q then c2 p else 0)
          + ∑ p ∈ T, if f3 p = q then c3 p else 0).eval σ * F q =
          (∑ p ∈ S, if f1 p = q then c1 p else 0).eval σ * F q +
          (∑ p ∈ S, if f2 p = q then c2 p else 0).eval σ * F q +
          (∑ p ∈ T, if f3 p = q then c3 p else 0).eval σ * F q := by
        intro q; rw [Polynomial.eval_add, Polynomial.eval_add]; ring
      show _ = ∑ q ∈ S', _ * F q
      rw [Finset.sum_congr rfl fun q _ => split q, Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3, e3',
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [c1, c2, c3, F, f1, f2, f3, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_neg, Polynomial.eval_X]
      ring

end GlobalTheory.HeckeTwo.TermSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiTransformHasDerivAtHolo
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem iteratedDeriv_hTrans_eq_sum
    (h1 : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y)
    (n : ℝ) (k : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ → ℂ) (ab : ι → ℕ × ℕ),
      (∀ i, Differentiable ℂ (c i)) ∧ (∀ i, 2 ≤ (ab i).1 + (ab i).2) ∧
      ∀ σ ∈ halfPlane, ∀ y : ℝ, y ≠ 0 →
        iteratedDeriv k (hTrans σ n) y = ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y := by
  induction k with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => (2, 0), fun _ => by fun_prop,
      fun _ => by simp, fun σ _ y _ => ?_⟩
    simp [hTransAB_two_zero]
  | succ k ih =>
    obtain ⟨ι, _, c, ab, hc, hab, h⟩ := ih
    refine ⟨ι ⊕ ι, inferInstance,
      Sum.elim (fun i σ => c i σ * (I * (-((ab i).1 : ℂ) - σ)))
        (fun i σ => c i σ * (I * (((ab i).2 : ℂ) + σ))),
      Sum.elim (fun i => ((ab i).1 + 1, (ab i).2)) (fun i => ((ab i).1, (ab i).2 + 1)),
      ?_, ?_, ?_⟩
    · rintro (i | i)
      · have := hc i
        simp only [Sum.elim_inl]; fun_prop
      · have := hc i
        simp only [Sum.elim_inr]; fun_prop
    · rintro (i | i)
      · have := hab i
        simp only [Sum.elim_inl]; omega
      · have := hab i
        simp only [Sum.elim_inr]; omega
    · intro σ hσ y hy
      have hev : iteratedDeriv k (hTrans σ n) =ᶠ[nhds y]
          fun y' => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y' := by
        filter_upwards [isOpen_ne.mem_nhds hy] with y' hy' using h σ hσ y' hy'
      have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
        (h1 (ab i).1 (ab i).2 σ n y (hab i) hσ hy).const_mul (c i σ))).congr_of_eventuallyEq hev
      rw [iteratedDeriv_succ, hd.deriv, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Sum.elim_inl, Sum.elim_inr]
      ring

theorem iteratedDeriv_hTrans_jet :
    (∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y) → (∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane) →
  (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) := by
  intro h1 h2 n k y hy
  obtain ⟨ι, _, c, ab, hc, hab, h⟩ := iteratedDeriv_hTrans_eq_sum h1 n k
  refine ⟨fun σ hσ => ?_, ?_⟩
  · have hev : iteratedDeriv k (hTrans σ n) =ᶠ[nhds y]
        fun y' => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y' := by
      filter_upwards [isOpen_ne.mem_nhds hy] with y' hy' using h σ hσ y' hy'
    have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (h1 (ab i).1 (ab i).2 σ n y (hab i) hσ hy).const_mul (c i σ))).congr_of_eventuallyEq hev
    rw [iteratedDeriv_succ]
    exact hd.differentiableAt.hasDerivAt
  · refine DifferentiableOn.congr
      (f := fun σ => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y) ?_ (fun σ hσ => h σ hσ y hy)
    exact DifferentiableOn.fun_sum fun i _ =>
      (hc i).differentiableOn.mul (h2 _ _ n y (hab i) hy)

end GlobalTheory.HeckeTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorToSubschemeSectionsRestricStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_affineHilbertTensorToSubschemeSections_restrict :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
      (g : T ⟶ Spec (CommRingCat.of A))
      (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
      (U V : T.affineOpens) (h : (U : T.Opens) ≤ V),
      letI := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
      letI := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
      ∃ ρ : Γ(T, V) →ₐ[A] Γ(T, U), ρ.toRingHom = (T.presheaf.map (homOfLE h).op).hom ∧
        (RingHom.ker (GlobalTheory.HilbAff.kappa A B g I V)).map
          (Algebra.TensorProduct.map ρ (AlgHom.id A B)) ≤
        RingHom.ker (GlobalTheory.HilbAff.kappa A B g I U) := by
  intro A B _ _ _ T g I U V h
  let := (GlobalTheory.HilbAff.secAlg A g U).toAlgebra
  let := (GlobalTheory.HilbAff.secAlg A g V).toAlgebra
  let ρ : Γ(T, V) →ₐ[A] Γ(T, U) :=
    { toRingHom := (T.presheaf.map (homOfLE h).op).hom
      commutes' := fun a => by
        exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
          (Scheme.Hom.appLE_map g (U := ⊤) (by simp) (homOfLE h).op) }
  refine ⟨ρ, rfl, ?_⟩
  have kappa_tmul (W : T.Opens) (c : Γ(T, W)) (b : B) :
      letI := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
      GlobalTheory.HilbAff.kappa A B g I W (c ⊗ₜ[A] b) =
        ((I.subschemeι ≫ pullback.snd _ g).app W).hom c *
          ((I.subschemeι ≫ pullback.fst _ g).appLE ⊤
            ((I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) (by simp)).hom
              ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
    let := (GlobalTheory.HilbAff.secAlg A g W).toAlgebra
    let : Algebra A Γ(I.subscheme, (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ W) :=
      (((I.subschemeι ≫ pullback.snd _ g).app W).hom.comp
        (GlobalTheory.HilbAff.secAlg A g W)).toAlgebra
    exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hκ (t : Γ(T, V) ⊗[A] B) :
      GlobalTheory.HilbAff.kappa A B g I U (Algebra.TensorProduct.map ρ (AlgHom.id A B) t) =
        (I.subscheme.presheaf.map (homOfLE (Scheme.Hom.preimage_mono
          (I.subschemeι ≫ pullback.snd _ g) h)).op).hom (GlobalTheory.HilbAff.kappa A B g I V t) := by
    induction t using TensorProduct.inductionOn with
    | tmul c b =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, kappa_tmul, kappa_tmul, map_mul]
      have hc : ρ c = (T.presheaf.map (homOfLE h).op).hom c := rfl
      rw [hc]
      congr 1
      · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
        rfl
      · have e := Scheme.Hom.appLE_map (I.subschemeι ≫ pullback.fst _ g) (U := ⊤)
            (V := (I.subschemeι ≫ pullback.snd _ g) ⁻¹ᵁ V) (by simp)
            (homOfLE (Scheme.Hom.preimage_mono (I.subschemeι ≫ pullback.snd _ g) h)).op
        exact (congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) e).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Ideal.map_le_iff_le_comap]
  intro t ht
  rw [RingHom.mem_ker] at ht
  rw [Ideal.mem_comap, RingHom.mem_ker]
  erw [hκ t, ht, map_zero]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerMapSubsetImMap
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem ker_map_subset_im_map (R C : Type) [CommRing R] [Field C] (f : R →+* C) (ξ ν : R) (N : ℕ)
    (F G : Matrix (Fin N) (Fin N) R) (hξ : ξ ∈ nonZeroDivisors R) (hν : f ν ≠ 0)
    (hfrac : ∀ c : C, ∃ s t : R, f s ≠ 0 ∧ c * f s = f t)
    (hker : ∃ s : R, f s ≠ 0 ∧ ∀ r : R, f r = 0 → ξ ∣ s * r)
    (hGF : G * F = (ξ * ν) • (1 : Matrix (Fin N) (Fin N) R))
    (x : Fin N → C) (hx : F.map f *ᵥ x = 0) : ∃ y : Fin N → C, x = G.map f *ᵥ y := by
  classical
  obtain ⟨s, hs, hsker⟩ := hker
  choose a b ha hab using fun i => hfrac (x i)

  set s0 : R := ∏ i, a i with hs0
  have hs0ne : f s0 ≠ 0 := by
    rw [hs0, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  let t : Fin N → R := fun i => b i * ∏ j ∈ Finset.univ.erase i, a j
  have ht : ∀ i, f (t i) = x i * f s0 := by
    intro i
    have h1 : s0 = a i * ∏ j ∈ Finset.univ.erase i, a j :=
      (Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)).symm
    simp only [t, map_mul, ← hab i]
    rw [h1, map_mul, mul_assoc]
  have hft : (f ∘ t) = f s0 • x := by
    funext i
    simp [ht i, mul_comm]

  have hFt : ∀ i, f ((F *ᵥ t) i) = 0 := by
    intro i
    rw [RingHom.map_mulVec, hft, Matrix.mulVec_smul, hx]
    simp
  choose w hw using fun i => hsker _ (hFt i)
  have hw' : s • (F *ᵥ t) = ξ • w := by
    funext i
    simpa using hw i

  have hG : ξ • ((s * ν) • t) = ξ • (G *ᵥ w) := by
    have h2 : G *ᵥ (s • (F *ᵥ t)) = G *ᵥ (ξ • w) := by rw [hw']
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGF, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h2
    rw [← h2]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hcancel : ∀ i, (s * ν) * t i = (G *ᵥ w) i := by
    intro i
    have h3 := congrFun hG i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    exact (mul_cancel_left_mem_nonZeroDivisors hξ).mp h3

  refine ⟨(f s * f ν * f s0)⁻¹ • (f ∘ w), ?_⟩
  funext i
  have h4 : f s * f ν * f s0 ≠ 0 := mul_ne_zero (mul_ne_zero hs hν) hs0ne
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← RingHom.map_mulVec, ← hcancel i, map_mul,
    map_mul, ht i]
  field_simp

end GlobalTheory.DetInv
end

