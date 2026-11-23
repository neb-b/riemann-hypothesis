module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFrameEOf
section
noncomputable section
open scoped BigOperators
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

theorem IntNorm_proof : IntNorm := by
  intro p _ E _ _ φ y
  obtain ⟨P, hP, hPx⟩ := RingOfIntegers.isIntegral_coe y
  have hx' : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (φ (y : E)) := by
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h := congrArg φ hPx
    rw [Polynomial.hom_eval₂, map_zero] at h
    rw [← h]
    congr 1
    exact Subsingleton.elim _ _
  have h := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx'
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem EigenFrame_of (hB : GramBasic) (hC : EigenCompat) : EigenFrame := by
  intro a b c d ha hd lam hlam hcm n _ _ h Λ g hg p _ ι hidx J _ v hv H _ _ N0 N1 A u hA Xo T T' chi chi'
    hadj hpres hchi' hT hT' hsep hnorm
  have hth0 : ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ≠ 0 := by
    have h1 : Complex.I * ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
      refine mul_ne_zero Complex.I_ne_zero ?_
      have h2 : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
      exact_mod_cast h2.ne'
    exact (map_ne_zero_iff ι ι.injective).2 h1
  generalize hth : ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = th at hth0 hnorm ⊢
  have hBx := fun x y => hB a b c d ha hd lam hlam hcm n h Λ g hg p ι hidx J v hv
    (fun j => A j x) (fun j => A j y) (fun j => hA j x) (fun j => hA j y)
  rw [hth] at hBx
  obtain ⟨BB, hBB⟩ : ∃ BB : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p],
      ∀ x y, BB x y = ∑ j, ∑ k, A j x * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * A k y :=
    ⟨_, fun _ _ => rfl⟩
  simp only [← hBB] at hBx hnorm
  have hcomp : ∀ e x y, ‖(chi e x.1 - chi' e y.1) * BB x y‖ ≤ ‖th‖ := by
    intro e x y
    obtain ⟨ε, hε, heq⟩ := hC a b c d ha hd lam hlam hcm n h Λ g hg p ι hidx J v hv (T e) (T' e) (hadj e)
      (hpres e) (fun j => A j x) (fun j => A j y) (chi e x.1) (chi' e y.1) (fun j => hA j x)
      (fun j => hA j y) (hchi' e y.1) (hT e x) (hT' e y)
    rw [hBB, heq, hth, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hε
  obtain ⟨q1, hq1, hsplit⟩ := Formalism.L2.Th1.G.eigenSplit ℂ_[p] ((Bool × H) × Fin N0 × Fin N1) (Bool × H) Xo
    (fun x => x.1) (fun τ => (!τ.1, τ.2)) BB th chi chi' hth0 (fun x y => (hBx x y).1) hcomp hsep
  have main : ∀ x y, ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
      BB x y = (if x.1.2 = y.1.2 ∧ x.2 = y.2 ∧ x.1.1 ≠ y.1.1 then u x.1.2 else 0) + th * e := by
    intro x y
    by_cases hxy : y.1 = (!x.1.1, x.1.2)
    · obtain ⟨⟨bx, t⟩, ab⟩ := x
      obtain ⟨⟨by', t'⟩, ab'⟩ := y
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      cases bx
      · obtain ⟨e, he, heq⟩ := hnorm t' ab ab'
        refine ⟨e, he, ?_⟩
        simp only [Bool.not_false]
        rw [heq]
        simp
      · obtain ⟨e, he, heq⟩ := hnorm t' ab' ab
        obtain ⟨e2, he2, hsym⟩ := (hBx ((true, t'), ab) ((false, t'), ab')).2.1
        refine ⟨e + e2, (IsUltrametricDist.norm_add_le_max _ _).trans (max_le he he2), ?_⟩
        simp only [Bool.not_true]
        rw [sub_eq_iff_eq_add.1 hsym, heq]
        simp only [eq_comm (a := ab') (b := ab)]
        simp
        ring
    · have h1 := hsplit x y
      simp only [if_neg hxy, zero_add] at h1
      refine ⟨q1 x y, hq1 x y, ?_⟩
      rw [if_neg, zero_add]
      · exact h1
      · rintro ⟨h2, _, h3⟩
        apply hxy
        refine Prod.ext ?_ h2.symm
        simp only
        revert h3
        cases x.1.1 <;> cases y.1.1 <;> simp
  choose q hq hqe using main
  refine ⟨q, hv, hA, hq, ?_⟩
  intro x y
  exact (hBB x y).symm.trans (hqe x y)

theorem EigenFrameE_of (hF : EigenFrame) (hS : SepPairs) (hN : IntNorm) : EigenFrameE := by
  intro a b c d ha hd lam hlam hcm n _ _ h Λ g hg p _ ι hidx J _ v hv hpd E _ _ _ cE s δ hδ hcδ hsδ hcc hss
    hsc H _ _ emb hinj hembδ hembt hKur act hadj hpres N0 N1 A u hA heig hnorm
  have hp2 : p ≠ 2 := by
    obtain ⟨_, _, h8, _⟩ := hcm
    omega
  refine hF a b c d ha hd lam hlam hcm n h Λ g hg p ι hidx J v hv H N0 N1 A u hA
    {ee : 𝓞 E × 𝓞 E // (ee.2 : E) = cE (ee.1 : E)} (fun ee => act ee.1.1) (fun ee => act ee.1.2)
    (fun ee τ => emb τ (ee.1.1 : E)) (fun ee τ => emb τ (ee.1.2 : E)) ?_ ?_ ?_ ?_ ?_ ?_ hnorm
  · intro ee x y
    exact hadj ee.1.1 ee.1.2 ee.2 x y
  · intro ee
    exact hpres ee.1.2
  · intro ee τ
    exact hN p E (emb τ) ee.1.2
  · intro ee x i
    exact heig ee.1.1 x i
  · intro ee x i
    exact heig ee.1.2 x i
  · intro τ ρ hρ
    obtain ⟨e, he⟩ := hS p hp2 E cE s δ hδ hcδ hsδ hcc hss hsc H emb hinj hembδ hembt hKur τ ρ hρ
    have hint : IsIntegral ℤ (cE (e : E)) := map_isIntegral_int cE (RingOfIntegers.isIntegral_coe e)
    exact ⟨⟨(e, ⟨cE (e : E), hint⟩), rfl⟩, he⟩

end Formalism.L2.Th1.GD
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Inertia
section
noncomputable section
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section SlopeTestRemainingChoices

variable {p : ℕ} [hp : Fact p.Prime]

lemma norm_p_eq : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have h : ‖(((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := PadicComplex.norm_extends' p _
  have h2 : (((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by
    simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p

lemma norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := by
  rw [norm_p_eq]
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  positivity

lemma norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [norm_p_eq]
  have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  exact inv_lt_one_of_one_lt₀ this

lemma norm_le_one_of_isIntegralElem {x : ℂ_[p]} (hx : (Int.castRingHom ℂ_[p]).IsIntegralElem x) :
    ‖x‖ ≤ 1 := by
  obtain ⟨P, hP, hPx⟩ := hx
  have hx' : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := by
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hPx]
    congr 1
  have h := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx'
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

lemma norm_map_le_one {E : Type} [Field E] [NumberField E] (ψ : E →+* ℂ_[p]) (y : 𝓞 E) :
    ‖ψ (y : E)‖ ≤ 1 := by
  obtain ⟨P, hP, hPx⟩ := RingOfIntegers.isIntegral_coe y
  refine norm_le_one_of_isIntegralElem ⟨P, hP, ?_⟩
  have h := congrArg ψ hPx
  rw [Polynomial.hom_eval₂, map_zero] at h
  rw [← h]
  congr 1
  exact Subsingleton.elim _ _

lemma kur_step {a : ℂ_[p]} (ha : a ∈ MaximalUnramifiedExtension p) (m : ℤ) (h : ‖a‖ < ‖(p : ℂ_[p])‖ ^ m) :
    ‖a‖ ≤ ‖(p : ℂ_[p])‖ ^ (m + 1) := by
  by_cases h0 : a = 0
  · rw [h0, norm_zero]
    exact (zpow_pos norm_p_pos _).le
  · obtain ⟨k, hk⟩ := Formalism.L2.Th1.D.kurUnram p a ha h0
    rw [hk] at h ⊢
    have h1 : m < k := (zpow_lt_zpow_iff_right_of_lt_one₀ norm_p_pos norm_p_lt_one).1 h
    exact (zpow_le_zpow_iff_right_of_lt_one₀ norm_p_pos norm_p_lt_one).2 (by omega)

end SlopeTestRemainingChoices

theorem InertiaRam_proof : InertiaRam := by
  intro p _ _ E _ _ s δ φ hδ hsδ hss hK
  set q : ℝ := ‖(p : ℂ_[p])‖ with hq
  have hq0 : 0 < q := norm_p_pos
  have hq1 : q < 1 := norm_p_lt_one
  set d : ℝ := ‖φ δ‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hdq : d ^ 2 = q := by
    rw [hd, ← norm_pow, ← map_pow, hδ, map_neg, map_natCast, norm_neg]
  have hdpos : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hdq
      norm_num at hdq
      exact absurd hdq hq0.ne
  have hd1 : d < 1 := by
    by_contra h
    rw [not_lt] at h
    have : 1 ≤ d ^ 2 := one_le_pow₀ h
    linarith
  have hqd : q ≤ d := by
    rw [← hdq]
    nlinarith
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [hd, h, map_zero, norm_zero] at hdpos
    exact lt_irrefl _ hdpos
  have hdr : d = q ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hdq, Real.sqrt_sq hd0]

  have key : ∀ b : ℂ_[p], b ∈ MaximalUnramifiedExtension p → ‖b‖ * d ≤ 1 → ‖b‖ ≤ 1 := by
    intro b hb h
    have h1 : ‖b‖ < q ^ (-1 : ℤ) := by
      rw [zpow_neg_one, ← hdq, ← one_div, lt_div_iff₀ (by positivity)]
      calc ‖b‖ * d ^ 2 = (‖b‖ * d) * d := by ring
        _ ≤ 1 * d := mul_le_mul_of_nonneg_right h hd0
        _ < 1 := by rw [one_mul]; exact hd1
    have := kur_step hb (-1) h1
    simpa using this
  have hint : ∀ y : 𝓞 E, ‖φ (y : E)‖ ≤ 1 := fun y => norm_map_le_one φ y
  have hints : ∀ y : 𝓞 E, ‖φ (s (y : E))‖ ≤ 1 := fun y => norm_map_le_one (φ.comp (s : E →+* E)) y
  refine ⟨hdr, ?_, ?_⟩
  · intro y
    rw [← hdr]
    set w : E := (y : E) - s (y : E) with hw
    have hsw : s (w / δ) = w / δ := by
      rw [map_div₀, hsδ, hw, map_sub, hss, div_neg, ← neg_div, neg_sub]
    have hw1 : ‖φ w‖ ≤ 1 := by
      rw [hw, map_sub, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint y) ?_)
      rw [norm_neg]
      exact hints y
    have hmul : ‖φ (w / δ)‖ * d = ‖φ w‖ := by
      rw [hd, ← norm_mul, ← map_mul, div_mul_cancel₀ _ hδ0]
    have h1 := key _ (hK _ hsw) (by rw [hmul]; exact hw1)
    rw [← map_sub, ← hw, ← hmul]
    exact mul_le_of_le_one_left hd0 h1
  · intro y hy
    set a : E := ((y : E) + s (y : E)) / 2 with ha
    set b : E := ((y : E) - s (y : E)) / (2 * δ) with hb
    have hsa : s a = a := by
      rw [ha, map_div₀, map_add (f := _), hss, map_ofNat, add_comm]
    have hsb : s b = b := by
      rw [hb, map_div₀, map_mul, hsδ, map_sub, hss, map_ofNat, mul_neg, div_neg, ← neg_div, neg_sub]
    have hy' : (y : E) = a + b * δ := by
      rw [ha, hb]
      field_simp
      ring
    have hnb : ‖φ (b * δ)‖ = ‖φ b‖ * d := by rw [map_mul, norm_mul]
    by_cases hne : ‖φ a‖ = ‖φ (b * δ)‖
    ·
      by_cases hb0 : φ b = 0
      · have ha0 : φ a = 0 := by
          rw [hnb, hb0, norm_zero, zero_mul] at hne
          exact norm_eq_zero.1 hne
        rw [hy', map_add (f := _), map_mul, ha0, hb0, zero_mul, add_zero, norm_zero]
        exact hd0
      · exfalso
        have ha0 : φ a ≠ 0 := by
          intro h
          rw [hnb, h, norm_zero] at hne
          have : 0 < ‖φ b‖ * d := mul_pos (norm_pos_iff.2 hb0) hdpos
          linarith
        obtain ⟨k, hk⟩ := Formalism.L2.Th1.D.kurUnram p _ (hK _ hsa) ha0
        obtain ⟨m, hm⟩ := Formalism.L2.Th1.D.kurUnram p _ (hK _ hsb) hb0
        have h2 : (‖φ a‖) ^ 2 = (‖φ b‖) ^ 2 * q := by
          rw [hne, hnb, mul_pow, hdq]
        rw [hk, hm, ← hq] at h2
        have h3 : q ^ (2 * k) = q ^ (2 * m + 1) := by
          rw [zpow_add₀ hq0.ne', zpow_one, mul_comm 2 k, mul_comm 2 m, zpow_mul, zpow_mul]
          exact_mod_cast h2
        have h4 := zpow_right_injective₀ hq0 hq1.ne h3
        omega
    · have hmax : ‖φ (y : E)‖ = max ‖φ a‖ ‖φ (b * δ)‖ := by
        rw [hy', map_add (f := _)]
        exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rw [hmax] at hy ⊢
      have hA : ‖φ a‖ < 1 := (le_max_left _ _).trans_lt hy
      have hB : ‖φ (b * δ)‖ < 1 := (le_max_right _ _).trans_lt hy
      refine max_le ?_ ?_
      · have := kur_step (hK _ hsa) 0 (by simpa using hA)
        rw [zero_add, zpow_one] at this
        exact this.trans hqd
      · rw [hnb] at hB ⊢
        exact mul_le_of_le_one_left hd0 (key _ (hK _ hsb) hB.le)

end Formalism.L2.Th1.GD
end
end

