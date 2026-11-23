module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0019
public import Formalism.LocalRingCardinality.DataCD

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeSelfDual
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.LatSelfDual

theorem ee_neg_eq_one_iff (t : ℝ) : ee (-t) = 1 ↔ ∃ m : ℤ, t = m := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [mul_comm (n : ℂ)] at hn
    have h3 := mul_left_cancel₀ h2 hn
    have h4 : (-t : ℝ) = (n : ℝ) := by exact_mod_cast h3
    push_cast
    linarith
  · rintro ⟨m, rfl⟩
    refine ⟨-m, ?_⟩
    push_cast
    ring

theorem gamA_add_left {D : D7} {ψ : AE D → ℂ} (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y) {N N' : ℕ} (ζ η ξ : XA D N N') :
    gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ := by
  simp only [gamA, ← hψ, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem gamA_add_right {D : D7} {ψ : AE D → ℂ} (hψ : ∀ x y, ψ (x + y) = ψ x * ψ y) {N N' : ℕ} (ζ η ξ : XA D N N') :
    gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ := by
  simp only [gamA, ← hψ, Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem gamA_rat {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {ψ : AE D → ℂ} (hψ : ∀ a, ψ (inc D a) = psi0 D cc δ a)
    {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    gamA ψ (z.map (inc D)) (y.map (inc D)) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  rw [← hψ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gamA, Matrix.map_apply, map_sum, map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]

theorem latA_selfDual (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hC : Crv D cc δ) (ψ : AE D → ℂ)
    (hψ : IsPsi D cc δ ψ) (N N' : ℕ) : SelfDual (gamA ψ) (latA D cc N N') := by
  obtain ⟨hadd, -, hrat, -, m₀, hm₀, h₀⟩ := hψ
  obtain ⟨l1, l2, l3, -, ⟨m₁, hm₁, h₁⟩, -⟩ := _root_.GlobalTheory.CompletedLattice.completed_lattice D hG cc δ hC N N'
  obtain ⟨w, -, hw⟩ := _root_.GlobalTheory.FinWeil.WdCocycle.wd_cocycle D hG cc δ hC
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, hL, h1, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
    exact h1 ▸ (hL 1).2
  obtain ⟨-, -, t1, t2, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩)
  have key : ∀ z y : Matrix (Fin N') (Fin N) D.host.E, gamA ψ (z.map (inc D)) (y.map (inc D)) = 1 ↔
      ∃ m : ℤ, (Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im = m := fun z y => by
    rw [gamA_rat hrat, ← (hw N N' z y).1, ee_neg_eq_one_iff]
  have hM : 0 < m₀ * m₁ * m₁ := by positivity
  have hs : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N',
      (∑ i, ∑ j, ((m₁ : AE D) * ζ i j) * sgA D ((m₁ : AE D) * η i j)) ∈ OhE D := fun ζ hζ η hη =>
    sum_mem fun i _ => sum_mem fun j _ => mul_mem (h₁ _ (hζ i j)) (Formalism.UG.P.csDual_sig_mem _ (h₁ _ (hη i j)))
  have dl : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ((m₀ * m₁ * m₁) • ζ) η = 1 := fun ζ hζ η hη => by
    rw [← h₀ _ (hs ζ hζ η hη), gamA]
    congr 1
    simp only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have dr : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ ((m₀ * m₁ * m₁) • η) = 1 := fun ζ hζ η hη => by
    rw [← h₀ _ (hs ζ hζ η hη), gamA]
    congr 1
    simp only [Finset.mul_sum, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have iso : ∀ ζ ∈ latA D cc N N', ∀ η ∈ latA D cc N N', gamA ψ ζ η = 1 := fun ζ hζ η hη => by
    obtain ⟨z, a, ha, hz⟩ := l3 ζ _ hM
    obtain ⟨y, b, hb, hy⟩ := l3 η _ hM
    have hzm : z.map (inc D) ∈ latA D cc N N' := hz ▸ add_mem hζ (nsmul_mem ha _)
    have hym : y.map (inc D) ∈ latA D cc N N' := hy ▸ add_mem hη (nsmul_mem hb _)
    have h := (key z y).2 (t1 _ ((l1 z).1 hzm) _ ((l1 y).1 hym))
    rwa [hz, gamA_add_left hadd, dl a ha _ hym, mul_one, hy, gamA_add_right hadd, dr ζ hζ b hb, mul_one] at h
  refine fun ζ => ⟨iso ζ, fun h => ?_⟩
  obtain ⟨z, a, ha, hz⟩ := l3 ζ 1 one_pos
  rw [one_smul] at hz
  have hzm : z.map (inc D) ∈ latA D cc N N' := by
    refine (l1 z).2 (t2 _ fun x hx => ?_)
    obtain ⟨y, rfl⟩ := l2 x hx
    have hym := (l1 y).2 hx
    rw [← key, hz, gamA_add_left hadd, h _ hym, iso a ha _ hym, mul_one]
  have : ζ = z.map (inc D) - a := by rw [hz, add_sub_cancel_right]
  rw [this]
  exact sub_mem hzm ha

end GlobalTheory.FinWeil.LatSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaDoubleTranslateMul
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Double

variable {Λ : AddSubgroup ℂ}

theorem exists_evenTheta_translate_mul_sq_comb (h : IsLat Λ) {t s : ℂ} (ht : t ∉ Λ) (h2 : 2 * t ∈ Λ) (hs : s ∉ Λ) :
    ∃ α γ : ℂ, ∀ w, GL3Theta.th0 Λ t (w + s) * GL3Theta.th0 Λ t (w - s) =
      α * GL3Theta.th0 Λ t w ^ 2 + γ * sgStar Λ w ^ 2 := by
  have hs0 := (h.sg_eq_zero s).not.2 hs
  have ht0 := (h.sg_eq_zero t).not.2 ht
  set E : ℂ → ℂ := fun u => Complex.exp (-(Real.pi : ℂ) * u * (starRingEnd ℂ) t / (area Λ : ℂ) -
    (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) with hE
  set K : ℂ := Complex.exp ((Real.pi : ℂ) * t * (starRingEnd ℂ) t / (area Λ : ℂ)) with hK
  set c : ℂ := U1 Λ t (sgStar Λ) 0 with hc
  have hθ : ∀ u, GL3Theta.th0 Λ t u = sgStar Λ (u + t) * E u * c⁻¹ := fun u => rfl
  refine ⟨-sgStar Λ s ^ 2 * (wpF Λ t - wpF Λ s),
    -sgStar Λ s ^ 2 * c⁻¹ ^ 2 * K / sgStar Λ t ^ 2, fun w => ?_⟩
  have e1 : E (w + s) * E (w - s) = E w ^ 2 := by
    simp only [hE]
    rw [sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have e2 : sgStar Λ (w + 2 * t) * E w ^ 2 = -K * sgStar Λ w := by
    have hl := h.sg_law h2 w
    rw [if_neg (by simpa using ht)] at hl
    rw [show -K * sgStar Λ w = (-1 * sgStar Λ w) * K by ring, ← hl]
    simp only [U1, hE, hK]
    rw [mul_assoc (sgStar Λ _), sq, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    simp only [map_mul, map_ofNat]
    ring
  have e3 := h.sqTh_sub hs ht (w + t)
  rw [sqTh, sqTh, show t + (w + t) = w + 2 * t by ring, show t - (w + t) = -w by ring,
    show s + (w + t) = w + s + t by ring, show s - (w + t) = -(w - s + t) by ring,
    h.sg_neg, h.sg_neg, div_eq_iff (pow_ne_zero 2 hs0)] at e3
  rw [hθ, hθ, hθ]
  linear_combination (sgStar Λ (w + s + t) * sgStar Λ (w - s + t) * c⁻¹ ^ 2) * e1 -
    (E w ^ 2 * c⁻¹ ^ 2) * e3 +
    (sgStar Λ s ^ 2 * c⁻¹ ^ 2 * sgStar Λ w / sgStar Λ t ^ 2) * e2

theorem evenTheta_double_translate_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ s, s ∉ Λ → ∀ z, U1 Λ s (sgStar Λ) 0 ^ 2 * (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) z * GL3Theta.th0 Λ t₀ z) = U1 Λ s (sgStar Λ) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 2 * U1 Λ s (GL3Theta.th0 Λ t₀) z ^ 2 + (U1 Λ (2 * s) (GL3Theta.th0 Λ t₀) 0 - U1 Λ s (GL3Theta.th0 Λ t₀) 0 ^ 4) * U1 Λ s (sgStar Λ) z ^ 2 := by
  intro Λ h t ht h2 s hs z
  obtain ⟨α, γ, hp⟩ := exists_evenTheta_translate_mul_sq_comb h ht h2 hs
  obtain ⟨-, h1, hev, -⟩ := evenThetaTwoTorsion_basic_properties Λ h t ht h2
  have hα : α = GL3Theta.th0 Λ t s ^ 2 := by
    have := hp 0
    rw [zero_add, zero_sub, hev, h1, (h.sg_eq_zero 0).2 Λ.zero_mem] at this
    linear_combination -this
  set F : ℂ → ℂ := fun u => Complex.exp (-(Real.pi : ℂ) * u * (starRingEnd ℂ) s / (area Λ : ℂ) -
    (Real.pi : ℂ) * s * (starRingEnd ℂ) s / (2 * (area Λ : ℂ))) with hF
  have hU : ∀ (G : ℂ → ℂ) u, U1 Λ s G u = G (u + s) * F u := fun _ _ => rfl
  have hU2 : ∀ (G : ℂ → ℂ) u, U1 Λ (2 * s) G u = G (u + s + s) * (F u ^ 2 * F 0 ^ 2) := by
    intro G u
    simp only [U1, hF]
    rw [sq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    · ring
    · simp only [map_mul, map_ofNat]
      ring
  have p1 := hp (z + s)
  have p0 := hp (0 + s)
  rw [add_sub_cancel_right, hα] at p1 p0
  rw [h1] at p0
  simp only [hU, hU2]
  simp only [zero_add] at p0 ⊢
  linear_combination (sgStar Λ s ^ 2 * F 0 ^ 4 * F z ^ 2) * p1 -
    (F 0 ^ 4 * F z ^ 2 * sgStar Λ (z + s) ^ 2) * p0

end GlobalTheory.EvenTheta.Double
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaEqProdSigmaStarSquareQuotient
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

open Polynomial

variable {Λ : AddSubgroup ℂ}

theorem IsLat.wpF_add_of_mem (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem IsLat.entire_eq_of_periodic (h : IsLat Λ) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hper : ∀ ω ∈ Λ, ∀ z, F (z + ω) = F z) (z : ℂ) : F z = F 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  exact hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hF.continuous
      fun z w hw => hper w ((hL w).2 hw) z).isBounded z 0

theorem IsLat.sqTh_law (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    sqTh Λ v (z + ω) * sgStar Λ z ^ 2 = sqTh Λ v z * sgStar Λ (z + ω) ^ 2 := by
  by_cases hz : z ∈ Λ
  · rw [(h.sg_eq_zero z).2 hz, (h.sg_eq_zero _).2 (add_mem hz hω)]
    simp
  · have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using sub_mem h' hω)
    rw [h.sqTh_eq hv hz, h.sqTh_eq hv hz', h.wpF_add_of_mem hω]
    ring

theorem IsLat.exists_poly_wp (h : IsLat Λ) (k : ℕ) : ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ z, F (-z) = F z) →
    (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) →
    ∃ P : ℂ[X], P.natDegree ≤ k ∧ P.coeff k = F 0 ∧
      ∀ z ∉ Λ, F z = sgStar Λ z ^ (2 * k) * P.eval (wpF Λ z) := by
  induction k with
  | zero =>
    intro F hF _ hlaw
    refine ⟨C (F 0), by simp, by simp, fun z _ => ?_⟩
    simpa using h.entire_eq_of_periodic hF (fun ω hω z => by simpa using hlaw ω hω z) z
  | succ k ih =>
    intro F hF he hlaw
    obtain ⟨v, hv⟩ := h.dense_compl.nonempty
    have hv : v ∉ Λ := hv
    have hd := h.differentiable_sqTh v
    obtain ⟨G, hG, hGe, hFG, hGl⟩ := GlobalTheory.EvenTheta.exists_eq_sg_sq_mul Λ h k
      (fun z => F z - F 0 * sqTh Λ v z ^ (k + 1)) (by fun_prop)
      (fun z => by simp only [he, sqTh_neg]) (by simp [h.sqTh_zero hv])
      (fun ω hω z => by
        have h1 := congrArg (· ^ (k + 1)) (h.sqTh_law hv hω z)
        simp only [mul_pow, ← pow_mul] at h1
        linear_combination hlaw ω hω z - F 0 * h1)
    obtain ⟨P, hP, -, hPG⟩ := ih G hG hGe hGl
    have hm : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).Monic := (monic_X_sub_C _).pow _
    have hdeg : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).natDegree = k + 1 := by
      rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    refine ⟨C (F 0) * (X - C (wpF Λ v)) ^ (k + 1) + P, ?_, ?_, fun z hz => ?_⟩
    · refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hdeg.le) (by omega)
    · have h1 := hm.coeff_natDegree
      rw [hdeg] at h1
      rw [coeff_add, coeff_C_mul, h1, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k + 1)]
      simp
    · have h1 := hFG z
      simp only [hPG z hz, h.sqTh_eq hv hz, mul_pow, ← pow_mul] at h1
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
      linear_combination h1

theorem exists_eval_eq_prod_fin {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) (h1 : P.coeff k = 1) :
    ∃ r : Fin k → ℂ, ∀ x, P.eval x = ∏ i, (x - r i) := by
  have hdeg : P.natDegree = k := natDegree_eq_of_le_of_coeff_ne_zero hP (by rw [h1]; exact one_ne_zero)
  have hm : P.Monic := by rw [Monic, leadingCoeff, hdeg, h1]
  have hs : P.Splits := IsAlgClosed.splits P
  have he := hs.eq_prod_roots_of_monic hm
  have hc := hs.natDegree_eq_card_roots
  obtain ⟨l, hl⟩ := Quotient.exists_rep P.roots
  have hl : (l : Multiset ℂ) = P.roots := hl
  rw [← hl] at he hc
  rw [hdeg, Multiset.coe_card] at hc
  subst hc
  refine ⟨fun i => l[i.1]'i.2, fun x => ?_⟩
  rw [he, eval_multiset_prod, Multiset.map_map, Multiset.map_coe, Multiset.prod_coe]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  exact (Fin.prod_univ_fun_getElem l fun a => x - a).symm

theorem exists_eq_prod_sqTh : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 1 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ) ∧ ∀ z, F z = ∏ i, sqTh Λ (Q i) z := by
  intro Λ h k F hF he h0 hlaw
  obtain ⟨P, hP, hc, hPF⟩ := h.exists_poly_wp k F hF he hlaw
  obtain ⟨r, hr⟩ := exists_eval_eq_prod_fin hP (hc.trans h0)
  choose Q hQ hQr using fun i => GlobalTheory.EvenTheta.exists_wpF_eq Λ h (r i)
  refine ⟨Q, hQ, fun z => ?_⟩
  refine congrFun (Continuous.ext_on h.dense_compl hF.continuous
    (g := fun z => ∏ i, sqTh Λ (Q i) z)
    (continuous_finsetProd _ fun i _ => (h.differentiable_sqTh (Q i)).continuous) fun z hz => ?_) z
  have hz : z ∉ Λ := hz
  beta_reduce
  simp only [h.sqTh_eq (hQ _) hz, hQr, hPF z hz, hr, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCentralCircleDistinctGradedEigen
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GradedCentralCircle

open GlobalTheory.RealPar

variable {p q : ℕ}

theorem flow_eq {T : GrpData p q} (σ : URep T) {X : Mat p q} (hX : X ∈ upq p q) {w : σ.H} {c : ℂ}
    (h0 : HasDerivAt (fun t : ℝ => σ.π (T.expt (t • X)) w) (c • w) 0) :
    σ.π (T.expt X) w = Complex.exp c • w := by
  set f : ℝ → σ.H := fun t => σ.π (T.expt (t • X)) w with hf
  have hd : ∀ t, HasDerivAt f (c • f t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) (c • w) t := by
      have := HasDerivAt.comp_sub_const t t (f := f) (f' := c • w) (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((σ.π (T.expt (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    convert (preTransparency := .reducible) h2 using 1
    · funext s
      simp only [hf, Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    · simp [hf]
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    convert h1.fun_smul (hd t) using 1
    rw [smul_smul, ← add_smul]; simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, ContinuousLinearMap.one_apply] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem exp_injective (c : ℂ) : Function.Injective fun m : ℕ => Complex.exp (Complex.I * (c + m)) := by
  intro m n h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h1 : ((m : ℝ) : ℂ) - (n : ℝ) = ((k : ℝ) * 2 * Real.pi : ℝ) := by
    push_cast
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination hk
  have h2 : (m : ℝ) - n = (k : ℝ) * 2 * Real.pi := by exact_mod_cast h1
  by_cases hk0 : k = 0
  · subst hk0
    have : (m : ℝ) = n := by simpa [sub_eq_zero] using h2
    exact_mod_cast this
  · exfalso
    have hi : Irrational (((k * 2 : ℤ) : ℝ) * Real.pi) :=
      irrational_pi.intCast_mul (by omega)
    have : ((k * 2 : ℤ) : ℝ) * Real.pi = ((m - n : ℤ) : ℝ) := by push_cast; linarith
    rw [this] at hi
    exact Int.not_irrational _ hi

theorem exists_central_eigen : ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (c : ℚ), (∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, M.act (Eab (Sum.inl i) (Sum.inl i)) x = ((c : ℂ) + m) • x) → ∃ k ∈ T.Kset, ∃ lam : ℕ → ℂ, Function.Injective lam ∧ ∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x := by
  intro p q T σ M j hj N c hN
  set θ : Ix p q → ℝ := Sum.elim (fun _ => 1) (fun _ => 0) with hθ
  have hX := TorusWt.torX_mem θ
  have hK : IsKC (TorusWt.torX θ) := by
    intro a b hab
    have : a ≠ b := by
      rintro rfl
      cases a <;> simp [sameBlock] at hab
    simp [TorusWt.torX, this]
  have hk := KStabLie.expt_mem T hX hK 1
  rw [one_smul] at hk
  refine ⟨_, hk, _, exp_injective (c : ℂ), fun m x hx => ?_⟩
  apply flow_eq σ hX
  have h0 := hj _ hX x
  have h1 : M.act (TorusWt.torX θ) x = (Complex.I * ((c : ℂ) + m)) • x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [TorusWt.torX_eq_sum, map_sum, LinearMap.sum_apply, Fintype.sum_sum_type, mul_smul, ← hN m x hx,
      Finset.smul_sum]
    simp [hθ]
  rw [h1, map_smul] at h0
  exact h0

end GlobalTheory.GradedCentralCircle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpBallUMemNhds
section
open Formalism.BasicNotions MeasureTheory Filter Topology

namespace GlobalTheory.ExpBallNhds

theorem exp_local_algebra (A : Type) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    (∃ S ∈ 𝓝 (0 : A), Set.InjOn (NormedSpace.exp : A → A) S) ∧
      Filter.map (NormedSpace.exp : A → A) (𝓝 0) = 𝓝 1 := by
  have h : HasStrictFDerivAt (NormedSpace.exp : A → A)
      ((ContinuousLinearEquiv.refl ℂ A : A ≃L[ℂ] A) : A →L[ℂ] A) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := A)
  refine ⟨⟨(h.toOpenPartialHomeomorph _).source, ?_, ?_⟩, ?_⟩
  · exact (h.toOpenPartialHomeomorph _).open_source.mem_nhds h.mem_toOpenPartialHomeomorph_source
  · have := (h.toOpenPartialHomeomorph _).injOn
    simpa using this
  · have := h.map_nhds_eq_of_equiv
    rwa [NormedSpace.exp_zero] at this

theorem exp_local_matrix (n : Type) [Fintype n] [DecidableEq n] :
    (∃ S ∈ 𝓝 (0 : Matrix n n ℂ), Set.InjOn (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) S) ∧
      Filter.map (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) (𝓝 0) = 𝓝 1 := by
  let : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  exact exp_local_algebra (Matrix n n ℂ)

open MeasureTheory Filter Topology in
private theorem exists_local_homeomorph_matrix_exp_source_zero {n : Type} [Fintype n] [DecidableEq n] :
    ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
      (0 : Matrix n n ℂ) ∈ e.source ∧ ⇑e = NormedSpace.exp := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)) 0 :=
    hasStrictFDerivAt_exp_zero
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source,
    hf.toOpenPartialHomeomorph_coe⟩


open MeasureTheory Filter Topology in
open Matrix in
theorem _root_.GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds : ∀ (P Q : ℕ) (r : ℝ), 0 < r →
    {g : _root_.Formalism.BasicNotions.UpqT P Q | ∃ X ∈ _root_.Formalism.BasicNotions.ballU P Q r,
      _root_.Formalism.BasicNotions.UpqT.mat g = NormedSpace.exp (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} ∈
      𝓝 (1 : _root_.Formalism.BasicNotions.UpqT P Q) := by
  intro P Q r hr
  obtain ⟨e, h0, he⟩ := exists_local_homeomorph_matrix_exp_source_zero (n := Fin P ⊕ Fin Q)
  set J := _root_.Formalism.UG.Jpq P Q with hJ
  have hJJ : J * J = 1 := by
    rw [hJ]; unfold _root_.Formalism.UG.Jpq; simp [fromBlocks_multiply]
  have hJinv : J⁻¹ = J := Matrix.inv_eq_right_inv hJJ
  have hJunit : IsUnit J := ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
  set σ : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
    fun X => -(J * Xᴴ * J) with hσ
  have hσc : Continuous σ := by
    rw [hσ]
    exact ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
      continuous_const).neg
  have hσ0 : σ 0 = 0 := by simp [hσ]
  set N : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := {X | ∑ i, ∑ j, ‖X i j‖ < r} with hN
  have hNo : IsOpen N := isOpen_lt (by fun_prop) continuous_const
  have hU : e.source ∩ σ ⁻¹' e.source ∩ N ∈ 𝓝 (0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
    refine ((e.open_source.inter (e.open_source.preimage hσc)).inter hNo).mem_nhds ⟨⟨h0, ?_⟩, ?_⟩
    · show σ 0 ∈ e.source
      rw [hσ0]; exact h0
    · show ∑ i, ∑ j, ‖(0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i j‖ < r
      simpa using hr
  have himg := e.image_mem_nhds h0 hU
  rw [he, NormedSpace.exp_zero] at himg
  have hmat : Continuous (fun g : _root_.Formalism.BasicNotions.UpqT P Q => _root_.Formalism.BasicNotions.UpqT.mat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hpre : (fun g : _root_.Formalism.BasicNotions.UpqT P Q => _root_.Formalism.BasicNotions.UpqT.mat g) ⁻¹'
      (NormedSpace.exp '' (e.source ∩ σ ⁻¹' e.source ∩ N)) ∈ 𝓝 (1 : _root_.Formalism.BasicNotions.UpqT P Q) :=
    hmat.continuousAt.preimage_mem_nhds himg
  filter_upwards [hpre] with g hg
  obtain ⟨X, ⟨⟨hXs, hσXs⟩, hXN⟩, hgX⟩ := hg
  beta_reduce at hgX
  have hgU : (_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g = J := g.2
  have hexpσ : NormedSpace.exp (σ X) = NormedSpace.exp X := by
    have hleft : J * (_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g = 1 := by
      rw [show J * (_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g = J * ((_root_.Formalism.BasicNotions.UpqT.mat g)ᴴ * J * _root_.Formalism.BasicNotions.UpqT.mat g)
        by simp only [mul_assoc], hgU, hJJ]
    rw [hσ]
    show NormedSpace.exp (-(J * Xᴴ * J)) = _
    have hc := Matrix.exp_conj J Xᴴ hJunit
    rw [hJinv] at hc
    rw [Matrix.exp_neg, hc, Matrix.exp_conjTranspose, hgX, Matrix.inv_eq_right_inv hleft]
  have hσX : σ X = X := e.injOn hσXs hXs (by rw [he]; exact hexpσ)
  have hJX : J * X = -(Xᴴ * J) := by
    conv_lhs => rw [← hσX]
    rw [hσ]
    show J * -(J * Xᴴ * J) = _
    rw [mul_neg, ← mul_assoc, ← mul_assoc, hJJ, one_mul]
  have hlie : X ∈ _root_.Formalism.BasicNotions.lieU P Q := by
    show Xᴴ * _root_.Formalism.UG.Jpq P Q + _root_.Formalism.UG.Jpq P Q * X = 0
    rw [← hJ, hJX, add_neg_cancel]
  exact ⟨⟨X, hlie⟩, hXN, hgX.symm⟩

end GlobalTheory.ExpBallNhds
end

