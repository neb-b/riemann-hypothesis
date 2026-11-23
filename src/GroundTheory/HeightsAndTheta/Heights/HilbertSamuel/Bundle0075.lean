module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsHomogeneousComponentNeZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatNoetherFrame
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjAvoidingForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ProjAvoidingForm

noncomputable section

theorem ProjAvoidingForm.constantCoeff_homogeneousComponent {σ : Type} {G : MvPolynomial σ ℚ} {d : ℕ}
    (hd : 0 < d) : constantCoeff (homogeneousComponent d G) = 0 := by
  show AddMonoidAlgebra.coeff (homogeneousComponent d G) 0 = 0
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · simp at h
    omega
  · rfl

theorem ProjAvoidingForm.proof (hSeg : SegreArith.Statement) : ProjAvoidingForm.Statement := by
  intro K _ ι _ Ω _ y D df f hV hf hfP
  classical
  have hV' := hV
  obtain ⟨-, ⟨hprime, -, hrelv⟩, hhor, -⟩ := hV'

  have : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have h1 : ((n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, map_intCast, Int.cast_natCast,
        ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    have h2 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simpa using h1
    rw [hhor] at h2
    exact_mod_cast Ideal.mem_bot.mp h2

  have hx := hSeg K ι Ω y D hV
  set x := segreCoords y with hxdef
  obtain ⟨B, e, ⟨B', hB'⟩, hF⟩ := RatNoetherFrame.proof D Ω ((k : K) → ι k) x hx
  set x' := matAct B x with hx'def
  set w : Fin (D + 1) → Ω := x' ∘ e with hwdef
  set R₀ := coneRing ℚ w
  have hBB : ∀ p l, ∑ i, B' p i * B i l = if p = l then 1 else 0 := by
    intro p l
    have := congrFun (hB' (Pi.single l 1)).2 p
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using this
  have hxinv : ∀ p, x p = ∑ i, (B' p i : Ω) * x' i := by
    intro p
    simp only [hx'def, matAct, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have h1 : ∀ l, (∑ i, (B' p i : Ω) * (B i l : Ω)) = if p = l then 1 else 0 := fun l => by
      have := congrArg (fun q : ℚ => (q : Ω)) (hBB p l)
      push_cast at this
      rw [this]
      split_ifs <;> simp
    simp [h1]

  have hlin : ∀ c : Ix ((k : K) → ι k) → ℚ,
      (∑ i, C (c i) * X i : MvPolynomial (Ix ((k : K) → ι k)) ℚ).IsHomogeneous 1 :=
    fun c => IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X _ _).C_mul _
  have hint : ∀ p, IsIntegral R₀ (Polynomial.C (x p) * Polynomial.X) := by
    intro p
    have := isIntegral_coneMap x' R₀ hF.integral (∑ i, C (B' p i) * X i)
    rw [coneMap_of_isHomogeneous ℚ x' (hlin _), pow_one] at this
    convert this using 2
    rw [hxinv p]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]

  let ℓq : Fin (D + 1) → MvPolynomial (Ix ((k : K) → ι k)) ℚ := fun j => ∑ i, C (B (e j) i) * X i
  have hℓhom : ∀ j, (ℓq j).IsHomogeneous 1 := fun j => hlin _
  have hℓx : ∀ j, aeval x (ℓq j) = w j := fun j => by
    simp [ℓq, hwdef, hx'def, matAct]
  set N : ℕ := ∏ j, ∏ i, (B (e j) i).den with hNdef
  have hN : (N : ℚ) ≠ 0 := by
    rw [hNdef]
    exact_mod_cast Finset.prod_ne_zero_iff.mpr fun j _ =>
      Finset.prod_ne_zero_iff.mpr fun i _ => (B (e j) i).den_nz
  have hden : ∀ j i, ∃ n : ℤ, (n : ℚ) = (N : ℚ) * B (e j) i := by
    intro j i
    obtain ⟨r, hr⟩ : (B (e j) i).den ∣ N :=
      (Finset.dvd_prod_of_mem (fun i => (B (e j) i).den) (Finset.mem_univ i)).trans
        (Finset.dvd_prod_of_mem (fun j => ∏ i, (B (e j) i).den) (Finset.mem_univ j))
    refine ⟨r * (B (e j) i).num, ?_⟩
    rw [hr]
    have hq := Rat.num_div_den (B (e j) i)
    have hd : ((B (e j) i).den : ℚ) ≠ 0 := by exact_mod_cast (B (e j) i).den_nz
    have h3 : ((B (e j) i).num : ℚ) = B (e j) i * (B (e j) i).den := (div_eq_iff hd).mp hq
    push_cast
    rw [h3]
    ring
  choose n hn using hden
  let L : Fin (D + 1) → MRing ι := fun j => segreSub (∑ i, C (n j i) * X i)
  have hLhom : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) (fun _ => 1) := fun j => isMultiHomog_segreSub_linear (n j)
  have hLz : ∀ (z : (Σ k, ι k) → ℂ) j,
      eval z (map (Int.castRingHom ℂ) (L j)) = (N : ℂ) * aeval (segreCoords z) (ℓq j) := by
    intro z j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [L, ℓq, eval_segreSub, map_sum, map_mul, map_C, map_X, eval_X, eval_C, aeval_C, aeval_X,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrArg (fun q : ℚ => (q : ℂ)) (hn j i)
    push_cast at this
    simp [this, mul_assoc]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN

  have hnz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0 := by
    intro z hz
    by_contra hall
    push Not at hall
    have hℓ0 : (fun j => aeval (segreCoords z) (ℓq j)) = 0 := funext fun j => by
      have := hLz z j
      rw [hall j] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hNC
    have hu0 : ∀ p, segreCoords z p = 0 := by
      intro p
      have hα : IsIntegral R₀ (coneMap ℚ x (X p)) := isIntegral_coneMap x R₀ hint (X p)
      have hg : ∀ k, ∃ g, coneMap ℚ w g = ((minpoly R₀ (coneMap ℚ x (X p))).coeff k : Polynomial Ω) :=
        fun k => (AlgHom.mem_range _).mp ((minpoly R₀ (coneMap ℚ x (X p))).coeff k).2
      choose g hg using hg
      have hrel := key_relation y w ℓq hℓhom hℓx (isHomogeneous_X ℚ p) _ (minpoly.aeval R₀ _) g hg
        (minpoly R₀ (coneMap ℚ x (X p))).natDegree hz
      simp only [← hxdef] at hrel
      rw [hℓ0, Finset.sum_range_succ, Finset.sum_eq_zero fun k hk => by
        rw [Finset.mem_range] at hk
        rw [if_pos (by omega), aeval_zero, constantCoeff_homogeneousComponent (by omega), map_zero, mul_zero],
        zero_add, if_pos (by omega), one_mul, Nat.sub_self, aeval_zero, homogeneousComponent_zero, constantCoeff_C] at hrel
      have htop : AddMonoidAlgebra.coeff (g (minpoly R₀ (coneMap ℚ x (X p))).natDegree) 0 = 1 := by
        have h1 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 0) (hg (minpoly R₀ (coneMap ℚ x (X p))).natDegree)
        simp only [coeff_coneMap, homogeneousComponent_zero, aeval_C] at h1
        rw [(minpoly.monic hα).coeff_natDegree] at h1
        simp only [OneMemClass.coe_one, Polynomial.coeff_one_zero] at h1
        exact (algebraMap ℚ Ω).injective (h1.trans (map_one _).symm)
      rw [htop, map_one, mul_one] at hrel
      simpa using eq_zero_of_pow_eq_zero hrel
    obtain ⟨c, hc⟩ : ∃ c : (k : K) → ι k, ∀ k, z ⟨k, c k⟩ ≠ 0 :=
      ⟨fun k => (hz.1 k).choose, fun k => (hz.1 k).choose_spec⟩
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hc k) (hu0 ⟨(), c⟩)

  choose ic hic using hrelv
  obtain ⟨F, hFhom, hFeq⟩ := exists_segre_form hf ic
  have hW : (∏ k, (X ⟨k, ic k⟩ : MRing ι) ^ (∑ k', df k' - df k)) ∉ mCoordIdeal y := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := mCoordIdeal y)).mp h
    exact hic k (hprime.mem_of_pow_mem _ hk)
  have hα0 : coneMap ℚ x (qmap F) ≠ 0 := by
    intro h
    rw [coneMap_qmap] at h
    have := segreSub_mem y (Q := F) (RingHom.mem_ker.mpr h)
    rw [hFeq] at this
    rcases hprime.mem_or_mem this with h1 | h1
    · exact hfP h1
    · exact hW h1
  have hαint : IsIntegral R₀ (coneMap ℚ x (qmap F)) := isIntegral_coneMap x R₀ hint (qmap F)
  have hg : ∀ k, ∃ g, coneMap ℚ w g = ((minpoly R₀ (coneMap ℚ x (qmap F))).coeff k : Polynomial Ω) :=
    fun k => (AlgHom.mem_range _).mp ((minpoly R₀ (coneMap ℚ x (qmap F))).coeff k).2
  choose g hg using hg
  have hg0 : g 0 ≠ 0 := by
    intro h
    have h1 := hg 0
    rw [h, map_zero] at h1
    exact minpoly_coeff_zero_ne hαint hα0 (Subtype.ext h1.symm)
  obtain ⟨d, hd⟩ := exists_homogeneousComponent_ne_zero hg0
  obtain ⟨M, hM, G, hG⟩ := exists_int_mul_eq_qmap (homogeneousComponent d (g 0))
  refine ⟨fun _ => 1, L, G, fun _ => le_rfl, hLhom, hnz, ?_, ?_⟩
  · rintro rfl
    rw [map_zero, mul_eq_zero] at hG
    rcases hG with h | h
    · exact hM (by exact_mod_cast h)
    · exact hd h
  · rintro ζ hGζ z hz ⟨t, ht⟩ hfz
    have hrel := key_relation y w ℓq hℓhom hℓx (hFhom.map (Int.castRingHom ℚ)) _ (minpoly.aeval R₀ _) g hg d hz
    simp only [← hxdef] at hrel
    have hFu : aeval (segreCoords z) (qmap F) = 0 := by
      rw [aeval_qmap, ← eval_segreSub, hFeq, map_mul, eval_mul, hfz, zero_mul]
    rw [Finset.sum_eq_single 0 (fun k _ hk => by rw [hFu, zero_pow hk]; simp) (by simp)] at hrel
    simp only [mul_zero, zero_le, if_true, pow_zero, one_mul, Nat.sub_zero] at hrel
    have hℓu : (fun j => aeval (segreCoords z) (ℓq j)) = fun j => (t / N) * ζ j := funext fun j => by
      have := hLz z j
      rw [ht j] at this
      field_simp
      linear_combination this.symm
    rw [hℓu, aeval_mul_of_isHomogeneous (homogeneousComponent_isHomogeneous d (g 0))] at hrel
    have hG1 : aeval ζ (homogeneousComponent d (g 0)) ≠ 0 := by
      intro h
      apply hGζ
      rw [← aeval_qmap, ← hG, map_mul, h, mul_zero]
    have ht0 : t ≠ 0 := by
      rintro rfl
      obtain ⟨j, hj⟩ := hnz z hz
      exact hj (by rw [ht j, zero_mul])
    rcases mul_eq_zero.mp hrel with h | h
    · exact pow_ne_zero _ (div_ne_zero ht0 hNC) h
    · exact hG1 h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelOneStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelOneStep

theorem chart_monomial_mem {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) (c : ∀ k, ι k) :
    ∏ k, y ⟨k, c k⟩ ^ b k ∈ relSecM R y b := by
  classical
  let μ : (Σ k, ι k) → ℕ := fun p => if p.2 = c p.1 then b p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = b k := by
    intro k
    simp [μ]
  have h := monomial_mem_relSecM R y μ hμ
  have heq : ∏ p, y p ^ μ p = ∏ k, y ⟨k, c k⟩ ^ b k := by
    rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [μ]
    rw [Finset.prod_congr rfl fun i _ => (show y ⟨k, i⟩ ^ (if i = c k then b k else 0) =
      if i = c k then y ⟨k, i⟩ ^ b k else 1 by split_ifs <;> simp)]
    simp
  rwa [heq] at h

end RelOneStep

theorem RelOneStep.proof (hC : RelChartPoly.Statement) (hT : RelTorsionBound.Statement) : RelOneStep.Statement := by
  intro K _ _ ι _ Ω _ R hR y c0 hc0
  choose n hn using fun k0 : K => hT K ι Ω R hR y c0 hc0 k0
  refine ⟨Finset.univ.sup n, fun b hb k0 t ht hxt => ?_⟩
  have hbk : ∀ k, n k0 ≤ b k := fun k => le_trans (Finset.le_sup (Finset.mem_univ k0)) (hb k)
  obtain ⟨g', hg', hfg⟩ := hn k0 b hbk (y ⟨k0, c0 k0⟩ * t) hxt (by
    intro c hc
    obtain ⟨N, hN⟩ := hC K ι Ω R y c _ (ht c hc)
    refine ⟨N, t * (∏ k, y ⟨k, c k⟩) ^ N, ?_, by ring⟩
    have hm := mul_mem_relSecM R y hN (RelOneStep.chart_monomial_mem R y b c)
    have hone : (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * ∏ k, y ⟨k, c k⟩ ^ b k = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← zpow_natCast, ← zpow_add₀ (hc k)]
      simp
    have heq : t * (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * (∏ k, y ⟨k, c k⟩) ^ N *
        ∏ k, y ⟨k, c k⟩ ^ b k = t * (∏ k, y ⟨k, c k⟩) ^ N := by
      linear_combination (t * (∏ k, y ⟨k, c k⟩) ^ N) * hone
    rw [heq, add_comm] at hm
    exact hm)
  have hx : y ⟨k0, c0 k0⟩ ≠ 0 := hc0 k0
  rwa [mul_left_cancel₀ hx hfg]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelSectionsLarge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelSectionsLarge

theorem chartMonomial_mem_relSecM {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (b : K → ℕ) :
    ∏ k, y ⟨k, c0 k⟩ ^ b k ∈ relSecM R y b := by
  classical
  have h := monomial_mem_relSecM R y (b := b) (fun p => if p.2 = c0 p.1 then b p.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (c0 k) (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem descend {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (n₁ : ℕ)
    (hstep : ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → ∀ k0 : K,
      ∀ t ∈ relChartLat R y (fun k => (b k : ℤ)) 1, y ⟨k0, c0 k0⟩ * t ∈ relSecM R y (b + Pi.single k0 1) →
        t ∈ relSecM R y b) :
    ∀ (m : ℕ) (e : K → ℕ), ∑ k, e k = m → ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ s ∈ relChartLat R y (fun k => (b k : ℤ)) 1,
        s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relSecM R y (b + e) → s ∈ relSecM R y b := by
  intro m
  induction m with
  | zero =>
    intro e he b _ s _ hs
    have h0 : e = 0 := funext fun k => by
      simpa using (Finset.sum_eq_zero_iff.mp he) k (Finset.mem_univ k)
    subst h0
    simpa using hs
  | succ m ih =>
    intro e he b hb s hsL hs
    obtain ⟨k0, hk0⟩ : ∃ k0, 0 < e k0 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have : ∑ k, e k = 0 := Finset.sum_eq_zero fun k _ => Nat.le_zero.mp (hcon k)
      omega
    set e' : K → ℕ := e - Pi.single k0 1 with he'
    have hee : e = e' + Pi.single k0 1 := by
      funext k
      simp only [he', Pi.add_apply, Pi.sub_apply]
      by_cases hk : k = k0
      · subst hk; simp; omega
      · simp [hk]
    have hsum : ∑ k, e' k = m := by
      have : ∑ k, e k = ∑ k, e' k + 1 := by
        rw [hee]; simp only [Pi.add_apply]; rw [Finset.sum_add_distrib]; simp
      omega
    refine ih e' hsum b hb s hsL ?_
    have htL : s * ∏ k, y ⟨k, c0 k⟩ ^ e' k ∈ relChartLat R y (fun k => ((b + e') k : ℤ)) 1 :=
      mul_prod_mem_relChartLat R y (a := fun k => (b k : ℤ)) (a' := fun k => ((b + e') k : ℤ)) (n := 1) e' c0
        (fun k => by simp only [Pi.add_apply]; push_cast; ring) hsL
    have hb' : ∀ k, n₁ ≤ (b + e') k := fun k => le_trans (hb k) (Nat.le_add_right _ _)
    refine hstep (b + e') hb' k0 _ htL ?_
    have hprod : y ⟨k0, c0 k0⟩ * (s * ∏ k, y ⟨k, c0 k⟩ ^ e' k) = s * ∏ k, y ⟨k, c0 k⟩ ^ e k := by
      rw [hee]
      have h1 : ∏ k, y ⟨k, c0 k⟩ ^ (Pi.single k0 1 : K → ℕ) k = y ⟨k0, c0 k0⟩ := by
        rw [Fintype.prod_eq_single k0 (fun k hk => by simp [hk])]
        simp
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, h1]
      ring
    rw [hprod, add_assoc, ← hee]
    exact hs

theorem proof (hC : RelChartPoly.Statement) (hO : RelOneStep.Statement) : RelSectionsLarge.Statement := by
  classical
  intro K _ ι _ Ω _ R hR y hy
  choose c0 hc0 using hy
  obtain ⟨n₁, hn₁⟩ := hO K ι Ω R hR y c0 hc0
  refine ⟨n₁, fun b hb s hs => ?_⟩
  obtain ⟨N, hN⟩ := hC K ι Ω R y c0 _ (hs c0 hc0)
  have hform := mul_mem_relSecM R y hN (chartMonomial_mem_relSecM R y c0 b)
  refine descend R y c0 n₁ hn₁ (∑ _k : K, N) (fun _ => N) rfl b hb s hs ?_
  rw [add_comm]
  convert hform using 1
  have hcancel : (∏ k, y ⟨k, c0 k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ)))) * ∏ k, y ⟨k, c0 k⟩ ^ b k = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [Nat.cast_one, one_mul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hc0 k))]
  rw [← Finset.prod_pow]
  linear_combination (-(s * ∏ k, y ⟨k, c0 k⟩ ^ N)) * hcancel

end RelSectionsLarge

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ShiftDegreePolynomial

def toMultilinear {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y)) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => K → ℤ) ℤ where
  toFun := f
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact hadd m i x y
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact (AddMonoidHom.mk' (fun x => f (Function.update m i x)) (hadd m i)).map_zsmul c x

theorem expand {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (q : ℤ) (a b : K → ℤ) :
    f (fun _ => q • a + b) =
      ∑ s : Finset (Fin n), q ^ s.card * f (s.piecewise (fun _ => a) (fun _ => b)) := by
  have h1 := (toMultilinear f hadd).map_add_univ (fun _ => q • a) (fun _ => b)
  refine h1.trans (Finset.sum_congr rfl fun s _ => ?_)
  have h2 := (toMultilinear f hadd).map_piecewise_smul (fun _ => q)
    (s.piecewise (fun _ => a) (fun _ => b)) s
  have h3 : s.piecewise (fun i => q • s.piecewise (fun _ => a) (fun _ => b) i)
      (s.piecewise (fun _ => a) (fun _ => b)) = s.piecewise (fun _ => q • a) (fun _ => b) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [h3, Finset.prod_const, RingHom.id_apply, smul_eq_mul] at h2
  exact h2

theorem genericFibre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (P.map (MvPolynomial.map (Int.castRingHom ℚ))) ∧
      ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
        ((D + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : P.IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have h1 : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hchar
  have hq : ReciprocityTheory.AnForm.R.extQ P = P.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq _ _ ?_
    rw [hform]
    push_cast
    ring

theorem proof (h : MixedNumberPolynomial.Statement.{0}) : ShiftDegreePolynomial.Statement := by
  classical
  intro K _ ι _ P D a b hP
  obtain ⟨hprime, hdimq⟩ := genericFibre hP
  set Q := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hQ
  have hadd := (h ℚ K ι Q D hprime hdimq).2
  let f : (Fin D → K → ℤ) → ℤ := fun bs => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ Q bs
  let c : Finset (Fin D) → ℤ := fun s => f (s.piecewise (fun _ => a) (fun _ => b))
  refine ⟨∑ s : Finset (Fin D), Polynomial.C (c s : ℝ) * Polynomial.X ^ s.card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    simpa using Finset.card_le_univ s
  · rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single Finset.univ]
    · simp [c, f, genDeg, hQ]
    · intro s _ hs
      rw [if_neg]
      intro hD
      apply hs
      rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
      exact hD.symm
    · intro hu
      exact absurd (Finset.mem_univ _) hu
  · intro q
    have hexp := expand f hadd (q : ℤ) a b
    have hg : genDeg P D ((q : ℤ) • a + b) = f (fun _ => (q : ℤ) • a + b) := rfl
    rw [hg, hexp, Polynomial.eval_finsetSum]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [c, mul_comm]

end ShiftDegreePolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

