module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0010
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0176
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangePrimePowMemIsotypicDegreePolySpan
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory


open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds in
theorem degrees_eq_image_pairs {e : ℕ} (Sig : Finset (ZMod e)) (c : ZMod e) (m m' : ℕ) :
    degrees Sig c m m' =
      ((Sig.image fun s => (c - s).val) ×ˢ Finset.Ico m m').image (fun p : ℕ × ℕ => p.1 + p.2 * e) := by
  ext i
  simp only [degrees, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨s, n, ⟨hs, hn⟩, rfl⟩
    exact ⟨(c - s).val, n, ⟨⟨s, hs, rfl⟩, hn⟩, rfl⟩
  · rintro ⟨x, n, ⟨⟨s, hs, rfl⟩, hn⟩, rfl⟩
    exact ⟨s, n, ⟨hs, hn⟩, rfl⟩

theorem add_mul_inj_of_lt {e x y n m : ℕ} (hx : x < e) (hy : y < e) (h : x + n * e = y + m * e) :
    x = y ∧ n = m := by
  have h1 : (x + n * e) % e = x := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have h2 : (y + m * e) % e = y := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  have hxy : x = y := by rw [← h1, ← h2, h]
  subst hxy
  have he : 0 < e := lt_of_le_of_lt (Nat.zero_le _) hx
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right he (by omega)⟩

end GlobalTheory

namespace GlobalTheory

theorem exists_period_dvd {l e a : ℕ} (ha : 1 ≤ a) (he : e + 1 = l ^ a) [NeZero e]
    (Sig : Finset (ZMod e)) (c : ZMod e) {s s' : ZMod e} (hs : s ∈ Sig) (hs' : s' ∈ Sig) :
    ∃ ρ, 1 ≤ ρ ∧ ρ ≤ GlobalTheory.BK.maxPeriod l Sig ∧
      ((l : ℤ) ^ a - 1) ∣ ((((c - s).val : ℕ) : ℤ) - (((c - s').val : ℕ) : ℤ)) * ((l : ℤ) ^ ρ - 1) := by
  have hla : ((l : ZMod e)) ^ a = 1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod e) he
    push_cast at h
    rw [ZMod.natCast_self, zero_add] at h
    exact h.symm
  have hper : Function.IsPeriodicPt (fun x : ZMod e => (l : ZMod e) * x) a (s' - s) := by
    show (fun x : ZMod e => (l : ZMod e) * x)^[a] (s' - s) = s' - s
    rw [mul_left_iterate, hla]; exact one_mul _
  refine ⟨GlobalTheory.BK.frobPeriod l (s' - s), hper.minimalPeriod_pos (by omega), ?_, ?_⟩
  · exact Finset.le_sup (f := fun p : ZMod e × ZMod e => GlobalTheory.BK.frobPeriod l (p.1 - p.2)) (b := (s', s))
      (Finset.mem_product.2 ⟨hs', hs⟩)
  · have hE : ((l : ℤ) ^ a - 1) = (e : ℤ) := by
      have : (e : ℤ) + 1 = (l : ℤ) ^ a := by exact_mod_cast he
      linarith
    rw [hE, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hfix : (fun x : ZMod e => (l : ZMod e) * x)^[GlobalTheory.BK.frobPeriod l (s' - s)] (s' - s) = s' - s :=
      Function.iterate_minimalPeriod
    rw [mul_left_iterate] at hfix
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination hfix

end GlobalTheory

namespace GlobalTheory


open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds GlobalTheory.BK in
theorem lagrange_C_rho_eq_comb_degrees : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a →
    ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l →
    ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) =
      α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) +
        β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  intro l e a _ ha he Sig c A' N hN hA
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  have hepos : 0 < e := by
    have : l ≤ l ^ a := Nat.le_self_pow (by omega) l
    omega
  have : NeZero e := ⟨by omega⟩
  have hE : ((l : ℤ) ^ a - 1) = (e : ℤ) := by
    have : (e : ℤ) + 1 = (l : ℤ) ^ a := by exact_mod_cast he
    linarith
  set Cc : Finset ℕ := Sig.image fun s => (c - s).val with hCc
  have hCclt : ∀ x ∈ Cc, x < e := by
    intro x hx
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hx
    exact ZMod.val_lt _
  have hD₁ : D₁ Sig c A' = (Cc ×ˢ Finset.Ico 0 A').image (fun p : ℕ × ℕ => p.1 + p.2 * e) :=
    degrees_eq_image_pairs Sig c 0 A'
  have hD₂ : D₂ Sig c A' = (Cc ×ˢ Finset.Ico A' (2 * A')).image (fun p : ℕ × ℕ => p.1 + p.2 * e) :=
    degrees_eq_image_pairs Sig c A' (2 * A')
  have hmap : ∀ T : Finset ℕ, (rootPoly T).map (Int.castRingHom ℤ_[l]) =
      ∏ i ∈ T.image (Nat.cast : ℕ → ℤ), (Polynomial.X - Polynomial.C ((i : ℤ) : ℤ_[l])) := by
    intro T
    rw [Finset.prod_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    simp [rootPoly, Polynomial.map_prod]
  set Z₁ : Finset ℤ := (D₁ Sig c A').image (Nat.cast : ℕ → ℤ) with hZ₁
  set Z₂ : Finset ℤ := (D₂ Sig c A').image (Nat.cast : ℕ → ℤ) with hZ₂
  have hdisj : Disjoint Z₁ Z₂ := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hi1
    obtain ⟨i₂, hi₂, heq⟩ := Finset.mem_image.1 hi2
    have heq' : i₂ = i₁ := by exact_mod_cast heq
    subst heq'
    rw [hD₁] at hi₁
    rw [hD₂] at hi₂
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 hi₁
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 hi₂
    rw [Finset.mem_product, Finset.mem_Ico] at hp hq
    have := add_mul_inj_of_lt (hCclt _ hp.1) (hCclt _ hq.1) (hpe.trans hqe.symm)
    omega
  have hlt : ∀ x ∈ Cc, x < l ^ a - 1 := fun x hx => by have := hCclt x hx; omega
  have hper : ∀ x ∈ Cc, ∀ y ∈ Cc, x ≠ y → ∃ ρ, 1 ≤ ρ ∧ ρ ≤ maxPeriod l Sig ∧
      ((l : ℤ) ^ a - 1) ∣ ((x : ℤ) - y) * ((l : ℤ) ^ ρ - 1) := by
    intro x hx y hy _
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hy
    exact exists_period_dvd ha he Sig c hs hs'
  have hU : Z₁ ∪ Z₂ = ((Cc ×ˢ Finset.range (2 * A')).image
      (fun p : ℕ × ℕ => p.1 + p.2 * e)).image (Nat.cast : ℕ → ℤ) := by
    rw [hZ₁, hZ₂, ← Finset.image_union, hD₁, hD₂, ← Finset.image_union, ← Finset.product_union]
    congr 3
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]
    omega
  have hbound : ∀ i ∈ Z₁, (∑ j ∈ Z₂, padicValInt l (i - j)) +
      ∑ j ∈ Z₁.erase i, padicValInt l (i - j) ≤ rho l Sig N := by
    intro i hi
    rw [Finset.sum_erase _ (by simp), add_comm, ← Finset.sum_union hdisj, hU,
      Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    rw [Finset.sum_image (fun p hp q hq hpq => by
      rw [Finset.mem_coe, Finset.mem_product] at hp hq
      have := add_mul_inj_of_lt (hCclt _ hp.1) (hCclt _ hq.1) hpq
      exact Prod.ext this.1 this.2), Finset.sum_product]
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hi
    rw [hD₁] at hi₀
    obtain ⟨⟨x, n⟩, hxn, rfl⟩ := Finset.mem_image.1 hi₀
    rw [Finset.mem_product, Finset.mem_Ico] at hxn
    have LB := Formalism.IrreducibleCountingLemmas.WindowSums.sumPadicValDifferencesLe l a A' (maxPeriod l Sig) Cc hl ha (by omega) hlt
      hper x hxn.1 n hxn.2.2
    rw [hE] at LB
    refine le_trans (le_of_eq ?_) (LB.trans ?_)
    · refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun m _ => ?_
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc
        simp
      · push_cast
        rfl
    · have hcard : Cc.card ≤ N := Finset.card_image_le.trans hN
      unfold rho
      calc (Cc.card - 1) * maxPeriod l Sig ≤ (N - 1) * maxPeriod l Sig :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 * (N - 1) * maxPeriod l Sig := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1
    (Formalism.IrreducibleCountingLemmas.WindowSums.lagrange_resolvent_T l Z₁ Z₂ (rho l Sig N) hdisj hbound)
  refine ⟨α, β, ?_⟩
  rw [← hαβ, P₁, P₂, hmap, hmap]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemEisensteinFiltrationEqEisensteinPowMulDisc
section
noncomputable section

namespace GlobalTheory.FilDiv

open PowerSeries Filter Topology GlobalTheory.BK

section
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

theorem FilPre_le_E_pow (j : ℕ) {g : S O K e} (hg : g ∈ FilPre O K l e j) :
    ∃ q ∈ Rpi (O := O) (K := K) l e, (g : K⟦X⟧) = E K l e ^ j * q := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, hx⟩ := hx
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    refine ⟨C (((m + j).factorial : K)⁻¹) * E K l e ^ m,
      mul_mem (HasK.C_mem _) (pow_mem (E_mem l e _) m), ?_⟩
    rw [hx, Ediv]; ring
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨q, hq, h⟩ := hx
    obtain ⟨q', hq', h'⟩ := hy
    exact ⟨q + q', add_mem hq hq', by rw [Subalgebra.coe_add, h, h', mul_add]⟩
  | smul c x _ hx =>
    obtain ⟨q, hq, h⟩ := hx
    exact ⟨c * q, mul_mem (S_le_R l e c.2) hq, by
      rw [smul_eq_mul, Subalgebra.coe_mul, h]; ring⟩

theorem norm_coeff_pow_mul_le (n : ℕ) {h : K⟦X⟧} (hh : h ∈ S O K e) (k : ℕ) :
    ‖coeff k ((l : K⟦X⟧) ^ n * h)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n := by
  rw [← map_natCast (C : K →+* K⟦X⟧), ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]
  refine mul_le_of_le_one_right (by positivity) ?_
  refine le_trans ?_ (hh.1 k)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans ?_ (norm_pow_le_norm_factorial l (k / e))
  rw [← rad_pow l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le k e)

theorem norm_coeff_E_le (k : ℕ) : ‖coeff k (E K l e)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ := by
  have he := NeZero.ne e
  rw [E, map_add (f := _), coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]
  by_cases hk : k = e
  · rw [if_pos hk, if_neg (by omega), add_zero, norm_one, one_mul, hk, rad_pow (K := K) l e]
  · by_cases h0 : k = 0
    · rw [if_neg hk, if_pos h0, zero_add, h0, pow_zero, mul_one]
    · rw [if_neg hk, if_neg h0, add_zero, norm_zero, zero_mul]
      exact norm_nonneg _

variable [CompleteSpace K]

theorem norm_coeff_quotE_le {r : K⟦X⟧} {n : ℕ}
    (hr : ∀ k, ‖coeff k r‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1)) (k : ℕ) :
    ‖coeff k (quotE l e r)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n := by
  have hρ := rad_pos l (1 / (e : ℝ))
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  rw [quotE, coeff_mk]
  have h1 : ‖tail l e r (k + e)‖ ≤ ‖(l : K)‖ ^ (n + 1) / rad l (1 / e) ^ (k + e) := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j => ?_
    rw [le_div_iff₀ (pow_pos hρ _), norm_term_eq]
    exact hr _
  calc ‖tail l e r (k + e)‖ * rad l (1 / e) ^ k
      ≤ ‖(l : K)‖ ^ (n + 1) / rad l (1 / e) ^ (k + e) * rad l (1 / e) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖(l : K)‖ ^ n := by
        rw [pow_add (rad l (1 / (e : ℝ))) k e, rad_pow (K := K) l e, pow_succ]
        field_simp

theorem norm_coeff_rem_le {r : K⟦X⟧} {n : ℕ}
    (hr : ∀ k, ‖coeff k r‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1)) (k : ℕ) :
    ‖coeff k (r - E K l e * quotE l e r)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
  have hw : ∀ i, 0 ≤ rad l (1 / (e : ℝ)) ^ i := fun i => pow_nonneg (rad_nonneg _ _) i
  rw [sub_eq_add_neg]
  refine (norm_coeff_add_le hw _ _ k).trans (max_le (hr k) ?_)
  rw [map_neg, norm_neg, pow_succ']
  exact norm_coeff_mul_le (w := fun i => rad l (1 / (e : ℝ)) ^ i) hw (fun i j => (pow_add _ i j).le)
    (norm_nonneg _) (by positivity) (norm_coeff_E_le l e) (norm_coeff_quotE_le l e hr) k

theorem exists_eq_E_pow_mul (j : ℕ) {ψ : K⟦X⟧} (hψ : ψ ∈ Rpi (O := O) (K := K) l e)
    (H : ∀ n : ℕ, ∃ q ∈ Rpi (O := O) (K := K) l e,
      ∀ k, ‖coeff k (ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) :
    ∃ q ∈ Rpi (O := O) (K := K) l e, ψ = E K l e ^ j * q := by
  have quot_mem {f : K⟦X⟧} (hf : f ∈ Rpi (O := O) (K := K) l e) :
      quotE l e f ∈ Rpi (O := O) (K := K) l e := by
    have hρ := rad_pos l (1 / (e : ℝ))
    have htail : Tendsto (fun n => ‖tail l e f n‖ * rad l (1 / e) ^ n) atTop (𝓝 0) := by
      have hcoeff := mem_R.1 hf
      rw [Metric.tendsto_atTop] at hcoeff ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hcoeff (ε / 2) (half_pos hε)
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      refine lt_of_le_of_lt ?_ (half_lt_self hε)
      rw [← le_div_iff₀ (pow_pos hρ n)]
      refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j => ?_
      rw [le_div_iff₀ (pow_pos hρ n), norm_term_eq]
      have hj := hN (n + j * e) (by omega)
      rw [Real.dist_eq, sub_zero] at hj
      exact (le_abs_self _).trans hj.le
    have hshift := (htail.comp (tendsto_add_atTop_nat e)).mul_const (rad l (1 / e) ^ e)⁻¹
    rw [zero_mul] at hshift
    refine mem_R.2 (hshift.congr fun n => ?_)
    simp only [Function.comp, quotE, coeff_mk]
    rw [pow_add, mul_assoc, mul_inv_cancel_right₀ (pow_pos hρ e).ne']
  have coeff_rem {f : K⟦X⟧} (hf : f ∈ Rpi (O := O) (K := K) l e) (n : ℕ) :
      coeff (n + e) (f - E K l e * quotE l e f) = 0 := by
    have tail_rec (m : ℕ) : tail l e f m = coeff m f - l * tail l e f (m + e) := by
      have hs : Summable fun j : ℕ => coeff (m + j * e) f * (-(l : K)) ^ j := by
        refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
        rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
        have h := ((mem_R.1 hf).comp (tendsto_add_mul e m)).mul_const (rad l (1 / e) ^ m)⁻¹
        rw [zero_mul] at h
        refine h.congr fun j => ?_
        simp only [Function.comp]
        rw [← norm_term_eq (K := K) l e, mul_inv_cancel_right₀ (pow_pos (rad_pos l _) m).ne']
      rw [tail, hs.tsum_eq_zero_add, tail, ← tsum_mul_left, sub_eq_add_neg, ← tsum_neg]
      congr 1
      · simp
      · refine tsum_congr fun j => ?_
        rw [show m + (j + 1) * e = m + e + j * e by ring]
        ring
    rw [map_sub, coeff_E_mul, quotE, coeff_mk, coeff_mk, tail_rec (n + e)]
    ring
  have zero_of_coeff {g : K⟦X⟧} (hg : g ∈ Rpi (O := O) (K := K) l e)
      (h : ∀ n, coeff (n + e) (E K l e * g) = 0) : g = 0 := by
    ext n
    have hcoeff : ∀ j, coeff n g = coeff (n + j * e) g * (-(l : K)) ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hj := h (n + j * e)
        rw [coeff_E_mul] at hj
        rw [ih, show n + (j + 1) * e = n + j * e + e by ring]
        linear_combination (-(l : K)) ^ j * hj
    have ht := (mem_R.1 hg).comp (tendsto_add_mul e n)
    have hzero : ‖coeff n g‖ * rad l (1 / e) ^ n = 0 := by
      refine tendsto_nhds_unique tendsto_const_nhds (ht.congr fun j => ?_)
      simp only [Function.comp]
      rw [← norm_term_eq (K := K) l e, ← hcoeff]
    simpa [(rad_pos l _).ne'] using hzero
  induction j generalizing ψ with
  | zero => exact ⟨ψ, hψ, by simp⟩
  | succ j ih =>
    have hQ := quot_mem hψ
    have key : ∀ n, ∃ q ∈ Rpi (O := O) (K := K) l e,
        (∀ k, ‖coeff k (quotE l e ψ - E K l e ^ j * q)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n) ∧
        ∀ k, ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
      intro n
      obtain ⟨q, hq, hr⟩ := H (n + 1)
      have hrR : ψ - E K l e ^ (j + 1) * q ∈ Rpi (O := O) (K := K) l e :=
        sub_mem hψ (mul_mem (pow_mem (E_mem l e _) _) hq)
      generalize hr_def : ψ - E K l e ^ (j + 1) * q = r at hr hrR
      have hg : quotE l e ψ - E K l e ^ j * q - quotE l e r = 0 := by
        refine zero_of_coeff (sub_mem (sub_mem hQ (mul_mem (pow_mem (E_mem l e _) _) hq))
          (quot_mem hrR)) fun m => ?_
        have h1 := coeff_rem hψ m
        have h2 := coeff_rem hrR m
        have : E K l e * (quotE l e ψ - E K l e ^ j * q - quotE l e r) =
            (r - E K l e * quotE l e r) - (ψ - E K l e * quotE l e ψ) := by
          rw [← hr_def]; ring
        rw [this, map_sub, h1, h2, sub_zero]
      have hg' : quotE l e ψ - E K l e ^ j * q = quotE l e r := sub_eq_zero.1 hg
      have hrem : ψ - E K l e * quotE l e ψ = r - E K l e * quotE l e r := by
        rw [← hg', ← hr_def]; ring
      exact ⟨q, hq, fun k => by rw [hg']; exact norm_coeff_quotE_le l e hr k,
        fun k => by rw [hrem]; exact norm_coeff_rem_le l e hr k⟩
    choose qs hqs hsmall hrem using key
    obtain ⟨q, hq, hQ'⟩ := ih hQ fun n => ⟨qs n, hqs n, hsmall n⟩
    have hR0 : ψ - E K l e * quotE l e ψ = 0 := by
      ext k
      rw [map_zero]
      have hρ := pow_pos (rad_pos l (1 / (e : ℝ))) k
      have ht : Tendsto (fun n : ℕ => ‖(l : K)‖ ^ (n + 1)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one l)).comp
          (tendsto_add_atTop_nat 1)
      have h0 : ‖coeff k (ψ - E K l e * quotE l e ψ)‖ * rad l (1 / e) ^ k ≤ 0 :=
        ge_of_tendsto' ht fun n => hrem n k
      exact norm_le_zero_iff.1 (le_of_mul_le_mul_right (by simpa using h0) hρ)
    refine ⟨q, hq, ?_⟩
    rw [sub_eq_zero] at hR0
    rw [hR0, hQ', pow_succ']; ring

end

theorem mem_Fil_eq_E_pow_mul : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] (j : ℕ), ∀ φ : S O K e, φ ∈ Fil O K l e j →
      ∃ q ∈ Rpi (O := O) (K := K) l e, (φ : K⟦X⟧) = E K l e ^ j * q := by
  intro O K _ _ _ _ _ _ l e _ _ _ j φ hφ
  have hψ : (φ : K⟦X⟧) ∈ Rpi (O := O) (K := K) l e := S_le_R l e φ.2
  refine exists_eq_E_pow_mul l e j hψ fun n => ?_
  obtain ⟨g, hg, h, H⟩ := (mem_Fil l).1 hφ n
  obtain ⟨q, hq, hgq⟩ := FilPre_le_E_pow l e j hg
  refine ⟨q, hq, fun k => ?_⟩
  have : (φ : K⟦X⟧) - E K l e ^ j * q = (l : K⟦X⟧) ^ n * h := by
    rw [H]; push_cast; rw [hgq]; ring
  rw [this]
  exact norm_coeff_pow_mul_le l e n h.2 k

end GlobalTheory.FilDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPhiModuleLatticeOfAdicSeriesPrimePowTerms
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

theorem PhiMod.mem_MM_of_series (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) :
    ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) →
      (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow (K := K) (a := a) (ι := ι) m) → w ∈ P.MM := by
  intro w t ht hw
  choose v hv htv using ht
  have h2 (k : ℕ) : ∃ s ∈ P.MM, ∀ m, ∃ g ∈ P.MM,
      w - (s + (l : K) ^ k • g) ∈ uPow (K := K) (a := a) (ι := ι) m := by
    refine ⟨∑ n ∈ Finset.range k, t n,
      sum_mem fun n _ => (htv n) ▸ P.l_pow_smul_mem_MM n (hv n), fun m => ?_⟩
    refine ⟨∑ n ∈ Finset.range m, (l : K) ^ n • v (k + n),
      sum_mem fun n _ => P.l_pow_smul_mem_MM n (hv _), uPow_anti (Nat.le_add_left m k) ?_⟩
    have := hw (k + m)
    rw [Finset.sum_range_add] at this
    simpa only [Finset.smul_sum, smul_smul, ← pow_add, ← htv] using this
  have hext {τ : ZMod a} {v : ι → K⟦X⟧} :
      v ∈ P.extc (S O K e) τ ↔ P.mxInv τ *ᵥ v ∈ vecs ι (S O K e) := by
    have hmem {v : ι → K⟦X⟧} : v ∈ P.extc (S O K e) τ ↔
        ∃ m ∈ vecs ι (S O K e), v = P.mx τ *ᵥ m := by
      rw [PhiMod.extc, Submodule.mem_span_range_iff_exists_fun]
      have key (c : ι → S O K e) : ∑ i, c i • (P.mx τ).col i =
          P.mx τ *ᵥ fun i => (c i : K⟦X⟧) := by
        ext1 j
        simp [Matrix.mulVec, dotProduct, Subalgebra.smul_def, mul_comm]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨_, fun i => (c i).2, key c⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨fun i => ⟨m i, hm i⟩, key _⟩
    rw [hmem]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rwa [Matrix.mulVec_mulVec, P.mxInv_mul_mx, Matrix.one_mulVec]
    · intro h
      exact ⟨_, h, by rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]⟩
  refine mem_tot.2 fun τ => hext.2 fun i => mem_S_of_approx (l := l) fun k => ?_
  obtain ⟨s, hs, H⟩ := h2 k
  refine ⟨_, hext.1 (mem_tot.1 hs τ) i, fun m => ?_⟩
  obtain ⟨g, hg, H'⟩ := H m
  refine ⟨_, hext.1 (mem_tot.1 hg τ) i, ?_⟩
  have := dvd_mulVec (P.mxInv τ) (H' τ) i
  simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul] using this

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTiltUntiltLeOfFrobeniusSeriesSizeLe
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem norm_sh_le_of_lam_le : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (ρ : ℝ) (x : Fl l), 2 ≤ h → 0 ≤ ρ → ρ < 1 → ‖sh x‖ < 1 → (∀ j : ℕ, j < 2 → ‖lam h j x‖ ≤ gam l h j ρ) → ‖sh x‖ ≤ ρ := by
  intro l _ h ρ x h2 hρ0 hρ1 hs1 hlam
  by_contra hlt
  push_neg at hlt
  set s := ‖sh x‖ with hs
  have hs0 : 0 < s := lt_of_le_of_lt hρ0 hlt
  have h1 : 1 ≤ h := le_trans (by norm_num) h2
  obtain ⟨j, hj, n₀, hn₀⟩ := _root_.GlobalTheory.PSer.Uniq.exists_unique_max_term l h s h2 hs0 hs1
  obtain ⟨hsum, -, -, -⟩ := _root_.GlobalTheory.PSer.lam_hasSum_norm_le_frob l h j s x h1 hs1 le_rfl
  have hpw := (_root_.GlobalTheory.PSer.PwLaws.pw_laws l).2.2.2.2.2.2
  have hterm : ∀ n : ℤ, ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖
      = ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) := by
    intro n
    rw [norm_mul, norm_zpow, hpw]
  have hnorm : ‖lam h j x‖ = ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
    rw [_root_.GlobalTheory.norm_hasSum_eq_of_dominant ℂ_[l] ℤ _ _ n₀ hsum (by
      intro n hn
      rw [hterm, hterm]
      exact hn₀ n hn), hterm]
  obtain ⟨-, ⟨m, hm⟩, -, -, -, hmono⟩ := _root_.GlobalTheory.gam_laws l h j s h1 hs0.le hs1
  have hgs : gam l h j s ≤ ‖lam h j x‖ := by
    rw [hm, hnorm]
    by_cases hmn : m = n₀
    · rw [hmn]
    · exact (hn₀ m hmn).le
  have hgρ : gam l h j ρ < gam l h j s := ((_root_.GlobalTheory.gam_laws l h j ρ h1 hρ0 hρ1).2.2.2.2.2) s hlt hs1
  have := hlam j hj
  linarith

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedLengthLatticeQuotientBaseChangeEqStatement
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedLength_latticeQuotient_baseChange_eq : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → (l : 𝓞 K) ∈ w.asIdeal → (∀ a : 𝓞 K, ∀ z : O, algebraMap O (FractionRing O) z = e (a : K) → (a ∈ w.asIdeal ↔ ¬ IsUnit z)) → ∀ (A B : Submodule (𝓞 K) V), A.FG → B ≤ A → lenUnit (O := O) l (↥(Submodule.span O (iV '' (A : Set V))) ⧸ (Submodule.span O (iV '' (B : Set V))).comap (Submodule.span O (iV '' (A : Set V))).subtype) = Formalism.L2.Col.lenUW w A B := by
  first | exact @GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | exact GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW | (intros; apply GlobalTheory.LatLenExt.lenUnit_span_eq_lenUW <;> assumption)
end

