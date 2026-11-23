module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticeNormalizedGaussSumEighthRoot

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsOrbitAverageOfSeedPowersWeight
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.OrbitAvg

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem sl_sum (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {α : Type} (T : Finset α) (u : α → Hn F → ℂ) :
    sl k h (∑ a ∈ T, u a) = ∑ a ∈ T, sl k h (u a) := by
  funext z; simp only [sl, sl0, Finset.sum_apply, Finset.mul_sum]

theorem det_free_slash_finset_sum (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {α : Type} (T : Finset α) (u : α → Hn F → ℂ) :
    sl0 k h (∑ a ∈ T, u a) = ∑ a ∈ T, sl0 k h (u a) := by
  funext z; simp only [sl0, Finset.sum_apply, Finset.mul_sum]

theorem hol_pow {f : Hn F → ℂ} (hf : Hol f) (M : ℕ) : Hol (f ^ M) := by
  induction M with
  | zero => rw [pow_zero]; exact differentiableOn_const _
  | succ n ih => rw [pow_succ]; exact (HolKeep.main F 0 _ _ 0 ih hf).2.2.1

theorem hol_sum {α : Type} (T : Finset α) (u : α → Hn F → ℂ) (hu : ∀ a ∈ T, Hol (u a)) :
    Hol (∑ a ∈ T, u a) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact differentiableOn_const _
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (HolKeep.main F 0 _ _ 0 (hu a (Finset.mem_insert_self a T))
      (ih fun b hb => hu b (Finset.mem_insert_of_mem hb))).1

theorem gr_pow {f : Hn F → ℂ} (hf : Gr f) (M : ℕ) : Gr (f ^ M) := by
  induction M with
  | zero => rw [pow_zero]; exact Growth.gr_const 1
  | succ n ih => rw [pow_succ]; exact Growth.gr_mul ih hf

theorem gr_sum {α : Type} (T : Finset α) (u : α → Hn F → ℂ) (hu : ∀ a ∈ T, Gr (u a)) :
    Gr (∑ a ∈ T, u a) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Growth.gr_const 0
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact Growth.gr_add (hu a (Finset.mem_insert_self a T)) (ih fun b hb => hu b (Finset.mem_insert_of_mem hb))

end Gen

section Small

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ)

theorem small_zero {s : ℝ} (hs : 0 ≤ s) : Small ι s (0 : Hn F → ℂ) := by
  refine ⟨0, ⟨⟨1, one_pos, fun ξ h => absurd rfl h⟩, fun z => ?_⟩, fun ξ => ?_⟩
  · simpa using (hasSum_zero : HasSum (fun _ : F => (0 : ℂ)) 0)
  · simpa using hs

theorem small_sum' {α : Type} (T : Finset α) (u : α → Hn F → ℂ) {r : ℝ} (hz : Small ι r (0 : Hn F → ℂ))
    (hu : ∀ a ∈ T, Small ι r (u a)) : Small ι r (∑ a ∈ T, u a) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hz
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := hu a (Finset.mem_insert_self a T)
    have h2 := ih fun b hb => hu b (Finset.mem_insert_of_mem hb)
    simpa using (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι r r _ _ 0 h1 h2).1

theorem small_sum {α : Type} (T : Finset α) (u : α → Hn F → ℂ) {r : ℝ} (hT : T.Nonempty)
    (hu : ∀ a ∈ T, Small ι r (u a)) : Small ι r (∑ a ∈ T, u a) := by
  obtain ⟨a0, ha0⟩ := hT
  have hr : 0 ≤ r := (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι r r _ _ 0 (hu a0 ha0) (hu a0 ha0)).2.2.2.2.1
  exact small_sum' ι T u (small_zero ι hr) hu

end Small

theorem norm_natCast_inv_le (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    ‖((n : Qbar p))⁻¹‖ ≤ (p : ℝ) ^ (n.factorization p) := by
  have e : ((n : ℕ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) (n : ℚ_[p]) := (map_natCast _ n).symm
  have h1 := Nat.ordProj_mul_ordCompl_eq_self n p
  have hc : ‖((ordCompl[p] n : ℕ) : ℚ_[p])‖ = 1 :=
    (Padic.norm_natCast_eq_one_iff).2 (Nat.coprime_ordCompl hp.out hn)
  have h2 : ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(n.factorization p : ℤ)) := by
    conv_lhs => rw [← h1]
    rw [Nat.cast_mul, norm_mul, hc, mul_one, Nat.cast_pow, Padic.norm_p_pow]
  rw [norm_inv, e, PadicAlgCl.norm_extends, h2, zpow_neg, inv_inv, zpow_natCast]

end GlobalTheory.HilbertThetaSeries.OrbitAvg

namespace GlobalTheory.HilbertThetaSeries.OrbitAvg

theorem sl_cancel {F : Type} [Field F] [NumberField F] (k : ℕ) (h h' : GL (Fin 2) (InfinitePlace F → ℝ))
    (hh : Pos h) (hh' : Pos h') (e : h * h' = 1) (f : Hn F → ℂ) : sl k h' (sl k h f) = f := by
  have H := SlashCocycle.slash_cocycle F k h h' f hh hh'
  rw [← H.2.2.2.1, e, H.2.2.2.2.2]

theorem avg_pow : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → ∃ N : ℕ, ∀ M : ℕ, p ^ N ∣ M → ∃ f : Hn F → ℂ, Comp ι δ ((p - 1) * M) (aff y 0) f := by
  intro F _ _ _ p _ ι hp2 δ hδ θ hθ y hy
  classical
  obtain ⟨hfin, hone, h1, hgrp⟩ := GlobalTheory.T.hilbert_seed_orbit_finite_and_congruence F p ι hp2 δ hδ θ hθ y hy
  set g0 := aff y (0 : Af F) with hg0
  set T := hfin.toFinset with hT
  have hmem : ∀ g, g ∈ T ↔ ∃ γ, Stab g0 γ ∧ g = sl (p - 1) (toInf γ) θ := fun g => by
    rw [hT, Set.Finite.mem_toFinset]; rfl
  have hpos : ∀ γ, Stab g0 γ → Pos (toInf γ) := fun γ hγ => ((GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash F 0 θ).2.1 γ).1.2 hγ.1
  have hθT : sl (p - 1) (toInf 1) θ ∈ T := (hmem _).2 ⟨1, h1, rfl⟩
  have hTne : T.Nonempty := ⟨_, hθT⟩
  have hcard : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hTne)

  have hmap : ∀ γ, Stab g0 γ → ∀ g ∈ T, sl (p - 1) (toInf γ) g ∈ T := by
    intro γ hγ g hg
    obtain ⟨γ', hγ', rfl⟩ := (hmem g).1 hg
    refine (hmem _).2 ⟨γ' * γ, (hgrp γ' γ hγ' hγ).1, ?_⟩
    rw [map_mul, (SlashCocycle.slash_cocycle F (p - 1) _ _ θ (hpos γ' hγ') (hpos γ hγ)).2.2.2.1]
  have hperm : ∀ γ, Stab g0 γ → ∀ M : ℕ, ∑ g ∈ T, (sl (p - 1) (toInf γ) g) ^ M = ∑ g ∈ T, g ^ M := by
    intro γ hγ M
    have hγi := (hgrp γ γ hγ hγ).2
    refine Finset.sum_nbij' (fun g => sl (p - 1) (toInf γ) g) (fun g => sl (p - 1) (toInf γ⁻¹) g)
      (fun g hg => hmap γ hγ g hg) (fun g hg => hmap γ⁻¹ hγi g hg) (fun g _ => ?_) (fun g _ => ?_) (fun g _ => rfl)
    · exact sl_cancel _ _ _ (hpos γ hγ) (hpos _ hγi) (by rw [← map_mul, mul_inv_cancel, map_one]) g
    · exact sl_cancel _ _ _ (hpos _ hγi) (hpos γ hγ) (by rw [← map_mul, inv_mul_cancel, map_one]) g
  have hholT : ∀ g ∈ T, Hol g := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := (hmem g).1 hg
    exact (HolKeep.main F (p - 1) θ θ 0 hθ.hol hθ.hol).2.2.2.2.2 _ (hpos γ hγ) |>.2
  have hgrT : ∀ g ∈ T, Gr g := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := (hmem g).1 hg
    exact Growth.gr_sl _ _ hθ.gr
  refine ⟨T.card.factorization p, ?_⟩
  rintro M ⟨m, rfl⟩
  set c : ℂ := (T.card : ℂ)⁻¹ with hc
  refine ⟨c • ∑ g ∈ T, g ^ (p ^ T.card.factorization p * m), ?_, ?_, ?_, ?_⟩
  · exact (HolKeep.main F 0 _ θ c
      (hol_sum T (fun g => g ^ (p ^ T.card.factorization p * m)) fun g hg => hol_pow (hholT g hg) _) hθ.hol).2.1
  · exact Growth.gr_smul c (gr_sum T (fun g => g ^ (p ^ T.card.factorization p * m)) fun g hg => gr_pow (hgrT g hg) _)
  · intro γ hγ
    have L := fun (f : Hn F → ℂ) => GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F (p - 1) (p ^ T.card.factorization p * m) (toInf γ) f f c
    rw [(GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F _ 0 (toInf γ) _ θ c).2.2.2.2.1, sl_sum]
    congr 1
    rw [← hperm γ hγ]
    exact Finset.sum_congr rfl fun g _ => (L g).2.2.2.2.2
  · intro γ hγ
    set N := T.card.factorization p
    have L := fun (f : Hn F → ℂ) => GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F (p - 1) (p ^ N * m) (toInf γ) f f c
    have e : sl0 ((p - 1) * (p ^ N * m)) (toInf γ) (c • ∑ g ∈ T, g ^ (p ^ N * m)) - 1 =
        c • ∑ g ∈ T, ((sl0 (p - 1) (toInf γ) g) ^ (p ^ N * m) - 1) := by
      rw [(GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F _ 0 (toInf γ) _ θ c).2.1, det_free_slash_finset_sum, Finset.sum_congr rfl fun g _ => (L g).2.2.1, Finset.sum_sub_distrib, smul_sub,
        Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc, inv_mul_cancel₀ hcard, one_smul]
    rw [e]
    have hS : Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (∑ g ∈ T, ((sl0 (p - 1) (toInf γ) g) ^ (p ^ N * m) - 1)) := by
      refine small_sum ι T _ hTne fun g hg => ?_
      obtain ⟨γ', hγ', rfl⟩ := (hmem g).1 hg
      exact GlobalTheory.T.hilbertQExp_padicCongruence_pow_prime_pow F p ι _ (hone γ' hγ' γ hγ) N m
    have H := (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ c hS hS).2.2.1
    have hθ1 := hone 1 h1 γ hγ
    refine (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ c H hθ1).2.2.2.1 ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hn : ‖ι.symm c‖ ≤ (p : ℝ) ^ N := by
      rw [hc, map_inv₀, map_natCast]
      exact norm_natCast_inv_le p T.card (Finset.card_ne_zero.2 hTne)
    calc ‖ι.symm c‖ * (p : ℝ)⁻¹ ^ (N + 1) ≤ (p : ℝ) ^ N * (p : ℝ)⁻¹ ^ (N + 1) :=
          mul_le_mul_of_nonneg_right hn (by positivity)
      _ = (p : ℝ)⁻¹ := by rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hp0.ne', one_pow, one_mul]

end GlobalTheory.HilbertThetaSeries.OrbitAvg

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orbit_average_of_seed_powers_weight : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → ∃ N : ℕ, ∀ M : ℕ, p ^ N ∣ M → ∃ f : Hn F → ℂ, Comp ι δ ((p - 1) * M) (aff y 0) f := by
  first | exact @GlobalTheory.HilbertThetaSeries.OrbitAvg.avg_pow | exact GlobalTheory.HilbertThetaSeries.OrbitAvg.avg_pow | (intros; apply GlobalTheory.HilbertThetaSeries.OrbitAvg.avg_pow <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSlashEighthRootOfSquareDet
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.ThetaLevel

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pos_toInf {γ : GL (Fin 2) F} (h : γ.val.det = 1) : Pos (toInf γ) := by
  intro v
  have e : (↑(toInf γ) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det = rhom γ.val.det := by
    rw [RingHom.map_det]
    rfl
  rw [e, h, map_one]
  exact one_pos

def low (x : F) : GL (Fin 2) F where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem natCast_int (N : ℕ) : IsIntegral ℤ (N : F) := by
  exact isIntegral_natCast N

theorem decomp (γ : GL (Fin 2) F) (hdet : γ.val.det = 1) (hc : γ.val 1 0 ≠ 0) :
    γ = aff 1 (γ.val 0 0 / γ.val 1 0) * wm (Units.mk0 _ hc) * aff 1 (γ.val 1 1 / γ.val 1 0) := by
  have had : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by rw [← hdet, Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, wm, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> linear_combination (-1 : F) * had

private theorem sl0_mul_of_pos (k : ℕ) (g h : GL (Fin 2) (InfinitePlace F → ℝ)) (hh : Pos h)
    (f : Hn F → ℂ) : sl0 k (g * h) f = sl0 k h (sl0 k g f) := by
  funext z
  simp only [sl0]
  have hact : act (g * h) z = act g (act h z) := by
    funext v
    simp only [act, map_mul, mul_smul]
  have hden : ∀ v, UpperHalfPlane.denom (cmp v (g * h)) (z v) =
      UpperHalfPlane.denom (cmp v g) (act h z v) * UpperHalfPlane.denom (cmp v h) (z v) := by
    intro v
    have hpos : 0 < ((cmp v h).det : ℝ) := by
      have e : ((cmp v h).det : ℝ) =
          (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
        simp [cmp]
      rw [e]
      exact hh v
    rw [map_mul, UpperHalfPlane.denom_cocycle_σ]
    simp only [UpperHalfPlane.σ, if_pos hpos, ContinuousAlgEquiv.refl_apply]
    rfl
  rw [hact, Finset.prod_congr rfl (fun v _ => hden v), Finset.prod_mul_distrib, mul_inv, mul_pow]
  ring

private theorem sl0_smul (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (ζ : ℂ)
    (f : Hn F → ℂ) : sl0 k h (ζ • f) = ζ • sl0 k h f := by
  funext z
  simp only [sl0, Pi.smul_apply, smul_eq_mul]
  ring

theorem main_abcd {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (hG : EvenPos G) (t : ℕ)
    (ht : G.det = (t : ℤ) ^ 2) (k : ℕ) (hk : Fintype.card κ = 2 * k) (N : ℕ) (hN0 : 0 < N)
    (hN : ∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y))
    (a b c d : F) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b) (hcN : IsIntegral ℤ (c / N)) (hd : IsIntegral ℤ d)
    (had : a * d - b * c = 1) (hc : c ≠ 0) :
    ∃ ζ : ℂ, ζ ^ 8 = 1 ∧
      sl0 k (toInf (aff 1 (a / c) * wm (Units.mk0 c hc) * aff 1 (d / c))) (th G oneL) = ζ • th G oneL := by
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN0.ne'
  have hcI : IsIntegral ℤ c := by
    have h1 := (natCast_int (F := F) N).mul hcN
    rwa [mul_div_cancel₀ _ hNF] at h1
  obtain ⟨T, hT, -, hTle, -⟩ := GlobalTheory.T.exists_finite_reps_scaled_lattice_card_norm F κ c 1 hc one_ne_zero (by rwa [div_one])
  obtain ⟨hsymm, hsc, -, hint, hLL, haL, het, hLd⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hG
  have hsupp : ∀ x : κ → F, (fun x => oneL x * et (a / c * QF G x)) x ≠ 0 → x ∈ aL κ (1 : F) := by
    intro x hx
    have hxL : x ∈ LL F κ := by
      by_contra hn
      apply hx
      simp [oneL, hn]
    exact (haL 1 x).2 ⟨x, hxL, (one_smul F x).symm⟩
  have hper : ∀ x l : κ → F, l ∈ aL κ c →
      (fun x => oneL x * et (a / c * QF G x)) (x + l) = (fun x => oneL x * et (a / c * QF G x)) x := by
    intro x l hl
    obtain ⟨m, hm, rfl⟩ := (haL c l).1 hl
    have hcm : c • m ∈ LL F κ := by
      rw [hLL]
      intro i
      rw [Pi.smul_apply, smul_eq_mul]
      exact hcI.mul ((hLL m).1 hm i)
    by_cases hx : x ∈ LL F κ
    · have hxl : x + c • m ∈ LL F κ := add_mem hx hcm
      simp only [oneL, if_pos hx, if_pos hxl, one_mul]
      rw [(hsymm x (c • m)).2, (hsymm x (c • m)).1, (hsc c m x).1, (hsc c m x).2.1]
      have e : a / c * (QF G x + c * BF G m x + c ^ 2 * QF G m) =
          a / c * QF G x + (a * BF G m x + a * c * QF G m) := by
        field_simp
        ring
      have hi : IsIntegral ℤ (a * BF G m x + a * c * QF G m) :=
        (ha.mul ((hint m hm).2 x hx)).add ((ha.mul hcI).mul (hint m hm).1)
      rw [e, (het (a / c * QF G x) (a * BF G m x + a * c * QF G m)).1,
        (het (a * BF G m x + a * c * QF G m) 0).2.2.2 hi, mul_one]
    · have hxl : x + c • m ∉ LL F κ := by
        intro h
        apply hx
        simpa using sub_mem h hcm
      simp [oneL, hx, hxl]
  have hW' := GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula F κ G hG t ht k hk c 1 (Units.mk0 c hc) T
    (fun x => oneL x * et (a / c * QF G x)) hc one_ne_zero hTle hT hsupp hper
  have hW : Pos (toInf (wm (Units.mk0 c hc))) := pos_toInf (by simp [wm, Matrix.det_fin_two, hc])
  have hB : Pos (toInf (aff 1 (d / c))) := pos_toInf (by simp [aff, Matrix.det_fin_two])
  rw [map_mul, sl0_mul_of_pos _ _ _ hB, map_mul, sl0_mul_of_pos _ _ _ hW, GlobalTheory.T.thetaSeries_translation_twists_coefficients, hW',
    GlobalTheory.T.thetaSeries_translation_twists_coefficients]
  refine ⟨wC k t c c * ∑ x ∈ T, et (a / c * QF G x),
    GlobalTheory.T.lattice_normalized_gaussSum_eighth_root F κ G hG t ht k hk N a b c d T hN0 hN ha hb hcN hd had hc hT, ?_⟩
  funext z
  simp only [th, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1
  funext y
  have key : wT G k t c (↑(Units.mk0 c hc)) T (fun x => oneL x * et (a / c * QF G x)) y *
      et (d / c * QF G y) = wC k t c c * (∑ x ∈ T, et (a / c * QF G x)) * oneL y := by
    have hcc : (c / c) • y = y := by rw [div_self hc, one_smul]
    by_cases hy : y ∈ dualL F G
    · have hsum : ∑ x ∈ T, oneL x * et (a / c * QF G x) * et (BF G y x / c) =
          ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxL : x ∈ LL F κ := by
          obtain ⟨l, hl, hxl⟩ := (haL 1 x).1 (hT.1 x hx)
          rw [hxl, one_smul]
          exact hl
        simp [oneL, hxL]
      have h62 := GlobalTheory.T.lattice_gaussSum_twist_dual_eq_indicator F κ G hG N a b c d T hN0 hN ha hb hcN hd had hc hT y hy
      simp only [wT, Units.val_mk0, hcc, hy, ↓reduceIte]
      rw [hsum, mul_assoc, h62]
      ring
    · have hyL : y ∉ LL F κ := fun h => hy (hLd h)
      simp only [wT, Units.val_mk0, hcc, hy, ↓reduceIte, oneL, hyL]
      ring
  rw [key]
  ring

theorem main_ne {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (hG : EvenPos G) (t : ℕ)
    (ht : G.det = (t : ℤ) ^ 2) (k : ℕ) (hk : Fintype.card κ = 2 * k) (N : ℕ) (hN0 : 0 < N)
    (hN : ∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y))
    (γ : GL (Fin 2) F) (hγ : InGam N γ) (hc : γ.val 1 0 ≠ 0) :
    ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 k (toInf γ) (th G oneL) = ζ • th G oneL := by
  obtain ⟨hdet, ha, hb, hcN, hd⟩ := hγ
  have had : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hdet
  rw [decomp γ hdet hc]
  exact main_abcd G hG t ht k hk N hN0 hN _ _ _ _ ha hb hcN hd had hc

theorem low_inGam (N : ℕ) (hN0 : 0 < N) : InGam N (low (-(N : F))) := by
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN0.ne'
  refine ⟨by simp [low, Matrix.det_fin_two], by simp [low, isIntegral_one], by simp [low, isIntegral_zero], ?_, by simp [low, isIntegral_one]⟩
  have : (low (-(N : F))).val 1 0 / N = -1 := by simp [low, hNF]
  rw [this]; exact isIntegral_one.neg

end GlobalTheory.HilbertThetaSeries.ThetaLevel


open GlobalTheory.HilbertThetaSeries.ThetaLevel in
theorem GlobalTheory.HilbertThetaSeries.theta_level_eighth_root : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∃ N : ℕ, 0 < N ∧ ∀ γ : GL (Fin 2) F, InGam N γ → ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 k (toInf γ) (th G oneL) = ζ • th G oneL := by
  intro F _ _ _ κ _ _ G hG t ht k hk
  obtain ⟨N, hN0, hN⟩ := (GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG).2.1
  refine ⟨N, hN0, fun γ hγ => ?_⟩
  by_cases hc : γ.val 1 0 = 0
  · have hNF : (N : F) ≠ 0 := by exact_mod_cast hN0.ne'
    obtain ⟨hdet, ha, hb, hcN, hd⟩ := hγ
    have hdet' : γ.val 0 0 * γ.val 1 1 = 1 := by
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      exact hdet
    have hd0 : γ.val 1 1 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdet'
      exact zero_ne_one hdet'
    have hNI : IsIntegral ℤ (N : F) := natCast_int N
    have e3 : ∀ i j, (γ * low (N : F)).val i j =
        γ.val i 0 * (low (N : F)).val 0 j + γ.val i 1 * (low (N : F)).val 1 j := by
      intro i j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hγ3 : InGam N (γ * low (N : F)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [Units.val_mul, Matrix.det_mul, hdet]
        simp [low, Matrix.det_fin_two]
      · rw [e3]
        simp only [low, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, mul_one]
        exact ha.add (hb.mul hNI)
      · rw [e3]
        simpa [low] using hb
      · rw [e3]
        simp only [low, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, hc, zero_mul, zero_add]
        rw [mul_div_cancel_right₀ _ hNF]
        exact hd
      · rw [e3]
        simpa [low, hc] using hd
    have hc3 : (γ * low (N : F)).val 1 0 ≠ 0 := by
      rw [e3]
      simpa [low, hc] using mul_ne_zero hd0 hNF
    have hlow : (low (-(N : F))).val 1 0 ≠ 0 := by
      simpa [low] using hNF
    obtain ⟨ζ1, h1, e1⟩ := main_ne G hG t ht k hk N hN0 hN _ hγ3 hc3
    obtain ⟨ζ2, h2, e2⟩ := main_ne G hG t ht k hk N hN0 hN _ (low_inGam N hN0) hlow
    have hγe : γ = γ * low (N : F) * low (-(N : F)) := by
      rw [mul_assoc]
      conv_lhs => rw [← mul_one γ]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [low, Matrix.mul_apply, Fin.sum_univ_succ]
    have hP : Pos (toInf (low (-(N : F)))) := pos_toInf (by simp [low, Matrix.det_fin_two])
    refine ⟨ζ1 * ζ2, by rw [mul_pow, h1, h2, one_mul], ?_⟩
    rw [hγe, map_mul, sl0_mul_of_pos _ _ _ hP, e1, sl0_smul, e2, smul_smul]
  · exact main_ne G hG t ht k hk N hN0 hN γ hγ hc

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_slash_eighth_root_of_square_det : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∃ N : ℕ, 0 < N ∧ ∀ γ : GL (Fin 2) F, InGam N γ → ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 k (toInf γ) (th G oneL) = ζ • th G oneL := by
  first | exact @GlobalTheory.HilbertThetaSeries.theta_level_eighth_root | exact GlobalTheory.HilbertThetaSeries.theta_level_eighth_root | (intros; apply GlobalTheory.HilbertThetaSeries.theta_level_eighth_root <;> assumption)
end
end

