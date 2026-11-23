module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0345
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperTriangularHeckeReindexCoprimeUnit
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem Tower.sum_act_upper_mul_unit {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (c : X.Fn l) (hc : ∀ t : ℤ, X.act l !![1, t; 0, 1] c = c) (q : ℕ) (e : ℤ) (hq : 0 < q)
    (he : IsCoprime e (q : ℤ)) :
    ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c =
      ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  set f : ℤ → X.Fn l := fun r => X.act l !![1, r; 0, (q : ℤ)] c with hf
  have step : ∀ x : ℤ, X.act l !![1, x; 0, (q : ℤ)] c = f (x % q) := by
    intro x
    have hm : !![1, x; 0, (q : ℤ)] = !![(1 : ℤ), x / q; 0, 1] * !![1, x % q; 0, (q : ℤ)] := by
      have := Int.emod_add_mul_ediv x q
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
    rw [hm, ← Tower.act_act Ω ε X l _ _ (by simp [Matrix.det_fin_two]) (by simp [Matrix.det_fin_two]; exact hq), hc]
  let g : ℕ → ℕ := fun j => (((j : ℤ) * e) % q).toNat
  have hg : ∀ j, ((g j : ℕ) : ℤ) = ((j : ℤ) * e) % q := fun j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hq'.ne')
  have hgr : ∀ j, g j < q := fun j => by
    have h1 := Int.emod_lt_of_pos ((j : ℤ) * e) hq'
    have h2 := hg j
    omega
  have hinj : Set.InjOn g (Finset.range q) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have h : ((i : ℤ) * e) % q = ((j : ℤ) * e) % q := by rw [← hg, ← hg, hij]
    have hd : (q : ℤ) ∣ ((j : ℤ) - i) * e := by
      rw [sub_mul]; exact (Int.ModEq.dvd h)
    have hd' : (q : ℤ) ∣ (j : ℤ) - i := he.symm.dvd_of_dvd_mul_right hd
    have h0 := Int.eq_zero_of_abs_lt_dvd hd' (by rw [abs_lt]; constructor <;> omega)
    omega
  have himg : (Finset.range q).image g = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_image] at hr; obtain ⟨j, _, rfl⟩ := hr; exact Finset.mem_range.2 (hgr j)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c
      = ∑ j ∈ Finset.range q, f ((g j : ℕ) : ℤ) := by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [step, hg]
    _ = ∑ r ∈ (Finset.range q).image g, f (r : ℤ) := (Finset.sum_image (f := fun r : ℕ => f (r : ℤ)) hinj).symm
    _ = ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by rw [himg]

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameClassLimitOfNormCompatibleShapiroSystem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA.TameLim

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  haveI : Module.Finite ℤ_[l] c.O := c.fin
  have hi : IsIntegral ℤ_[l] x := by
    have h := (isIntegral_algHom_iff (c.O.val.restrictScalars ℤ_[l]) Subtype.val_injective).2
      (Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : c.O))
    simpa using h
  have hq : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  change spectralValue (minpoly ℚ_[l] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem inv_pow_mem (c : Coef l) (e k : ℕ) (h : k = 0 ∨ ¬ l ∣ k) : (((k : ℕ) : Qbar l) ^ e)⁻¹ ∈ c.O := by
  rcases h with rfl | h
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · simpa using c.O.one_mem
    · simpa [zero_pow he.ne'] using c.O.zero_mem
  · have hk : IsUnit ((k : ℤ_[l])) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_def]
      push_cast
      rw [Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h
    obtain ⟨u, hu⟩ := hk.pow e
    have e1 : (((k : ℕ) : Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [map_units_inv (algebraMap ℤ_[l] (Qbar l)) u, hu, map_pow, map_natCast]
    rw [e1]
    exact c.O.algebraMap_mem _

theorem val_unit (r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    (x : ZMod (l ^ r)).val = 0 ∨ ¬ l ∣ (x : ZMod (l ^ r)).val := by
  have hp : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · left
    haveI : NeZero (l ^ 0) := ⟨by simp⟩
    have := ZMod.val_lt (x : ZMod (l ^ 0))
    exact Nat.lt_one_iff.mp (lt_of_lt_of_eq this (pow_zero l))
  · right
    intro hd
    have hc := ZMod.val_coe_unit_coprime x
    have h2 : l ∣ Nat.gcd (x : ZMod (l ^ r)).val (l ^ r) := Nat.dvd_gcd hd (dvd_pow_self l (by omega))
    rw [hc] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

theorem mul_sub_mul_le (a a' u u' : Qbar l) (C : ℝ) (ha' : ‖a'‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    (h1 : ‖a' - a‖ ≤ C) (h2 : ‖u' - u‖ ≤ C) : ‖a' * u' - a * u‖ ≤ C := by
  have e : a' * u' - a * u = a' * (u' - u) + (a' - a) * u := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) ha').trans h2
  · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans h1

end GlobalTheory.KA.TameLim

namespace GlobalTheory.KA.TameLim

theorem core (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (n : ℕ)
    (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (y : G ℚ Ω → Fin 2 → Qbar l) (P : Qbar l) (b : ℕ → Fin 2 → Qbar l)
    (hWO : ∀ s i j, mat W s i j ∈ c.O) (hWρ : ∀ s, mat W s = (θ s : Qbar l) • ρ s)
    (hρO : ∀ s i j, ρ s i j ∈ c.O) (hηO : ∀ r x, η r x ∈ c.O)
    (hηc : ∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖η (r + 1) x - η r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hηa : ∀ r s x, ‖η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hSh : ∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r))
    (hcont : ∀ r x i, Continuous fun s => Yw r s x i)
    (hYO : ∀ r s x i, Yw r s x i ∈ c.O)
    (hnc : ∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s)
    (hb : ∀ r i, b r i ∈ c.O)
    (hrel : ∀ r s i, ‖(∑ a, spec (η r) (fun s x => Yw r s (a, x)) s) i - (P • y s + (mat W s *ᵥ b r - b r)) i‖ ≤
      ‖((l : ℕ) : Qbar l) ^ r‖) :
    ∃ (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (b' : Fin 2 → Qbar l), ShCoc (mat W) ψ Y ∧
      (∀ x i, Continuous fun s => Y s x i) ∧ (∀ s x i, Y s x i ∈ c.O) ∧ (∀ i, b' i ∈ c.O) ∧
      (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b')) ∧
      ∀ r s x i, ‖Y s x i - spec (η r) (fun s x' => Yw r s (x, x')) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hq := GlobalTheory.norm_natCast_prime_qbar l
  have hC : ∀ r : ℕ, (0 : ℝ) ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := fun r => norm_nonneg _
  have ht0 : Filter.Tendsto (fun r : ℕ => ‖((l : ℕ) : Qbar l) ^ r‖) Filter.atTop (nhds 0) := by
    simp only [norm_pow]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq
  have hzero : ∀ z : Qbar l, (∀ r, ‖z‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → z = 0 := fun z hz =>
    norm_le_zero_iff.mp (ge_of_tendsto' ht0 hz)
  have n1 : ∀ {x : Qbar l}, x ∈ c.O → ‖x‖ ≤ 1 := fun hx => norm_le_one_of_mem c hx
  have hMle : ∀ s i j, ‖mat W s i j‖ ≤ 1 := fun s i j => n1 (hWO s i j)
  have hρle : ∀ s i j, ‖ρ s i j‖ ≤ 1 := fun s i j => n1 (hρO s i j)

  set Yr : ℕ → G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l :=
    fun r s a => spec (η r) (fun s x => Yw r s (a, x)) s with hYr
  have hYr_apply : ∀ r s a i, Yr r s a i = ∑ x, η r x * Yw r s (a, x) i := by
    intro r s a i; simp only [hYr, spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hYrO : ∀ r s a i, Yr r s a i ∈ c.O := by
    intro r s a i; rw [hYr_apply]
    exact Subalgebra.sum_mem _ fun x _ => Subalgebra.mul_mem _ (hηO r x) (hYO r s (a, x) i)

  have hslice : ∀ a r s, (fun x => Yw r s (a, x)) = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (fun s x' => Yw (r + 1) s (a, x')) s := by
    intro a r s; funext x
    rw [hnc r s]
    simp only [push]
    refine Finset.sum_nbij' (fun p => p.2) (fun x' => (a, x')) ?_ ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq] at hp ⊢; exact hp.2
    · intro x' hx'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq, id] at hx' ⊢; first | exact hx' | exact ⟨rfl, hx'⟩
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq, id] at hp
      exact Prod.ext hp.1.symm rfl
    · intro x' _; rfl
    · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.map, Prod.mk.injEq, id] at hp
      rw [← hp.1]
  have hstep : ∀ r s a i, ‖Yr (r + 1) s a i - Yr r s a i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    intro r s a i
    exact spec_cauchy l (fun r s x => Yw r s (a, x)) η (fun r s x i => n1 (hYO r s (a, x) i))
      (fun r x => n1 (hηO r x)) (fun r s => hslice a r s) hηc r s i
  have hlim : ∀ s a i, ∃ v ∈ c.O, ∀ r, ‖v - Yr r s a i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
    fun s a i => GlobalTheory.coef_limit l c (fun r => Yr r s a i) (fun r => hYrO r s a i) (fun r => hstep r s a i)
  choose Y hYO' hYap using hlim

  have happ : ∀ r s t a i, ‖Yr r (s * t) a i - (Yr r s a + mat W s *ᵥ Yr r t (a * ψ s)) i‖ ≤
      ‖((l : ℕ) : Qbar l) ^ r‖ := by
    intro r s t a i
    have key : Yr r (s * t) a - (Yr r s a + mat W s *ᵥ Yr r t (a * ψ s)) =
        ρ s *ᵥ ∑ x, (η r (x * cycMod ℚ Ω l r s) - η r x * (θ s : Qbar l)) • Yw r t (a * ψ s, x) := by
      have h1 : Yr r (s * t) a = Yr r s a +
          ρ s *ᵥ ∑ x, η r x • Yw r t (a * ψ s, x * (cycMod ℚ Ω l r s)⁻¹) := by
        simp only [hYr, spec, hSh r s t, smul_add, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul,
          Prod.mk_mul_mk, MonoidHom.prod_apply, MonoidHom.inv_apply]
      have hre : ∑ x, η r x • Yw r t (a * ψ s, x * (cycMod ℚ Ω l r s)⁻¹) =
          ∑ x, η r (x * cycMod ℚ Ω l r s) • Yw r t (a * ψ s, x) :=
        Fintype.sum_equiv (Equiv.mulRight (cycMod ℚ Ω l r s)⁻¹) _ _ (fun x => by simp)
      rw [h1, hre, hWρ s]
      simp only [hYr, spec]
      rw [Matrix.smul_mulVec, ← Matrix.mulVec_smul, add_sub_add_left_eq_sub, ← Matrix.mulVec_sub]
      congr 1
      simp only [Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, sub_smul, mul_comm (θ s : Qbar l)]
    rw [← Pi.sub_apply, key]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hC r)
    intro j _
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hρle s i j)) ?_
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hC r)
    intro x _
    rw [norm_mul]
    exact le_trans (mul_le_of_le_one_right (norm_nonneg _) (n1 (hYO r t _ j))) (hηa r s x)

  have hcoc : ShCoc (mat W) ψ Y := by
    intro s t a
    funext i
    rw [← sub_eq_zero]
    apply hzero
    intro r
    have e : Y (s * t) a i - (Y s a + mat W s *ᵥ Y t (a * ψ s)) i =
        (Y (s * t) a i - Yr r (s * t) a i) + (Yr r (s * t) a i - (Yr r s a + mat W s *ᵥ Yr r t (a * ψ s)) i)
          + (Yr r s a i - Y s a i) + (mat W s *ᵥ (Yr r t (a * ψ s) - Y t (a * ψ s))) i := by
      simp only [Pi.add_apply, Matrix.mulVec_sub, Pi.sub_apply]; ring
    rw [e]
    have hM : ‖(mat W s *ᵥ (Yr r t (a * ψ s) - Y t (a * ψ s))) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hC r)
      intro j _
      rw [norm_mul, norm_sub_rev]
      exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hMle s i j)) (hYap t (a * ψ s) j r)
    have h3 : ‖Yr r s a i - Y s a i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
      rw [norm_sub_rev]; exact hYap s a i r
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hYap _ _ _ r) (happ r s t a i))) h3)) hM)

  have hcontY : ∀ x i, Continuous fun s => Y s x i := by
    intro x i
    have hu : TendstoUniformly (fun r s => Yr r s x i) (fun s => Y s x i) Filter.atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [ht0.eventually (gt_mem_nhds hε)] with r hr s
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hYap s x i r) hr
    refine hu.continuous (Filter.Frequently.of_forall fun r => ?_)
    simp only [hYr_apply]
    exact continuous_finsetSum _ fun x' _ => continuous_const.mul (hcont r (x, x') i)

  obtain ⟨b', hb'K, φ, hφ, hφt⟩ := (isCompact_univ_pi (fun _ : Fin 2 => GlobalTheory.Coef.isCompact_O l c)).tendsto_subseq
    (x := b) (fun r => Set.mem_univ_pi.mpr (hb r))
  have hb'O : ∀ i, b' i ∈ c.O := fun i => Set.mem_univ_pi.mp hb'K i
  have hsum : ∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b') := by
    intro s; funext i
    have hφ0 : Filter.Tendsto (fun k => ‖((l : ℕ) : Qbar l) ^ φ k‖) Filter.atTop (nhds 0) :=
      ht0.comp hφ.tendsto_atTop
    have h1 : Filter.Tendsto (fun k => (∑ x, Yr (φ k) s x) i) Filter.atTop (nhds ((∑ x, Y s x) i)) := by
      simp only [Finset.sum_apply]
      refine tendsto_finsetSum _ fun x _ => ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hφ0
      rw [norm_sub_rev]; exact hYap s x i (φ k)
    have hg : Continuous fun v : Fin 2 → Qbar l => (P • y s + (mat W s *ᵥ v - v)) i := by
      fun_prop
    have h2 : Filter.Tendsto (fun k => (P • y s + (mat W s *ᵥ b (φ k) - b (φ k))) i) Filter.atTop
        (nhds ((P • y s + (mat W s *ᵥ b' - b')) i)) :=
      (hg.tendsto b').comp hφt
    have h3 : Filter.Tendsto (fun k => (∑ x, Yr (φ k) s x) i - (P • y s + (mat W s *ᵥ b (φ k) - b (φ k))) i)
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hrel (φ k) s i) hφ0
    exact sub_eq_zero.mp (tendsto_nhds_unique (h1.sub h2) h3)
  exact ⟨Y, b', hcoc, hcontY, hYO', hb'O, hsum, fun r s x i => hYap s x i r⟩

end GlobalTheory.KA.TameLim

namespace GlobalTheory.KA

theorem tame_limit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (e n : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l) (P : Qbar l) (b : ℕ → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x, χ r x ∈ c.O) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) → (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) → P ∈ c.O → (∀ r i, b r i ∈ c.O) → (∀ s i, y s i ∈ c.O) → (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i - (P • y s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∃ (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (b' : Fin 2 → Qbar l), ShCoc (mat W) ψ Y ∧ (∀ x i, Continuous fun s => Y s x i) ∧ (∀ s x i, Y s x i ∈ c.O) ∧ (∀ i, b' i ∈ c.O) ∧ (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b')) ∧ ∀ r s x i, ‖Y s x i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x' => Yw r s (x, x')) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l _ Ω _ _ W c e n χ θ ρ ψ Yw y P b hWO hWρ hρO hχO hχc hηa hSh hcont hYO hnc _ hb _ hrel
  refine TameLim.core l Ω W c n (fun r x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) θ ρ ψ Yw y P b
    hWO hWρ hρO (fun r x => Subalgebra.mul_mem _ (TameLim.inv_pow_mem c e _ (TameLim.val_unit r x)) (hχO r x))
    (fun r x => ?_) hηa hSh hcont hYO hnc hb hrel
  exact TameLim.mul_sub_mul_le _ _ _ _ _
    (TameLim.norm_le_one_of_mem c (TameLim.inv_pow_mem c e _ (TameLim.val_unit (r + 1) x)))
    (TameLim.norm_le_one_of_mem c (hχO r _)) (GlobalTheory.PowCong.powCong l e r x).1 (hχc r x)

end GlobalTheory.KA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoCocycleModPowCoboundaryOfFrobeniusSplit
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.FrobCob

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def J (l : ℕ) [Fact l.Prime] (n : ℕ) : AddSubgroup (Qbar l) where
  carrier := {x | ‖x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖}
  zero_mem' := by simp only [Set.mem_setOf_eq, norm_zero]; exact norm_nonneg _
  add_mem' := fun ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' := fun ha => by simpa only [Set.mem_setOf_eq, norm_neg] using ha

theorem cg_iff {n : ℕ} {a b : Qbar l} : Cg n a b ↔ a - b ∈ J l n := Iff.rfl

theorem mul_memJ {n : ℕ} {x y : Qbar l} (hy : ‖y‖ ≤ 1) (hx : x ∈ J l n) : y * x ∈ J l n := by
  show ‖y * x‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul hy hx (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul _))

theorem natMul_memJ (n q : ℕ) {y : Qbar l} (hy : ‖y‖ ≤ 1) : ((l ^ n * q : ℕ) : Qbar l) * y ∈ J l n := by
  show ‖_‖ ≤ _
  rw [norm_mul, Nat.cast_mul, norm_mul, Nat.cast_pow]
  have h1 := IsUltrametricDist.norm_natCast_le_one (Qbar l) q
  calc _ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ * 1 * 1 := by gcongr
    _ = _ := by ring

theorem eps_mul' (s t : G ℚ Ω) : eps l (s * t) = eps l s * eps l t := by
  simp [eps, map_mul]

theorem eps_pow' (s : G ℚ Ω) (i : ℕ) : eps l (s ^ i) = eps l s ^ i := by
  simp [eps, map_pow]

def Tr (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (j : ℕ) : Qbar l :=
  Nat.rec (motive := fun _ => Qbar l) (ξ 1 1) (fun i t => t - ξ (g ^ i) g) j

theorem Tr_zero (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) : Tr ξ g 0 = ξ 1 1 := rfl

theorem Tr_succ (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (j : ℕ) : Tr ξ g (j + 1) = Tr ξ g j - ξ (g ^ j) g := rfl

theorem Tr_mem (c : Coef l) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hint : ∀ s t, ξ s t ∈ c.O) :
    ∀ j, Tr ξ g j ∈ c.O
  | 0 => by rw [Tr_zero]; exact hint 1 1
  | j + 1 => by rw [Tr_succ]; exact sub_mem (Tr_mem c ξ g hint j) (hint _ _)

theorem Tr_key (n : ℕ) (D : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hg : g ∈ D)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s)) (i : ℕ) :
    ∀ j, ξ (g ^ i) (g ^ j) - (eps l g ^ i * Tr ξ g j - Tr ξ g (i + j) + Tr ξ g i) ∈ J l n
  | 0 => by
    have h := (cg_iff).1 (hcoc (g ^ i) (pow_mem hg i) 1 D.one_mem 1 D.one_mem)
    simp only [mul_one, eps_pow'] at h
    have e : ξ (g ^ i) (g ^ 0) - (eps l g ^ i * Tr ξ g 0 - Tr ξ g (i + 0) + Tr ξ g i) =
        -(eps l g ^ i * ξ 1 1 + ξ (g ^ i) 1 - (ξ (g ^ i) 1 + ξ (g ^ i) 1)) := by
      simp only [pow_zero, add_zero, Tr_zero]; ring
    rw [e]; exact neg_mem h
  | j + 1 => by
    have ih := Tr_key n D ξ g hg hcoc i j
    have h := (cg_iff).1 (hcoc (g ^ i) (pow_mem hg i) (g ^ j) (pow_mem hg j) g hg)
    rw [eps_pow', ← pow_succ, ← pow_add] at h
    have e : ξ (g ^ i) (g ^ (j + 1)) - (eps l g ^ i * Tr ξ g (j + 1) - Tr ξ g (i + (j + 1)) + Tr ξ g i) =
        (eps l g ^ i * ξ (g ^ j) g + ξ (g ^ i) (g ^ (j + 1)) - (ξ (g ^ (i + j)) g + ξ (g ^ i) (g ^ j))) +
        (ξ (g ^ i) (g ^ j) - (eps l g ^ i * Tr ξ g j - Tr ξ g (i + j) + Tr ξ g i)) := by
      rw [← add_assoc i j 1]; simp only [Tr_succ]; ring
    rw [e]; exact add_mem h ih

theorem Tr_period (n : ℕ) (c : Coef l) (D K : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hg : g ∈ D)
    (m : ℕ) (hgm : g ^ m ∈ K) (hepsK : ∀ k ∈ K, Cg n (eps l k) 1) (hint : ∀ s t, ξ s t ∈ c.O)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s))
    (hinv : ∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) (j : ℕ) :
    Tr ξ g (m + j) - (Tr ξ g j + (Tr ξ g m - Tr ξ g 0)) ∈ J l n := by
  have km := Tr_key n D ξ g hg hcoc m j
  have k0 := Tr_key n D ξ g hg hcoc 0 j
  have hi := (cg_iff).1 (hinv 1 D.one_mem (g ^ j) (pow_mem hg j) (g ^ m) hgm).1
  rw [one_mul] at hi
  have he : (eps l g ^ m - 1) ∈ J l n := by
    have := (cg_iff).1 (hepsK _ hgm); rwa [eps_pow'] at this
  have hT := CupCob.norm_le_one_of_mem c (Tr_mem c ξ g hint j)
  have em := mul_memJ hT he
  have e : Tr ξ g (m + j) - (Tr ξ g j + (Tr ξ g m - Tr ξ g 0)) =
      Tr ξ g j * (eps l g ^ m - 1) - (-(ξ (g ^ m) (g ^ j) - (eps l g ^ m * Tr ξ g j - Tr ξ g (m + j) + Tr ξ g m)) +
        (ξ (g ^ m) (g ^ j) - ξ 1 (g ^ j)) +
        (ξ (g ^ 0) (g ^ j) - (eps l g ^ 0 * Tr ξ g j - Tr ξ g (0 + j) + Tr ξ g 0))) := by
    simp only [pow_zero, zero_add]; ring
  rw [e]; exact sub_mem em (add_mem (add_mem (neg_mem km) hi) k0)

theorem Tr_periods (n : ℕ) (c : Coef l) (D K : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hg : g ∈ D)
    (m : ℕ) (hgm : g ^ m ∈ K) (hepsK : ∀ k ∈ K, Cg n (eps l k) 1) (hint : ∀ s t, ξ s t ∈ c.O)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s))
    (hinv : ∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) (j : ℕ) :
    ∀ t : ℕ, Tr ξ g (m * t + j) - (Tr ξ g j + (t : Qbar l) * (Tr ξ g m - Tr ξ g 0)) ∈ J l n
  | 0 => by simp only [mul_zero, zero_add, Nat.cast_zero, zero_mul, add_zero, sub_self]; exact zero_mem _
  | t + 1 => by
    have ih := Tr_periods n c D K ξ g hg m hgm hepsK hint hcoc hinv j t
    have hp := Tr_period n c D K ξ g hg m hgm hepsK hint hcoc hinv (m * t + j)
    have e1 : m * (t + 1) + j = m + (m * t + j) := by ring
    rw [e1]
    have e : Tr ξ g (m + (m * t + j)) - (Tr ξ g j + ((t + 1 : ℕ) : Qbar l) * (Tr ξ g m - Tr ξ g 0)) =
        (Tr ξ g (m + (m * t + j)) - (Tr ξ g (m * t + j) + (Tr ξ g m - Tr ξ g 0))) +
        (Tr ξ g (m * t + j) - (Tr ξ g j + (t : Qbar l) * (Tr ξ g m - Tr ξ g 0))) := by
      push_cast; ring
    rw [e]; exact add_mem hp ih

theorem Tr_mod (n : ℕ) (c : Coef l) (D K : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (g : G ℚ Ω) (hg : g ∈ D)
    (m : ℕ) (hgm : g ^ m ∈ K) (hepsK : ∀ k ∈ K, Cg n (eps l k) 1) (hint : ∀ s t, ξ s t ∈ c.O)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s))
    (hinv : ∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) (j : ℕ) :
    Tr ξ g j - Tr ξ g (j % (m * l ^ n)) ∈ J l n := by
  have h := Tr_periods n c D K ξ g hg m hgm hepsK hint hcoc hinv (j % (m * l ^ n)) (l ^ n * (j / (m * l ^ n)))
  have ej : m * (l ^ n * (j / (m * l ^ n))) + j % (m * l ^ n) = j := by
    rw [← mul_assoc]; exact Nat.div_add_mod j (m * l ^ n)
  rw [ej] at h
  have hd : ‖Tr ξ g m - Tr ξ g 0‖ ≤ 1 :=
    CupCob.norm_le_one_of_mem c (sub_mem (Tr_mem c ξ g hint m) (Tr_mem c ξ g hint 0))
  have h2 := natMul_memJ (l := l) n (j / (m * l ^ n)) hd
  have e : Tr ξ g j - Tr ξ g (j % (m * l ^ n)) =
      (Tr ξ g j - (Tr ξ g (j % (m * l ^ n)) + ((l ^ n * (j / (m * l ^ n)) : ℕ) : Qbar l) * (Tr ξ g m - Tr ξ g 0))) +
      ((l ^ n * (j / (m * l ^ n)) : ℕ) : Qbar l) * (Tr ξ g m - Tr ξ g 0) := by ring
  rw [e]; exact add_mem h h2

theorem isLocallyConstant_hom {Γ H : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [Group H] (χ : Γ →* H) (hχ : IsOpen (χ.ker : Set Γ)) : IsLocallyConstant χ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set Γ) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  rw [map_mul, map_inv, inv_mul_eq_one] at hg'
  exact hg'.symm

theorem twoCocycleModPow_coboundary_of_frobenius_split (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ)
    (D K : Subgroup (G ℚ Ω)) (φ : ↥D) (m : ℕ) (d : ↥D →* Multiplicative (ZMod (m * l ^ n)))
    (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (hm : 0 < m) (hφm : ((φ ^ m : ↥D) : G ℚ Ω) ∈ K) (hker : IsOpen (d.ker : Set ↥D))
    (hdec : ∀ s : ↥D, (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥D) : G ℚ Ω) ∈ K)
    (hepsK : ∀ k ∈ K, Cg n (eps l k) 1) (hint : ∀ s t, ξ s t ∈ c.O)
    (hcoc : ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s))
    (hinv : ∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) :
    Cob2 c n D ξ := by
  classical
  haveI : NeZero (m * l ^ n) := ⟨Nat.mul_ne_zero hm.ne' (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  set g : G ℚ Ω := (φ : G ℚ Ω) with hgdef
  have hg : g ∈ D := φ.2
  have hgm : g ^ m ∈ K := by simpa [hgdef] using hφm
  set k : ↥D → ℕ := fun s => (Multiplicative.toAdd (d s)).val with hkdef
  set T := Tr ξ g with hT
  refine ⟨fun s => if h : s ∈ D then T (k ⟨s, h⟩) else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun s : ↥D => T (k s)) :=
      ((isLocallyConstant_hom d hker).comp fun z => T (Multiplicative.toAdd z).val).continuous
    exact hc.congr fun s => by simp [Set.restrict, s.2]
  · intro s; dsimp only; split_ifs
    · exact Tr_mem c ξ g hint _
    · exact zero_mem _
  · intro s hs t ht
    rw [cg_iff]
    set s' : ↥D := ⟨s, hs⟩
    set t' : ↥D := ⟨t, ht⟩
    set a := k s' with ha
    set b := k t' with hb
    have hst : s * t ∈ D := D.mul_mem hs ht
    simp only [dif_pos hs, dif_pos ht, dif_pos hst]
    have hk : k ⟨s * t, hst⟩ = (a + b) % (m * l ^ n) := by
      show (Multiplicative.toAdd (d (s' * t'))).val = _
      rw [map_mul, toAdd_mul, ZMod.val_add]
    rw [hk]
    set κ1 : G ℚ Ω := (((φ ^ a)⁻¹ * s' : ↥D) : G ℚ Ω) with hκ1
    set κ2 : G ℚ Ω := (((φ ^ b)⁻¹ * t' : ↥D) : G ℚ Ω) with hκ2
    have hK1 : κ1 ∈ K := hdec s'
    have hK2 : κ2 ∈ K := hdec t'
    have es : g ^ a * κ1 = s := by simp [hκ1, hgdef, s']
    have et : g ^ b * κ2 = t := by simp [hκ2, hgdef, t']
    have i1 := (cg_iff).1 (hinv (g ^ a) (pow_mem hg a) t ht κ1 hK1).1
    rw [es] at i1
    have i2 := (cg_iff).1 (hinv (g ^ a) (pow_mem hg a) (g ^ b) (pow_mem hg b) κ2 hK2).2
    rw [et] at i2
    have kk := Tr_key n D ξ g hg hcoc a b
    have md := Tr_mod n c D K ξ g hg m hgm hepsK hint hcoc hinv (a + b)
    have he := (cg_iff).1 (hepsK κ1 hK1)
    have hn1 : ‖eps l g ^ a * T b‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (CupCob.norm_le_one_of_mem c (CupCob.eps_mem c g)))
        (norm_nonneg _) (CupCob.norm_le_one_of_mem c (Tr_mem c ξ g hint b))
    have em := mul_memJ hn1 he
    have eeps : eps l s = eps l g ^ a * eps l κ1 := by rw [← es, eps_mul', eps_pow']
    rw [eeps]
    have e : ξ s t - (eps l g ^ a * eps l κ1 * T b - T ((a + b) % (m * l ^ n)) + T a) =
        (ξ s t - ξ (g ^ a) t) + (ξ (g ^ a) t - ξ (g ^ a) (g ^ b)) +
        (ξ (g ^ a) (g ^ b) - (eps l g ^ a * T b - T (a + b) + T a)) -
        eps l g ^ a * T b * (eps l κ1 - 1) - (T (a + b) - T ((a + b) % (m * l ^ n))) := by ring
    rw [e]
    exact sub_mem (sub_mem (add_mem (add_mem i1 i2) kk) em) md

end GlobalTheory.Ord2.FrobCob
end
end

