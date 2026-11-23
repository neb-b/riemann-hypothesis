module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertQExpPadicCongruencePowPrimePow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.QPow

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {p : ℕ} [Fact p.Prime] {ι : Qbar p ≃+* ℂ}

theorem norm_p (ι : Qbar p ≃+* ℂ) : ‖ι.symm (p : ℂ)‖ = (p : ℝ)⁻¹ := by
  rw [map_natCast]
  have h : ‖(algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]))‖ = ‖(p : ℚ_[p])‖ :=
    PadicAlgCl.norm_extends p _
  rw [map_natCast, Padic.norm_p] at h
  exact h

private theorem hasQ_const (c : ℂ) :
    HasQ (F := F) (fun _ : Hn F => c) (({0} : Set F).indicator fun _ => c) := by
  classical
  refine ⟨⟨1, one_pos, fun ξ hξ => ?_⟩, fun z => ?_⟩
  · have h0 : ξ = 0 := by
      by_contra hne
      exact hξ (by simp [Set.indicator_apply, hne])
    subst h0
    refine ⟨Or.inl rfl, ?_⟩
    rw [mul_zero]
    exact isIntegral_zero
  · have h := hasSum_single
      (f := fun ξ : F => (({0} : Set F).indicator (fun _ => c) ξ) * ez ξ z) 0
      (fun b hb => by simp [Set.indicator_apply, hb])
    convert h using 1
    simp [Set.indicator_apply, ez, reAt]

theorem small_const {r : ℝ} {g : Hn F → ℂ} (h : Small ι r g) (c : ℂ) :
    Small (F := F) ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  classical
  refine ⟨_, hasQ_const c, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · simp [Set.indicator_apply, hξ]
  · simp [Set.indicator_apply, hξ]

theorem small_mono {r s : ℝ} {g : Hn F → ℂ} (h : Small ι r g) (hrs : r ≤ s) : Small ι s g := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨a, ha, fun ξ => (hb ξ).trans hrs⟩

private theorem hasQ_add {f g : Hn F → ℂ} {a b : F → ℂ} (hf : HasQ f a) (hg : HasQ g b) :
    HasQ (f + g) (a + b) := by
  obtain ⟨⟨D, hD, hDa⟩, ha⟩ := hf
  obtain ⟨⟨E, hE, hEb⟩, hb⟩ := hg
  refine ⟨⟨D * E, Nat.mul_pos hD hE, fun ξ hξ => ?_⟩, fun z => ?_⟩
  · by_cases h0 : a ξ = 0
    · have hb0 : b ξ ≠ 0 := by
        intro hb0
        apply hξ
        simp [h0, hb0]
      obtain ⟨h1, h2⟩ := hEb ξ hb0
      refine ⟨h1, ?_⟩
      have h3 := (isIntegral_natCast (R := ℤ) (B := F) D).mul h2
      have e : ((D * E : ℕ) : F) * ξ = (D : F) * ((E : F) * ξ) := by
        push_cast
        ring
      rw [e]
      exact h3
    · obtain ⟨h1, h2⟩ := hDa ξ h0
      refine ⟨h1, ?_⟩
      have h3 := (isIntegral_natCast (R := ℤ) (B := F) E).mul h2
      have e : ((D * E : ℕ) : F) * ξ = (E : F) * ((D : F) * ξ) := by
        push_cast
        ring
      rw [e]
      exact h3
  · have h := (ha z).add (hb z)
    simp only [Pi.add_apply, add_mul]
    exact h

theorem small_add {r s : ℝ} {f g : Hn F → ℂ} (hf : Small ι r f) (hg : Small ι s g) : Small ι (max r s) (f + g) := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hg
  refine ⟨a + b, hasQ_add ha hb, fun ξ => ?_⟩
  rw [Pi.add_apply, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (ha' ξ) (hb' ξ))

theorem small_mul {r s : ℝ} {f g : Hn F → ℂ} (hf : Small ι r f) (hg : Small ι s g) : Small ι (r * s) (f * g) := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hg
  have hr : 0 ≤ r := (norm_nonneg _).trans (ha' 0)
  have hs : 0 ≤ s := (norm_nonneg _).trans (hb' 0)
  obtain ⟨c, hc, hc'⟩ := hasQ_mul F f g a b ha hb
  refine ⟨c, hc, fun ξ => ?_⟩
  obtain ⟨t, ht⟩ := hc' ξ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ht, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun η _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul (ha' η) (hb' (ξ - η)) (norm_nonneg _) hr

theorem small_nonneg {r : ℝ} {f : Hn F → ℂ} (hf : Small ι r f) : 0 ≤ r := by
  obtain ⟨a, -, hb⟩ := hf
  exact (norm_nonneg _).trans (hb 0)

theorem small_zero {r : ℝ} {f : Hn F → ℂ} (hf : Small ι r f) : Small ι r (0 : Hn F → ℂ) := by
  refine ⟨0, ⟨⟨1, one_pos, fun ξ hξ => (hξ rfl).elim⟩, fun z => ?_⟩, fun ξ => ?_⟩
  · simpa using (hasSum_zero : HasSum (fun _ : F => (0 : ℂ)) 0)
  · simpa using small_nonneg hf

theorem pow_sub_one {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ 1) :
    ∀ m : ℕ, Small ι r (f ^ m - 1) := by
  have hr0 := small_nonneg h
  intro m
  induction m with
  | zero => simpa using small_zero h
  | succ m ih =>
    have e : f ^ (m + 1) - 1 = (f ^ m - 1) * (f - 1) + ((f ^ m - 1) + (f - 1)) := by ring
    rw [e]
    have h1 := small_add (small_mul ih h) (small_add ih h)
    refine small_mono h1 ?_
    rw [max_self]
    exact max_le (mul_le_of_le_one_left hr0 hr) le_rfl

theorem sum_small {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ (p : ℝ)⁻¹) :
    ∀ n : ℕ, Small ι (p : ℝ)⁻¹ (∑ i ∈ Finset.range n, (f ^ i - 1)) := by
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hs : Small ι (p : ℝ)⁻¹ (f - 1) := small_mono h hr
  intro n
  induction n with
  | zero => simpa using small_zero hs
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := small_add ih (pow_sub_one hs hp1 n)
    rwa [max_self] at h1

theorem pow_p {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ (p : ℝ)⁻¹) :
    Small ι (r * (p : ℝ)⁻¹) (f ^ p - 1) := by
  have key : ∀ x : ℂ, x ^ p - 1 =
      (x - 1) * ∑ i ∈ Finset.range p, (x ^ i - 1) + (p : ℂ) * (x - 1) := by
    intro x
    have hg := geom_sum_mul x p
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    linear_combination (-1 : ℂ) * hg
  have e : f ^ p - 1 = (f - 1) * ∑ i ∈ Finset.range p, (f ^ i - 1) +
      (fun _ : Hn F => (p : ℂ)) * (f - 1) := by
    funext z
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.one_apply, Pi.mul_apply, Pi.add_apply,
      Finset.sum_apply]
    exact key (f z)
  rw [e]
  have h1 := small_mul h (sum_small h hr p)
  have h2 := small_mul (small_const h (p : ℂ)) h
  rw [norm_p ι] at h2
  refine small_mono (small_add h1 h2) ?_
  rw [mul_comm (p : ℝ)⁻¹ r, max_self]

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ)
    (f : Hn F → ℂ), Small ι (p : ℝ)⁻¹ (f - 1) → ∀ N m : ℕ,
      Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (f ^ (p ^ N * m) - 1) := by
  intro F _ _ _ p _ ι f h N m
  have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have step : ∀ n : ℕ, Small ι ((p : ℝ)⁻¹ ^ (n + 1)) (f ^ (p ^ n) - 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have h1 := pow_p ih (pow_le_of_le_one hp0 hp1 (Nat.succ_ne_zero n))
      rw [← pow_mul, ← pow_succ, ← pow_succ] at h1
      exact h1
  have h2 := pow_sub_one (step N) (pow_le_one₀ hp0 hp1) m
  rwa [← pow_mul] at h2

end GlobalTheory.QPow

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertQExp_padicCongruence_pow_prime_pow : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (f : Hn F → ℂ), Small ι (p : ℝ)⁻¹ (f - 1) → ∀ N m : ℕ, Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (f ^ (p ^ N * m) - 1) := by
  first | exact @GlobalTheory.QPow.main | exact GlobalTheory.QPow.main | (intros; apply GlobalTheory.QPow.main <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSeedOrbitFiniteAndCongruence
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GaussSumOrbitFiniteness

theorem reAt_eq {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) : reAt v x = rhom x v := by
  simp only [reAt, rhom]
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]
  rfl

theorem scal_comm {R : Type} [CommRing R] (z : Rˣ) (A : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z * A = A * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.scalar, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, mul_comm]

theorem norm_rat {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (q : ℚ) : ‖ι.symm (q : ℂ)‖ = ‖(q : ℚ_[p])‖ := by
  rw [map_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]

theorem fermat {p : ℕ} [hp : Fact p.Prime] (r : ℚ) (hr : ‖(r : ℚ_[p])‖ = 1) :
    ‖((r : ℚ_[p]) ^ (p - 1) - 1)‖ ≤ (p : ℝ)⁻¹ := by
  set x : ℤ_[p] := ⟨r, hr.le⟩ with hxdef
  have hxn : ‖x‖ = 1 := hr
  have hx : IsUnit x := PadicInt.isUnit_iff.mpr hxn
  have h0 : PadicInt.toZMod x ≠ 0 := by
    intro h
    have : x ∈ RingHom.ker (PadicInt.toZMod (p := p)) := h
    rw [PadicInt.ker_toZMod] at this
    exact (IsLocalRing.mem_maximalIdeal x).mp this hx
  have h1 : x ^ (p - 1) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one h0, sub_self]
  have h2 : ‖x ^ (p - 1) - 1‖ < 1 := PadicInt.mem_nonunits.mp h1
  have h3 : ‖x ^ (p - 1) - 1‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    rw [PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]; simpa using h2
  have h4 : ‖x ^ (p - 1) - 1‖ = ‖((r : ℚ_[p]) ^ (p - 1) - 1)‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [← h4]; simpa using h3

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem tp_mul {a b : F} (ha : TP a) (hb : TP b) : TP (a * b) := fun v => by
  rw [reAt_eq, map_mul, Pi.mul_apply, ← reAt_eq, ← reAt_eq]; exact mul_pos (ha v) (hb v)

theorem tp_one : TP (1 : F) := fun v => by rw [reAt_eq, map_one]; exact one_pos

theorem stab_one (g : GL (Fin 2) (Af F)) : Stab g (1 : GL (Fin 2) F) :=
  ⟨by simpa using (tp_one : TP (1 : F)), 1, 1, (KLev F 2 1).one_mem, by simp⟩

theorem stab_mul (g : GL (Fin 2) (Af F)) (γ γ' : GL (Fin 2) F) (h : Stab g γ) (h' : Stab g γ') : Stab g (γ * γ') := by
  obtain ⟨ht, z, u, hu, he⟩ := h
  obtain ⟨ht', z', u', hu', he'⟩ := h'
  refine ⟨?_, z' * z, u * u', (KLev F 2 1).mul_mem hu hu', ?_⟩
  · rw [Units.val_mul, Matrix.det_mul]; exact tp_mul ht ht'
  · rw [map_mul, mul_assoc, he', ← mul_assoc, ← mul_assoc, ← scal_comm, mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) z'), he, map_mul]
    simp only [mul_assoc]

theorem stab_inv (g : GL (Fin 2) (Af F)) (γ : GL (Fin 2) F) (h : Stab g γ) : Stab g γ⁻¹ := by
  obtain ⟨ht, z, u, hu, he⟩ := h
  refine ⟨?_, z⁻¹, u⁻¹, (KLev F 2 1).inv_mem hu, ?_⟩
  · have h1 : γ.val.det * (γ⁻¹).val.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    intro v
    have hv := congrArg (fun x => rhom x v) h1
    simp only [map_mul, map_one, Pi.mul_apply, Pi.one_apply] at hv
    have hp := ht v
    rw [reAt_eq] at hp ⊢
    exact (pos_iff_pos_of_mul_pos (by rw [hv]; exact one_pos)).mp hp
  · rw [map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← scal_comm, mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹), he]
    simp only [map_inv]
    group

theorem absF_ne_zero (y : (Af F)ˣ) : absF y ≠ 0 := by
  classical
  unfold absF
  rw [finprod_def]
  split_ifs with h
  · rw [Finset.prod_ne_zero_iff]
    intro w _
    rw [norm_ne_zero_iff]
    exact ((Units.map (pLoc F w).toMonoidHom y).ne_zero)
  · exact one_ne_zero

end GlobalTheory.HilbertThetaSeries.GaussSumOrbitFiniteness

namespace GlobalTheory.HilbertThetaSeries


open GlobalTheory.HilbertThetaSeries.GaussSumOrbitFiniteness in
theorem orbit_seed_finite_congr : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → {f | ∃ γ, Stab (aff y 0) γ ∧ f = sl (p - 1) (toInf γ) θ}.Finite ∧ (∀ γ, Stab (aff y 0) γ → ∀ γ', InG p δ γ' → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ') (sl (p - 1) (toInf γ) θ) - 1)) ∧ Stab (aff y 0) (1 : GL (Fin 2) F) ∧ ∀ γ γ' : GL (Fin 2) F, Stab (aff y 0) γ → Stab (aff y 0) γ' → Stab (aff y 0) (γ * γ') ∧ Stab (aff y 0) γ⁻¹ := by
  intro F _ _ _ p _ ι hp2 δ hδ θ hθ y hy
  have hk : Even (p - 1) := (Fact.out : p.Prime).even_sub_one hp2
  obtain ⟨-, hsl, hscal, htS, -⟩ := GlobalTheory.T.hilbert_slash_rational_matrix_properties F (p - 1) θ
  have hpos : ∀ γ : GL (Fin 2) F, TP γ.val.det → Pos (toInf γ) := fun γ h => (hsl γ).1.mpr h

  have hsc : ∀ (η : Fˣ) (γ : GL (Fin 2) F), TP γ.val.det →
      sl (p - 1) (toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ)) θ = sl (p - 1) (toInf γ) θ := by
    intro η γ h
    rw [map_mul, htS η]
    exact (hscal hk _ _ (hpos γ h)).2
  refine ⟨?_, ?_, stab_one _, fun γ γ' h h' => ⟨stab_mul _ γ γ' h h', stab_inv _ γ h⟩⟩
  ·
    obtain ⟨N, hN, hlev⟩ := hθ.lev
    obtain ⟨T, hT, hcov⟩ := GlobalTheory.T.stabilizer_eq_scalar_mul_congruence_mul_finset F (aff y 0) N hN
    refine ((Polynomial.nthRoots 8 (1 : ℂ)).toFinset.finite_toSet.image2
      (fun ζ τ => ζ • sl (p - 1) (toInf τ) θ) T.finite_toSet).subset ?_
    rintro f ⟨γ, hγ, rfl⟩
    obtain ⟨η, γ₀, τ, hτ, hγ₀, rfl⟩ := hcov γ hγ
    obtain ⟨ζ, hζ, hζe⟩ := hlev γ₀ hγ₀
    refine ⟨ζ, ?_, τ, hτ, ?_⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots (by norm_num)).mpr hζ
    have hdet0 : γ₀.val.det = 1 := hγ₀.1
    have hp0 : Pos (toInf γ₀) := hpos γ₀ (by rw [hdet0]; exact tp_one)
    have hpτ : Pos (toInf τ) := hpos τ (hT τ hτ).1
    have hd : TP (γ₀ * τ).val.det := by
      rw [Units.val_mul, Matrix.det_mul, hdet0, one_mul]; exact (hT τ hτ).1
    symm
    show sl (p - 1) (toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₀ * τ)) θ = ζ • sl (p - 1) (toInf τ) θ
    rw [mul_assoc, hsc η _ hd, map_mul,
      (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F (p - 1) _ _ θ hp0 hpτ).2.2.2.1, (hsl γ₀).2, hdet0, hζe]
    simp only [map_one, Rat.cast_one, abs_one, Real.one_rpow, Complex.ofReal_one, one_smul]
    exact ((slash_add_smul_pow F (p - 1) 1 (toInf τ) θ θ ζ).2.2.2.2.1)
  ·
    intro γ hγ γ' hγ'
    obtain ⟨htp, z, u, hu, he⟩ := hγ
    obtain ⟨hmulG, -, hcmp⟩ := GlobalTheory.T.exists_inG_scalar_mul_and_abs_norm_det_mul_absF_eq F p δ hδ
    obtain ⟨η, r, hG, hr0, hr1, hnorm⟩ := hcmp y y z γ u hy hy htp hu he
    set γ₁ := Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ with hγ₁
    have hN : |((Algebra.norm ℚ γ₁.val.det : ℚ) : ℝ)| = (r : ℝ) ^ 2 :=
      mul_right_cancel₀ (absF_ne_zero y) hnorm
    have hpow : (|((Algebra.norm ℚ γ₁.val.det : ℚ) : ℝ)| ^ (((p - 1 : ℕ) : ℝ) / 2) : ℝ) = (r : ℝ) ^ (p - 1) := by
      rw [hN, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast]
      congr 1; ring
    have hp1 : Pos (toInf γ₁) := hpos γ₁ hG.2.2.2.2.2
    have hp' : Pos (toInf γ') := hpos γ' hγ'.2.2.2.2.2
    set c : ℂ := (((r ^ (p - 1) : ℚ) : ℝ) : ℂ) with hc
    have e1 : sl (p - 1) (toInf γ) θ = c • sl0 (p - 1) (toInf γ₁) θ := by
      rw [← hsc η γ htp, (hsl γ₁).2, hpow, hc]; push_cast; rfl
    have hS := hθ.one (γ₁ * γ') (hmulG γ₁ γ' hG hγ')
    set F0 := sl0 (p - 1) (toInf (γ₁ * γ')) θ with hF0
    have e2 : sl0 (p - 1) (toInf γ') (sl (p - 1) (toInf γ) θ) - 1 = c • (F0 - 1) + (fun _ => c - 1) := by
      rw [e1, (slash_add_smul_pow F (p - 1) 1 (toInf γ') (sl0 (p - 1) (toInf γ₁) θ) θ c).2.1,
        ← (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F (p - 1) _ _ θ hp1 hp').2.2.1, ← map_mul, hF0]
      funext w; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]; ring
    have hcn : ‖ι.symm c‖ = 1 := by
      rw [hc, Complex.ofReal_ratCast, norm_rat, Rat.cast_pow, norm_pow, hr1, one_pow]
    have hc1 : ‖ι.symm (c - 1)‖ ≤ (p : ℝ)⁻¹ := by
      have : c - 1 = (((r ^ (p - 1) - 1 : ℚ)) : ℂ) := by rw [hc]; push_cast; ring
      rw [this, norm_rat]; push_cast; exact fermat r hr1
    obtain ⟨-, -, hA, -, -, -⟩ := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ c hS hS
    obtain ⟨-, -, -, -, -, hB⟩ := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ (c - 1) hS hS
    obtain ⟨hsum, -, -, -, -, -⟩ := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ 0 hA hB
    rw [e2]
    refine (GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι _ _ _ _ 0 hsum hS).2.2.2.1 ?_
    rw [hcn, one_mul]
    exact max_le le_rfl hc1

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_seed_orbit_finite_and_congruence : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ θ : Hn F → ℂ, Seed ι δ θ → ∀ y : (Af F)ˣ, AtP p δ y → {f | ∃ γ, Stab (aff y 0) γ ∧ f = sl (p - 1) (toInf γ) θ}.Finite ∧ (∀ γ, Stab (aff y 0) γ → ∀ γ', InG p δ γ' → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ') (sl (p - 1) (toInf γ) θ) - 1)) ∧ Stab (aff y 0) (1 : GL (Fin 2) F) ∧ ∀ γ γ' : GL (Fin 2) F, Stab (aff y 0) γ → Stab (aff y 0) γ' → Stab (aff y 0) (γ * γ') ∧ Stab (aff y 0) γ⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.orbit_seed_finite_congr | exact GlobalTheory.HilbertThetaSeries.orbit_seed_finite_congr | (intros; apply GlobalTheory.HilbertThetaSeries.orbit_seed_finite_congr <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesPeriodicInversionFormula
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem thetaSeries_periodic_slash_frickeMatrix : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a b : F) (c : Fˣ) (T : Finset (κ → F)) (Φ : (κ → F) → ℂ), a ≠ 0 → b ≠ 0 → aL κ a ≤ aL κ b → IsReps (aL κ a) (aL κ b) T → (∀ x, Φ x ≠ 0 → x ∈ aL κ b) → (∀ x, ∀ l ∈ aL κ a, Φ (x + l) = Φ x) → sl0 k (toInf (wm c)) (th G Φ) = th G (wT G k t a c T Φ) := by
  classical
  intro F _ _ _ κ _ _ G hG t ht k hk a b c T Φ ha hb hab hT hsupp hper
  have hdec : ∀ x, Φ x = ∑ x₀ ∈ T, Φ x₀ * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) := by
    intro x
    have e2 : ∀ x₀ ∈ T, Φ x₀ * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) = Φ x * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) := by
      intro x₀ _
      split_ifs with h
      · have := hper x₀ (x - x₀) h
        rw [show x₀ + (x - x₀) = x by abel] at this
        rw [this]
      · simp
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum]
    by_cases h0 : Φ x = 0
    · simp [h0]
    · obtain ⟨y, ⟨hyT, hy⟩, huniq⟩ := hT.2 x (hsupp x h0)
      rw [Finset.sum_eq_single y]
      · simp [hy]
      · intro x₀ hx₀ hne
        rw [if_neg]
        intro hm
        exact hne (huniq x₀ ⟨hx₀, hm⟩)
      · intro h
        exact absurd hyT h
  have hW : ∀ y, wT G k t a c T Φ y = ∑ x₀ ∈ T, Φ x₀ * wT G k t a c {x₀} (fun _ => 1) y := by
    intro y
    simp only [wT, Finset.sum_singleton, one_mul]
    split_ifs
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x₀ _ => by ring)
    · simp
  have hsumL : ∀ x₀ ∈ T, ∀ z : Hn F, Summable fun x => (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) * ez (QF G x) z := by
    intro x₀ hx₀ z
    refine (_root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hG b _ 1 ?_ ?_).1 z
    · intro x hx
      have hm : x - x₀ ∈ aL κ a := by
        by_contra hm
        exact hx (if_neg hm)
      have := (aL κ b).add_mem (hab hm) (hT.1 x₀ hx₀)
      simpa using this
    · intro x
      split_ifs <;> simp
  have hsumR : ∀ (x₀ : κ → F) (z : Hn F), Summable fun y => wT G k t a c {x₀} (fun _ => (1:ℂ)) y * ez (QF G y) z := by
    intro x₀ z
    obtain ⟨-, ⟨N, hN, hN2⟩, -⟩ := _root_.GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG
    have hc : (c : F) ≠ 0 := c.ne_zero
    have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    refine (_root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hG ((c:F) / ((N:F) * a)) _ ‖wC k t a (c:F)‖ ?_ ?_).1 z
    · intro y hy
      have hd : (a / c) • y ∈ dualL F G := by
        by_contra hd
        exact hy (by simp [wT, hd])
      have hw := (hN2 _ hd).1
      refine AddSubgroup.mem_map.2 ⟨_, hw, ?_⟩
      simp only [DistribSMul.toAddMonoidHom_apply]
      rw [smul_smul, smul_smul]
      rw [show (c:F) / ((N:F) * a) * (N:F) * (a / c) = 1 by field_simp, one_smul]
    · intro y
      simp only [wT, Finset.sum_singleton, one_mul]
      split_ifs
      · simp [et, Complex.norm_exp]
      · simp
  have thL : ∀ z, th G Φ z = ∑ x₀ ∈ T, Φ x₀ * th G (fun x => if x - x₀ ∈ aL κ a then (1:ℂ) else 0) z := by
    intro z
    simp only [th]
    have e : ∀ x, Φ x * ez (QF G x) z = ∑ x₀ ∈ T, Φ x₀ * ((if x - x₀ ∈ aL κ a then (1:ℂ) else 0) * ez (QF G x) z) := by
      intro x
      rw [hdec x, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [tsum_congr e, Summable.tsum_finsetSum (fun x₀ hx₀ => (hsumL x₀ hx₀ z).mul_left (Φ x₀))]
    exact Finset.sum_congr rfl (fun x₀ _ => tsum_mul_left)
  have thR : ∀ z, th G (wT G k t a c T Φ) z = ∑ x₀ ∈ T, Φ x₀ * th G (wT G k t a c {x₀} (fun _ => (1:ℂ))) z := by
    intro z
    simp only [th]
    have e : ∀ y, wT G k t a c T Φ y * ez (QF G y) z = ∑ x₀ ∈ T, Φ x₀ * (wT G k t a c {x₀} (fun _ => (1:ℂ)) y * ez (QF G y) z) := by
      intro y
      rw [hW y, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [tsum_congr e, Summable.tsum_finsetSum (fun x₀ _ => (hsumR x₀ z).mul_left (Φ x₀))]
    exact Finset.sum_congr rfl (fun x₀ _ => tsum_mul_left)
  funext z
  rw [thR z]
  simp only [sl0]
  rw [thL, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x₀ _ => ?_)
  have := congrFun (_root_.GlobalTheory.T.hilbertThetaSeries_coset_inversion_formula F κ G hG t ht k hk a c x₀ ha) z
  simp only [sl0] at this
  rw [← this]
  ring

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a b : F) (c : Fˣ) (T : Finset (κ → F)) (Φ : (κ → F) → ℂ), a ≠ 0 → b ≠ 0 → aL κ a ≤ aL κ b → IsReps (aL κ a) (aL κ b) T → (∀ x, Φ x ≠ 0 → x ∈ aL κ b) → (∀ x, ∀ l ∈ aL κ a, Φ (x + l) = Φ x) → sl0 k (toInf (wm c)) (th G Φ) = th G (wT G k t a c T Φ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix | exact GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix | (intros; apply GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix <;> assumption)
end

