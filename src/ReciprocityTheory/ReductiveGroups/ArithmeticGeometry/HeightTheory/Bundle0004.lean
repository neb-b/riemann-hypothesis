module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0002
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisExtend
section
namespace ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension

variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

noncomputable def liftY : FractionRing (MvPolynomial σ L) →+* FractionRing (MvPolynomial σ E) :=
  IsFractionRing.lift (A := MvPolynomial σ L)
    (g := (algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))).comp
      (MvPolynomial.map (algebraMap L E)))
    ((IsFractionRing.injective (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))).comp
      (MvPolynomial.map_injective _ (algebraMap L E).injective))

theorem basis_extend [FiniteDimensional L E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n L E) :
    letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) :=
      (liftY (L := L) (E := E) (σ := σ)).toAlgebra;
    ∃ b' : Module.Basis n (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)),
      (∀ i, b' i = algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E))
        (MvPolynomial.C (b i))) ∧
      ∀ e : E, Algebra.leftMulMatrix b' (algebraMap (MvPolynomial σ E)
          (FractionRing (MvPolynomial σ E)) (MvPolynomial.C e)) =
        (Algebra.leftMulMatrix b e).map (algebraMap L (FractionRing (MvPolynomial σ L))) := by

  try intro _
  letI : Algebra (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) := (liftY (L := L) (E := E) (σ := σ)).toAlgebra
  letI : Algebra (MvPolynomial σ L) (MvPolynomial σ E) := MvPolynomial.algebraMvPolynomial
  classical
  have hlift : ∀ q : MvPolynomial σ L, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) =
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.map (algebraMap L E) q) := by
    intro q
    show liftY (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) = _
    simp only [liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  have hsmul : ∀ (q : MvPolynomial σ L) (P : MvPolynomial σ E),
      q • P = MvPolynomial.map (algebraMap L E) q * P := fun q P => by
    rw [Algebra.smul_def]; rfl
  have himg : ∀ (q : MvPolynomial σ L) (P : MvPolynomial σ E),
      algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (q • P) = algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) q) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) P := by
    intro q P; rw [hsmul, map_mul, hlift]
  have hmem : ∀ P : MvPolynomial σ E, algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) P ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro P
    set_option synthInstance.maxHeartbeats 100000 in
      rw [PolynomialCoordinateBasis.eq_sum_crd b P, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [himg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent (FractionRing (MvPolynomial σ L)) (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (MvPolynomial σ L))
      Finset.univ g
    have hd' : ∀ j, ∃ a : MvPolynomial σ L, algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) a = (d : MvPolynomial σ L) • g j :=
      fun j => hd j (Finset.mem_univ j)
    choose a ha using hd'
    have h0 : algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (∑ j, a j • (MvPolynomial.C (b j) : MvPolynomial σ E)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [himg, ha]
      have e1 : ∑ j, algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) ((d : MvPolynomial σ L) • g j) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) =
          algebraMap (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E)) (algebraMap (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)) d) * ∑ j, g j • algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
      rw [e1]
      beta_reduce at hg
      rw [hg, mul_zero]
    have h1 : ∑ j, a j • (MvPolynomial.C (b j) : MvPolynomial σ E) = 0 :=
      IsFractionRing.injective _ (FractionRing (MvPolynomial σ E)) (by rw [h0, map_zero])
    have h2 := (Fintype.linearIndependent_iff.mp (PolynomialCoordinateBasis.linearIndependent_C (σ := σ) b)) a h1 i
    have h3 : (d : MvPolynomial σ L) • g i = 0 := by rw [← ha i, h2, map_zero]
    rw [Algebra.smul_def] at h3
    exact (mul_eq_zero.mp h3).resolve_left (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2)
  have hmul : ∀ x ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))), ∀ y ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))), x * y ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro x hx y hy
    have hxy := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine (Submodule.span_le.mpr ?_) hxy
    rintro _ ⟨_, ⟨k, rfl⟩, _, ⟨l, rfl⟩, rfl⟩
    show algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b k)) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b l)) ∈ _
    rw [← map_mul]; exact hmem _
  have hone : (1 : FractionRing (MvPolynomial σ E)) ∈ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by simpa using hmem 1
  have hfg : (Subalgebra.toSubmodule ((Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))))).toSubalgebra hone (fun x y hx hy => hmul x hx y hy))).FG := by
    rw [Submodule.toSubalgebra_toSubmodule]
    exact Submodule.fg_span (Set.finite_range _)
  have htop : ⊤ ≤ Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i)))) := by
    intro x _
    obtain ⟨a, q, hq, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial σ E) x
    have hint := IsIntegral.of_mem_of_fg _ hfg (algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) q) (hmem q)
    have hinv := Subalgebra.inv_mem_of_algebraic ((Submodule.span (FractionRing (MvPolynomial σ L)) (Set.range (fun i => algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b i))))).toSubalgebra hone (fun x y hx hy => hmul x hx y hy))
      (x := ⟨algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) q, hmem q⟩) hint.isAlgebraic
    rw [div_eq_mul_inv]
    exact hmul _ (hmem a) _ hinv
  refine ⟨Module.Basis.mk hli htop, fun i => Module.Basis.mk_apply _ _ _, fun e => ?_⟩
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Module.Basis.mk_apply]
  have hx : algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C e) * algebraMap (MvPolynomial σ E) (FractionRing (MvPolynomial σ E)) (MvPolynomial.C (b j)) =
      ∑ k, algebraMap L (FractionRing (MvPolynomial σ L)) (b.repr (e * b j) k) • (Module.Basis.mk hli htop) k := by
    rw [← map_mul, ← MvPolynomial.C_mul]
    conv_lhs => rw [← b.sum_repr (e * b j)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Module.Basis.mk_apply, Algebra.smul_def (algebraMap L (FractionRing (MvPolynomial σ L)) _),
      IsScalarTower.algebraMap_apply L (MvPolynomial σ L) (FractionRing (MvPolynomial σ L)), MvPolynomial.algebraMap_eq,
      ← himg, hsmul, MvPolynomial.map_C, ← MvPolynomial.C_mul, Algebra.smul_def]
  beta_reduce
  rw [hx, Module.Basis.repr_sum_self]

end ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CoeffPsiBNeZero
section
namespace ReciprocityTheory.ChartRestriction.G.T0.MHF

open MvPolynomial ReciprocityTheory.MultiplicativeHeights

variable {K : Type*} [Field K] {B n : ℕ}

def bw (b : Fin B) (s : Fin B × Fin n →₀ ℕ) : ℕ := ∑ j, s (b, j)

theorem bw_add (b : Fin B) (s t : Fin B × Fin n →₀ ℕ) : bw b (s + t) = bw b s + bw b t := by
  simp [bw, Finset.sum_add_distrib]

theorem bw_single (b : Fin B) (v : Fin B × Fin n) (e : ℕ) :
    bw b (Finsupp.single v e) = if v.1 = b then e else 0 := by
  obtain ⟨i, j⟩ := v
  by_cases h : i = b
  · subst h; simp [bw, Finsupp.single_apply]
  · simp [bw, h]

noncomputable def psiB (b : Fin B) :
    MvPolynomial (Fin B × Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin B × Fin n) K) :=
  aeval fun v => if v.1 = b then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

theorem psiB_X (b : Fin B) (v : Fin B × Fin n) :
    psiB (K := K) b (X v) = Polynomial.C (X v) * Polynomial.X ^ (if v.1 = b then 1 else 0) := by
  simp only [psiB, aeval_X]; split_ifs <;> simp

theorem psiB_monomial (b : Fin B) (s : Fin B × Fin n →₀ ℕ) (a : K) :
    psiB b (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ bw b s := by
  induction s using Finsupp.induction generalizing a
  · simp [psiB, bw, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  · rename_i v e f _ _ ih
    rw [monomial_single_add, map_mul, map_pow, ih, psiB_X, bw_add, bw_single]
    split_ifs <;> simp only [map_mul, map_pow, mul_pow, ← pow_mul, pow_add, mul_one,
      pow_zero, zero_add] <;> ring

theorem psiB_eq_of_hom (b : Fin B) (δ : ℕ) (f : MvPolynomial (Fin B × Fin n) K)
    (hf : ∀ s ∈ f.support, bw b s = δ) : psiB b f = Polynomial.C f * Polynomial.X ^ δ := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s hs => by rw [psiB_monomial, hf s hs]

theorem coeff_psiB_ne_zero (b : Fin B) (f : MvPolynomial (Fin B × Fin n) K)
    (s : Fin B × Fin n →₀ ℕ) (hs : s ∈ f.support) : (psiB b f).coeff (bw b s) ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (AddMonoidAlgebra.coeff · s) h0
  conv at h1 => lhs; rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff, coeff_sum] at h1
  simp only [psiB_monomial, Polynomial.coeff_C_mul_X_pow, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
  rw [Finset.sum_eq_single s] at h1
  · simp at h1; exact (mem_support_iff.1 hs) h1
  · intro s' _ hne
    split_ifs <;> simp [coeff_monomial, hne]
  · intro h; exact absurd hs h

theorem ntd_pow {R : Type*} [CommRing R] [IsDomain R] (p : Polynomial R) (hp : p ≠ 0) (m : ℕ) :
    (p ^ m).natTrailingDegree = m * p.natTrailingDegree := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero _ hp) hp, ih, Nat.succ_mul]

theorem isMH_of_pow (hB : 0 < B) (F0 : MvPolynomial (Fin B × Fin n) K) (κ : K) (m δ : ℕ)
    (hm : 1 ≤ m) (hκ : κ ≠ 0) (hF0 : F0 ≠ 0)
    (h : IsMultiHomogeneous (fun _ => δ) (C κ * F0 ^ m)) :
    ∃ d0, m * d0 = δ ∧ IsMultiHomogeneous (fun _ => d0) F0 := by
  classical
  have key : ∀ b : Fin B, ∃ k, m * k = δ ∧ ∀ s ∈ F0.support, bw b s = k := by
    intro b
    have h1 := psiB_eq_of_hom b δ _ (fun s hs => h s hs b)
    rw [map_mul, map_pow, show psiB b (C κ) = Polynomial.C (C κ) by
      simp [psiB, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply], map_mul] at h1
    have hCk : (Polynomial.C (C κ) : Polynomial (MvPolynomial (Fin B × Fin n) K)) ≠ 0 := by
      simp [hκ]
    have h2 : psiB b F0 ^ m = Polynomial.C (F0 ^ m) * Polynomial.X ^ δ := by
      apply mul_left_cancel₀ hCk
      rw [h1, map_pow]; ring
    obtain ⟨s0, hs0⟩ : F0.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.2 fun h0 => hF0 (support_eq_empty.1 h0)
    have hP : psiB b F0 ≠ 0 := fun h0 => coeff_psiB_ne_zero b F0 s0 hs0 (by rw [h0]; simp)
    have hFm : F0 ^ m ≠ 0 := pow_ne_zero _ hF0
    have hdeg := congrArg Polynomial.natDegree h2
    have htr := congrArg Polynomial.natTrailingDegree h2
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C_mul_X_pow _ _ hFm] at hdeg
    rw [ntd_pow _ hP, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hFm] at htr
    have heq : (psiB b F0).natDegree = (psiB b F0).natTrailingDegree :=
      Nat.eq_of_mul_eq_mul_left hm (hdeg.trans htr.symm)
    refine ⟨(psiB b F0).natDegree, hdeg, fun s hs => ?_⟩
    have hc := coeff_psiB_ne_zero b F0 s hs
    have h3 := Polynomial.le_natDegree_of_ne_zero hc
    have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
    omega
  obtain ⟨k0, hk0, -⟩ := key ⟨0, hB⟩
  refine ⟨k0, hk0, fun s hs b => ?_⟩
  obtain ⟨k, hk, hks⟩ := key b
  rw [show (∑ j, s (b, j)) = bw b s from rfl, hks s hs]
  exact Nat.eq_of_mul_eq_mul_left hm (hk.trans hk0.symm)

end ReciprocityTheory.ChartRestriction.G.T0.MHF
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DimensionQuotientBound
section
namespace ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound

open IsLocalRing

lemma le_dim_quot {R : Type*} [CommRing R] (p P m : Ideal R) [hp : p.IsPrime] [hP : P.IsPrime]
    [hm : m.IsPrime] (h1 : p < P) (h2 : P < m) : (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  rw [ringKrullDim_quotient]
  let a : PrimeSpectrum.zeroLocus (p : Set R) := ⟨⟨p, hp⟩, fun x hx => hx⟩
  let b : PrimeSpectrum.zeroLocus (p : Set R) := ⟨⟨P, hP⟩, fun x hx => h1.le hx⟩
  let c : PrimeSpectrum.zeroLocus (p : Set R) := ⟨⟨m, hm⟩, fun x hx => (h1.trans h2).le hx⟩
  have hab : a < b := h1
  have hbc : b < c := h2
  have hs : ((2 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (p : Set R)) :=
    Order.LTSeries.length_le_krullDim (((RelSeries.singleton _ a).snoc b
      (by first | exact hab | exact ⟨_, _, rfl, hab⟩ | simpa using hab)).snoc c
      (by first | exact hbc | exact ⟨_, _, rfl, hbc⟩ | (simp only [RelSeries.last_snoc]; exact hbc) | simpa using hbc))
  exact_mod_cast hs

lemma one_le_dim {R : Type*} [CommRing R] (p m : Ideal R) [p.IsPrime] [m.IsPrime] (h : p < m) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
  let a : PrimeSpectrum R := ⟨p, inferInstance⟩
  let b : PrimeSpectrum R := ⟨m, inferInstance⟩
  have hab : a < b := h
  have hs : ((1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum R) :=
    Order.LTSeries.length_le_krullDim ((RelSeries.singleton _ a).snoc b hab)
  exact_mod_cast hs

theorem local_step {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] (M : Ideal B) [hM : M.IsMaximal]
    (w e : B) (hw : w ∈ M) (hw0 : w ≠ 0) (he : e ≠ 0) :
    ∃ q : Ideal B, q.IsPrime ∧ q ≤ M ∧ e ∉ q ∧ w ∉ q ∧
      ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M := by
  classical
  let R := Localization.AtPrime M
  haveI : IsDomain R := IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors M)
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors M)
  have hcm : (IsLocalRing.maximalIdeal R).comap (algebraMap B R) = M :=
    Localization.AtPrime.under_maximalIdeal (I := M)
  have hh : algebraMap B R (e * w) ≠ 0 := by
    intro h
    exact mul_ne_zero he hw0 (hinj (by rw [h, map_zero]))
  have hmax : (⊥ : Ideal R) < IsLocalRing.maximalIdeal R := by
    rw [bot_lt_iff_ne_bot]
    intro h
    have hw' : algebraMap B R w ∈ IsLocalRing.maximalIdeal R := by
      rw [← Ideal.mem_comap, hcm]; exact hw
    rw [h, Ideal.mem_bot] at hw'
    exact hw0 (hinj (by rw [hw', map_zero]))
  have hdim : 1 ≤ ringKrullDim R := one_le_dim ⊥ (IsLocalRing.maximalIdeal R) hmax
  obtain ⟨p, hp, hpd, hpn⟩ := ReciprocityTheory.ChartRestriction.G.T0.av_prime_dim_one hdim _ hh
  haveI := hp
  refine ⟨p.comap (algebraMap B R), Ideal.comap_isPrime _ _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hcm]
    exact IsLocalRing.le_maximalIdeal hp.ne_top hx
  · intro he'
    apply hpn
    rw [map_mul]
    exact p.mul_mem_right _ he'
  · intro hw'
    apply hpn
    rw [map_mul]
    exact p.mul_mem_left _ hw'
  · intro P hP hqP hPM hwP
    by_contra hne
    have hdisj : Disjoint (M.primeCompl : Set B) P := by
      rw [Set.disjoint_left]
      intro x hx hxP
      exact hx (hPM hxP)
    haveI hP' : (P.map (algebraMap B R)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M.primeCompl R P hP hdisj
    have hcomap : (P.map (algebraMap B R)).comap (algebraMap B R) = P :=
      IsLocalization.under_map_of_isPrime_disjoint M.primeCompl R hP hdisj
    have h1 : p < P.map (algebraMap B R) := by
      refine lt_of_le_of_ne ?_ ?_
      · have hpe : (p.comap (algebraMap B R)).map (algebraMap B R) = p :=
          IsLocalization.map_under M.primeCompl R p
        rw [← hpe]
        exact Ideal.map_mono hqP
      · intro heq
        apply hpn
        rw [heq, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hwP)
    have h2 : P.map (algebraMap B R) < IsLocalRing.maximalIdeal R := by
      refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP'.ne_top) ?_
      intro heq
      apply hne
      rw [← hcomap, heq, hcm]
    have h3 := le_dim_quot p (P.map (algebraMap B R)) (IsLocalRing.maximalIdeal R) h1 h2
    rw [hpd] at h3
    exact absurd h3 (by decide)

end ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormA
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HNm

theorem wt_add_eq_zero {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  cases a with
  | top => simp at h
  | coe x =>
    cases b with
    | top => simp at h
    | coe y =>
      have h' : x + y = 0 := by exact_mod_cast h
      have hx : 0 ≤ x := by exact_mod_cast ha
      have hy : 0 ≤ y := by exact_mod_cast hb
      exact_mod_cast (show x = 0 by omega)

theorem nonneg_of_isIntegral {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (w : AddValuation L (WithTop ℤ)) (h0 : ∀ r : R, 0 ≤ w (algebraMap R L r)) {x : L}
    (hx : IsIntegral R x) : 0 ≤ w x := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hneg)
  have hm0 : m < 0 := by rw [← hm] at hneg; exact_mod_cast hneg
  obtain ⟨p, hpm, hp⟩ := hx
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hp
  have hsum := eq_neg_of_add_eq_zero_left hp
  have hlow : ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤
      w (∑ i ∈ Finset.range p.natDegree, algebraMap R L (p.coeff i) * x ^ i) := by
    apply w.map_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rw [w.map_mul, w.map_pow, ← hm]
    have ha := h0 (p.coeff i)
    have hle : ((p.natDegree : ℤ) - 1) * m ≤ (i : ℤ) * m :=
      mul_le_mul_of_nonpos_right (by omega) hm0.le
    calc ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤ (((i : ℤ) * m : ℤ) : WithTop ℤ) := by
          exact_mod_cast hle
      _ = i • (m : WithTop ℤ) := by rw [← WithTop.coe_nsmul, nsmul_eq_mul]
      _ ≤ w (algebraMap R L (p.coeff i)) + i • (m : WithTop ℤ) := le_add_of_nonneg_left ha
  have hxn : w (x ^ p.natDegree) = (((p.natDegree : ℤ) * m : ℤ) : WithTop ℤ) := by
    rw [w.map_pow, ← hm, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have key : ((((p.natDegree : ℤ) - 1) * m : ℤ) : WithTop ℤ) ≤
      (((p.natDegree : ℤ) * m : ℤ) : WithTop ℤ) := by
    rw [← hxn, hsum, w.map_neg]; exact hlow
  have key' := WithTop.coe_le_coe.mp key
  nlinarith

end HNm

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HadamardGram
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix

theorem hadamard_gram {R : Type*} [Fintype R] [DecidableEq R] {n : ℕ} (hR : Fintype.card R = n)
    (M : R → Fin n → ℂ) (ν : R → ℝ) (s : Fin n → ℝ) (hν : ∀ r, 0 < ν r)
    (hM : ∀ r k, ‖M r k‖ * ν r ≤ s k) :
    ‖(Matrix.of fun k l : Fin n => ∑ r, M r k * M r l).det‖ * ∏ r, ν r ^ 2 ≤
      (n : ℝ) ^ n * ∏ k, s k ^ 2 := by
  classical

  let e : R ≃ Fin n := Fintype.equivFinOfCardEq hR
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => M (e.symm i) k
  let N : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => (ν (e.symm i) : ℂ) * M (e.symm i) k
  have hG : (Matrix.of fun k l : Fin n => ∑ r, M r k * M r l) = Aᵀ * A := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, A]
    exact (Equiv.sum_comp e.symm (fun r => M r k * M r l)).symm
  have hNd : N = Matrix.diagonal (fun i => (ν (e.symm i) : ℂ)) * A := by
    ext i k
    simp [N, A, Matrix.diagonal_mul]
  have hprod : ∏ i, ν (e.symm i) = ∏ r, ν r := Equiv.prod_comp e.symm ν
  have hνpos : 0 ≤ ∏ r, ν r := Finset.prod_nonneg fun r _ => (hν r).le
  have hdetN : ‖N.det‖ = (∏ r, ν r) * ‖A.det‖ := by
    rw [hNd, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_prod, ← hprod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hν _)]
  have hleft : ‖(Matrix.of fun k l : Fin n => ∑ r, M r k * M r l).det‖ * ∏ r, ν r ^ 2
      = ‖N.det‖ ^ 2 := by
    rw [hG, Matrix.det_mul, Matrix.det_transpose, norm_mul, hdetN, Finset.prod_pow]
    ring
  rw [hleft]

  have hH : ‖N.det‖ ≤ ∏ k, Real.sqrt (∑ i, ‖N i k‖ ^ 2) := by
    have := hadamard_det_le Nᵀ
    simpa [Matrix.det_transpose, Matrix.transpose_apply] using this
  have hcol : ∀ k, ∑ i, ‖N i k‖ ^ 2 ≤ (n : ℝ) * s k ^ 2 := by
    intro k
    have : ∀ i, ‖N i k‖ ^ 2 ≤ s k ^ 2 := by
      intro i
      have h1 : ‖N i k‖ = ‖M (e.symm i) k‖ * ν (e.symm i) := by
        simp only [N, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hν _)]
        ring
      rw [h1]
      exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (hν _).le) (hM _ _) 2
    calc ∑ i, ‖N i k‖ ^ 2 ≤ ∑ _i : Fin n, s k ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = (n : ℝ) * s k ^ 2 := by simp
  calc ‖N.det‖ ^ 2 ≤ (∏ k, Real.sqrt (∑ i, ‖N i k‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hH 2
    _ = ∏ k, ∑ i, ‖N i k‖ ^ 2 := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun k _ =>
          Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
    _ ≤ ∏ k, ((n : ℝ) * s k ^ 2) :=
        Finset.prod_le_prod₀ (fun k _ => Finset.sum_nonneg fun i _ => by positivity)
          fun k _ => hcol k
    _ = (n : ℝ) ^ n * ∏ k, s k ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end ReciprocityTheory.ChartRestriction.G.T0
end

