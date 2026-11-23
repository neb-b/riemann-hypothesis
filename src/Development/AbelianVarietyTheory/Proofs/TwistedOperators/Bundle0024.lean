module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
section
noncomputable section

open Polynomial TensorProduct Matrix Formalism.UG

namespace GlobalTheory.ClassParam

section Cyclic

theorem charpoly_dvd_of_aeval {K : Type} [Field K] {r : ℕ} (g : Matrix (Fin r) (Fin r) K)
    (hs : g.charpoly.Separable) (q : K[X]) (hq : aeval g q = 0) : g.charpoly ∣ q := by
  classical
  by_cases h0 : q = 0
  · simp [h0]
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  rw [← Polynomial.map_dvd_map' f]
  have hq0 : q.map f ≠ 0 := Polynomial.map_ne_zero h0
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots (Polynomial.map_ne_zero g.charpoly_monic.ne_zero) ?_
  rw [Multiset.le_iff_subset (nodup_roots hs.map)]
  intro μ hμ
  rw [mem_roots hq0]
  have h1 : μ ∈ spectrum Ω (g.map f) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
    exact isRoot_of_mem_roots hμ
  have h2 := spectrum.subset_polynomial_aeval (g.map f) (q.map f) ⟨μ, h1, rfl⟩
  have h3 : aeval (g.map f) (q.map f) = 0 := by
    rw [aeval_map_algebraMap]
    have := congrArg (AlgHom.mapMatrix (m := Fin r) (Algebra.ofId K Ω)) hq
    rw [← aeval_algHom_apply, map_zero] at this
    exact this
  rw [h3] at h2
  by_contra hne
  exact (spectrum.mem_iff.1 h2) (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin r) (Fin r) Ω)))

def krylov {A : Type} [CommRing A] {r : ℕ} (g : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    Matrix (Fin r) (Fin r) A := Matrix.of fun i j => ((g ^ (j : ℕ)) *ᵥ v) i

theorem krylov_map {A B : Type} [CommRing A] [CommRing B] {r : ℕ} (f : A →+* B)
    (g : Matrix (Fin r) (Fin r) A) (v : Fin r → A) :
    (krylov g v).map f = krylov (g.map f) (f ∘ v) := by
  ext i j
  simp only [krylov, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, Matrix.map_pow]

theorem exists_cyclic_field {K : Type} [Field K] {r : ℕ} (g : Matrix (Fin r) (Fin r) K)
    (hs : g.charpoly.Separable) : ∃ v, (krylov g v).det ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval' (Matrix.toLin' g))
  refine ⟨(Module.AEval'.of (Matrix.toLin' g)).symm x, fun h => ?_⟩
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  set v := (Module.AEval'.of (Matrix.toLin' g)).symm x with hv
  let q : K[X] := ∑ j : Fin r, monomial (j : ℕ) (w j)
  have ha : ∀ p : K[X], aeval (Matrix.toLin' g) p = Matrix.toLin' (aeval g p) := fun p =>
    (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := Fin r)) g p)
  have hqv : aeval g q *ᵥ v = 0 := by
    rw [← hw]
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [q, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hmem : q ∈ Module.annihilator K[X] (Module.AEval' (Matrix.toLin' g)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    apply (Module.AEval'.of (Matrix.toLin' g)).symm.injective
    rw [Module.AEval.of_symm_smul, map_zero, ha]
    exact hqv
  have hq : aeval g q = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero, ← ha]
    refine LinearMap.ext fun u => ?_
    have := Module.mem_annihilator.1 hmem (Module.AEval'.of (Matrix.toLin' g) u)
    have h2 := congrArg (Module.AEval'.of (Matrix.toLin' g)).symm this
    rw [Module.AEval.of_symm_smul, map_zero] at h2
    simpa using h2
  have hd := charpoly_dvd_of_aeval g hs q hq
  have hdeg : q.degree < g.charpoly.degree := by
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => lt_of_le_of_lt (degree_monomial_le _ _) ?_
    exact_mod_cast j.2
  have hq0 := eq_zero_of_dvd_of_degree_lt hd hdeg
  apply hw0
  ext j
  have := congrArg (fun p => p.coeff j) hq0
  simpa only [q, Polynomial.finsetSum_coeff, coeff_monomial_apply, Fin.val_inj,
    Fintype.sum_ite_eq', coeff_zero, Pi.zero_apply] using this

theorem exists_cyclic {A : Type} [CommRing A] [IsArtinianRing A] {r : ℕ}
    (g : Matrix (Fin r) (Fin r) A) (hs : g.charpoly.Separable) :
    ∃ v, IsUnit (krylov g v).det := by
  classical
  have hloc : ∀ m : MaximalSpectrum A, ∃ v : Fin r → A ⧸ m.asIdeal,
      (krylov (g.map (Ideal.Quotient.mk m.asIdeal)) v).det ≠ 0 := by
    intro m
    have := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact exists_cyclic_field _ (by rw [Matrix.charpoly_map]; exact hs.map)
  choose w hw using hloc
  have hsurj : ∀ i : Fin r, ∃ a : A, ∀ m : MaximalSpectrum A,
      Ideal.Quotient.mk m.asIdeal a = w m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum A => m.asIdeal)
      (fun m m' h => MaximalSpectrum.isCoprime_of_ne h) (fun m => w m i)
    exact ⟨a, ha⟩
  choose v hv using hsurj
  refine ⟨v, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hw ⟨m, hm⟩
  have : w ⟨m, hm⟩ = Ideal.Quotient.mk m ∘ v := funext fun i => (hv i ⟨m, hm⟩).symm
  rw [this, ← krylov_map]
  rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det] at hmem
  exact hmem

end Cyclic

section Transfer

variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S]
  [Algebra A B] {ι : Type} [Fintype ι] [DecidableEq ι]

end Transfer

section Forms

variable {A : Type} [CommRing A] {r : ℕ} (σ : A →+* A)

theorem hform_eq (J : Matrix (Fin r) (Fin r) A) (x y : Fin r → A) :
    hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (J g : Matrix (Fin r) (Fin r) A) (x y : Fin r → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ (cT σ g * J * g) x y := by
  have h2 : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  rw [hform_eq, hform_eq, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cT,
    Matrix.dotProduct_mulVec _ (g.map σ)ᵀ, Matrix.vecMul_transpose]

theorem hform_single (J : Matrix (Fin r) (Fin r) A) (i j : Fin r) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite σ]

theorem mem_UJ_iff (J : Matrix (Fin r) (Fin r) A) (g : GL (Fin r) A) :
    g ∈ UJ σ J ↔ ∀ x y, hform σ J ((g : Matrix (Fin r) (Fin r) A) *ᵥ x)
      ((g : Matrix (Fin r) (Fin r) A) *ᵥ y) = hform σ J x y := by
  show cT σ (g : Matrix (Fin r) (Fin r) A) * J * g = J ↔ _
  constructor
  · intro h x y; rw [hform_mulVec, h]
  · intro h; ext i j
    rw [← hform_single σ (_ * J * _), ← hform_mulVec, h, hform_single]

end Forms

section Core

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}

variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}

end Core

section Concrete

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion

attribute [local instance] algLk

variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]

end Concrete

end GlobalTheory.ClassParam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem weight_fst_eq_mapDomain {ι κ : Type} (k : ι × κ →₀ ℕ) :
    Finsupp.weight (fun p : ι × κ => (Finsupp.single p.1 1 : ι →₀ ℕ)) k = Finsupp.mapDomain Prod.fst k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain]
  refine Finsupp.sum_congr fun p _ => ?_
  simp

theorem substF_X_isWeightedHomogeneous {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (X p)) (Finsupp.single p.1 1) := by
  rw [substF_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun k _ => IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
  have h1 := isWeightedHomogeneous_X ℂ (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ)) (p.1, k, l)
  have h2 := (isWeightedHomogeneous_C (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
    (h p.1 k p.2.1 * g p.1 l p.2.2)).mul h1
  rwa [zero_add] at h2

theorem mapDomain_fst_eq_of_coeff_substF_ne_zero {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ)
    (hk : AddMonoidAlgebra.coeff (substF h g (MvPolynomial.monomial k 1)) k' ≠ 0) :
    Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  have key : IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (MvPolynomial.monomial k 1)) (Finsupp.mapDomain Prod.fst k) := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, ← weight_fst_eq_mapDomain, Finsupp.weight_apply,
      Finsupp.sum]
    refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
    rw [map_pow]
    exact (substF_X_isWeightedHomogeneous h g p).pow (k p)
  rw [← weight_fst_eq_mapDomain]
  exact key hk

end GlobalTheory.CompactHowe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMul
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    substF h g (substF h' g' P) = substF (h * h') (g * g') P := by
  have key : (substF h g).comp (substF h' g') = substF (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, substF_X, substF_X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, substF_X, algHom_C, algebraMap_eq, Pi.mul_apply, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key

end GlobalTheory.CompactHowe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionScalarMonomial
section
noncomputable section
open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_scalar_X {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (p : ι × Fin N × Fin n) :
    substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (X p)
      = C (if p.1 = τ₀ then ζ else 1) * X p := by
  rw [substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
  · obtain ⟨a, b⟩ := p
    by_cases h : a = τ₀
    · subst h; simp
    · simp [h]
  · intro l _ hl
    by_cases h : p.1 = τ₀ <;> simp [h, Matrix.one_apply_ne hl]
  · simp
  · intro k _ hk
    simp [Matrix.one_apply_ne hk]
  · simp

theorem mapDomain_fst_apply {ι : Type} [DecidableEq ι] {N n : ℕ} (k : ι × Fin N × Fin n →₀ ℕ) (τ₀ : ι) :
    Finsupp.mapDomain Prod.fst k τ₀ = ∑ p ∈ k.support, if p.1 = τ₀ then k p else 0 := by
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  rw [Finsupp.single_apply]

theorem substF_scalar_monomial {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, substF_scalar_X, mul_pow, Finset.prod_mul_distrib]
  rw [mapDomain_fst_apply, smul_eq_C_mul, ← Finset.prod_pow_eq_pow_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← map_pow]
  split_ifs <;> simp

end GlobalTheory.CompactHowe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MetaplecticOneParameterSchwartzIntertwining
section
noncomputable section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory.RealWeil

theorem integral_norm_sq_eq_norm_toLp_sq {l : Type} [Fintype l] (g : Sch l) :
    ∫ x, ‖g x‖ ^ 2 = ‖g.toLp 2 volume‖ ^ 2 := by
  rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
  have h2 : (2 : ENNReal).toReal = 2 := by simp
  simp only [h2]
  have hn : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num

theorem metaplectic_oneParam_schwartz : GlobalTheory.Published.RealMetaplecticRepresentation →
    ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ),
      X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧
        (∀ f, U 0 f = f) ∧
        (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧
        (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  intro hMp l _ _ _ X hX
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, h5, h6⟩ := hMp l
  obtain ⟨γ, -, h0, hadd, hpr, hd⟩ := h6 X hX
  refine ⟨fun t => (omS (γ t)).toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f
    simp only [ContinuousLinearMap.coe_coe, hadd, map_mul, ContinuousLinearMap.mul_apply]
  · intro f
    simp [h0]
  · intro t w f f₁ h
    simp only [ContinuousLinearMap.coe_coe]
    rw [← hpr t]
    have hL : f₁.toLp 2 = rho w (f.toLp 2) := by
      refine Lp.ext ((SchwartzMap.coeFn_toLp f₁ 2 volume).trans ?_)
      refine Filter.EventuallyEq.symm ((coeFn_rho w _).trans ?_)
      rw [h]
      exact rhoFun_congr w (SchwartzMap.coeFn_toLp f 2 volume)
    have key : (omS (γ t) f₁).toLp 2 =
        rho ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ((omS (γ t) f).toLp 2) := by
      rw [← h4, hL, h3, h4]
    have hae : ⇑(omS (γ t) f₁) =ᵐ[volume]
        rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f) := by
      refine (SchwartzMap.coeFn_toLp (omS (γ t) f₁) 2 volume).symm.trans ?_
      rw [key]
      refine (coeFn_rho _ _).trans ?_
      exact rhoFun_congr _ (SchwartzMap.coeFn_toLp (omS (γ t) f) 2 volume)
    have hc : Continuous (rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f)) :=
      (continuous_phase _).mul ((omS (γ t) f).continuous.comp (continuous_id.add continuous_const))
    exact (Continuous.ae_eq_iff_eq volume (omS (γ t) f₁).continuous hc).1 hae
  · intro t f
    simp only [ContinuousLinearMap.coe_coe]
    rw [integral_norm_sq_eq_norm_toLp_sq, integral_norm_sq_eq_norm_toLp_sq, ← h4, LinearIsometryEquiv.norm_map]
  · intro f y
    let lam : Sch l →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
    have hlam : ∀ g : Sch l, lam g = g y := fun g => rfl
    have := (metaplectic_schwartz_smooth h3 h4 h5).2.2 lam X hX γ h0 hpr hd f
    simpa only [hlam, ContinuousLinearMap.coe_coe] using this

end GlobalTheory.RealWeil

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearZeroOfKillsTranslatesTensor
section
open scoped InnerProductSpace

namespace GlobalTheory.DensityMultiPlace

theorem multilinear_translates_zero : ∀ (ι : Type) [Fintype ι] (H : ι → Type) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)] (G : ι → Type) [∀ i, Group (G i)] (π : ∀ i, G i →* (H i →L[ℂ] H i)), (∀ i g x, ‖π i g x‖ = ‖x‖) → (∀ i, ∀ B : H i →L[ℂ] H i, (∀ g, B.comp (π i g) = (π i g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ (H i)) → ∀ (Sm : ∀ i, Submodule ℂ (H i)), (∀ i, Dense (Sm i : Set (H i))) → ∀ (hinv : ∀ i g, ∀ x ∈ Sm i, π i g x ∈ Sm i) (L : (∀ i, Sm i) →ₘₗ[ℂ] ℂ) (C : ℝ), (∀ v, ‖L v‖ ≤ C * ∏ i, ‖(v i : H i)‖) → ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → ∀ i, Sm i), (∀ g : ∀ i, G i, ∑ j, c j * L (fun i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩) = 0) → ∀ (φ : ∀ i, H i) (u : ∀ i, Sm i), (∑ j, c j * ∏ i, ⟪φ i, (v j i : H i)⟫_ℂ) * L u = 0 := by
  intro ι _ H _ _ _ G _ π hu hs Sm hd hinv L C hL n c v hv φ u
  classical
  let w : Fin n → (∀ i, G i) → ∀ i, Sm i :=
    fun j g i => ⟨π i (g i) (v j i), hinv i (g i) _ (v j i).2⟩
  have key : ∀ s : Finset ι, ∀ (g : ∀ i, G i) (u : ∀ i, Sm i),
      ∑ j, c j * (∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) * L (s.piecewise u (w j g)) = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro g u
      simpa [w] using hv g
    · intro a s ha ih g u
      have hnorm : ∀ (m : ∀ i, Sm i) (x : Sm a),
          ∏ i, ‖((Function.update m a x) i : H i)‖
            = (∏ i ∈ Finset.univ.erase a, ‖(m i : H i)‖) * ‖x‖ := by
        intro m x
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), Function.update_self,
          mul_comm]
        congr 1
        · refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have hbd : ∀ j (x : Sm a), ‖L.toLinearMap (s.piecewise u (w j g)) a x‖
          ≤ (C * ∏ i ∈ Finset.univ.erase a, ‖((s.piecewise u (w j g)) i : H i)‖) * ‖x‖ := by
        intro j x
        rw [MultilinearMap.toLinearMap_apply, mul_assoc, ← hnorm]
        exact hL _
      have hden : DenseRange (Sm a).subtypeL := (hd a).denseRange_val
      have hui : IsUniformInducing (Sm a).subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
      let Λ : Fin n → (H a →L[ℂ] ℂ) := fun j =>
        (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) •
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)).extend (Sm a).subtypeL
      have hΛ : ∀ j (x : Sm a), Λ j (x : H a) = (c j * ∏ i ∈ s, ⟪φ i, (v j i : H i)⟫_ℂ) *
          L (Function.update (s.piecewise u (w j g)) a x) := by
        intro j x
        have := ContinuousLinearMap.extend_eq
          ((L.toLinearMap (s.piecewise u (w j g)) a).mkContinuous _ (hbd j)) hden hui x
        simp only [Λ, smul_apply, smul_eq_mul]
        erw [this]
        rw [LinearMap.mkContinuous_apply, MultilinearMap.toLinearMap_apply]
      have hupd : ∀ j (k : G a), s.piecewise u (w j (Function.update g a k))
          = Function.update (s.piecewise u (w j g)) a ⟨π a k (v j a), hinv a k _ (v j a).2⟩ := by
        intro j k
        funext i
        by_cases hia : i = a
        · subst hia
          simp [Finset.piecewise_eq_of_notMem _ _ _ ha, w]
        · rw [Function.update_of_ne hia]
          by_cases his : i ∈ s
          · simp [Finset.piecewise_eq_of_mem _ _ _ his]
          · simp [Finset.piecewise_eq_of_notMem _ _ _ his, w, Function.update_of_ne hia]
      have hG : ∀ k : G a, ∑ j, Λ j (π a k (v j a)) = 0 := by
        intro k
        have h1 := ih (Function.update g a k) u
        rw [← h1]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show (π a k (v j a) : H a) = ((⟨π a k (v j a), hinv a k _ (v j a).2⟩ : Sm a) : H a) from rfl,
          hΛ, hupd, mul_assoc]
      have h2 := GlobalTheory.T.irreducibleUnitary_vector_density (H a) (G a) (π a) (hu a) (hs a) n (fun j => (v j a : H a)) Λ hG
        (φ a) (u a)
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hΛ, Finset.prod_insert ha, Finset.piecewise_insert]
      ring
  have h := key Finset.univ (fun _ => 1) u
  simp only [Finset.piecewise_univ] at h
  rw [Finset.sum_mul]
  rw [← h]

end GlobalTheory.DensityMultiPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpanStatement
section
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorStable_piTensorPureKernelSpan : ∀ {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i)),
    (∀ i, GlobalTheory.TensHead.Stab (Op i) (K i)) →
    GlobalTheory.TensHead.Stab (GlobalTheory.TensHead.piOps Op) (GlobalTheory.TensHead.piKer K) := by
  first | exact @GlobalTheory.TensHead.stab_piOps_piKer | exact GlobalTheory.TensHead.stab_piOps_piKer | (intros; apply GlobalTheory.TensHead.stab_piOps_piKer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulInvariantMeasureShearedProductPairGroupStatement
section
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N), κ.IsHaarMeasure → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → SMulInvariantMeasure (GlobalTheory.UnfoldNormal.pairGroup Γ N hN) (H × H) ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)) := by
  first | exact @GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map | exact GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map | (intros; apply GlobalTheory.UnfoldNormal.smulInvariantMeasure_shear_map <;> assumption)
end

