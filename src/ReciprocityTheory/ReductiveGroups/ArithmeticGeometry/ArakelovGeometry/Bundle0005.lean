module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Jacobson.Ring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStA
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem aeval_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    aeval x (map (Int.castRingHom ℚ) f) = aeval x f := by
  rw [aeval_def, eval₂_map, aeval_def]
  congr 1 <;> exact RingHom.ext_int _ _

theorem eval_smul_of_homog {R : Type*} [CommRing R] {φ : MvPolynomial J R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : J → R) : eval (c • z) φ = c ^ d * eval z φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd : ∑ i ∈ s.support, s i = d := by
    have := hφ (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem secFun_smul {b : MvPolynomial J ℚ} {n : ℕ}
    (hb : ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : J → ℂ) : secFun b (c • z) = c ^ n * secFun b z := by
  obtain ⟨f, hf, rfl⟩ := hb
  have hmap : map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℂ) f := by
    rw [map_map]
    congr 1 <;> exact RingHom.ext_int _ _
  simp only [secFun, hmap]
  exact eval_smul_of_homog (hf.map _) c z

theorem continuous_secFun (b : MvPolynomial J ℚ) : Continuous (secFun b) := by
  unfold secFun
  exact MvPolynomial.continuous_eval _

theorem secFun_map_int (f : MvPolynomial J ℤ) (z : J → ℂ) :
    secFun (map (Int.castRingHom ℚ) f) z = eval z (map (Int.castRingHom ℂ) f) := by
  unfold secFun
  rw [map_map]
  congr 2 <;> exact RingHom.ext_int _ _

theorem secFun_eq_zero_of_pts {x : J → Ω} {n : ℕ} {d : MvPolynomial J ℤ} (hd : d.IsHomogeneous n)
    (h0 : aeval x d = 0) {z : J → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    secFun (map (Int.castRingHom ℚ) d) z = 0 := by
  have hmem : d ∈ coordIdeal ℤ x := by
    unfold coordIdeal coneMap
    rw [RingHom.mem_ker, aeval_def, ← eval_map]
    have hpt : (fun i => Polynomial.C (x i) * Polynomial.X) =
        (Polynomial.X : Polynomial Ω) • fun i => Polynomial.C (x i) := by
      funext i
      exact mul_comm _ _
    have hC : eval (fun i => Polynomial.C (x i)) (map (algebraMap ℤ (Polynomial Ω)) d) =
        Polynomial.C (aeval x d) := by
      rw [eval_map, aeval_def, hom_eval₂]
      congr 1 <;> exact RingHom.ext_int _ _
    rw [hpt, eval_smul_of_homog (hd.map _), hC, h0, map_zero, mul_zero]
  rw [secFun_map_int]
  exact hz.2 d hmem

theorem secFun_conjPt (b : MvPolynomial J ℚ) (z : J → ℂ) :
    secFun b (conjPt z) = starRingEnd ℂ (secFun b z) := by
  simp only [secFun, eval_map, hom_eval₂]
  rw [RingHom.ext_rat ((starRingEnd ℂ).comp (algebraMap ℚ ℂ)) (algebraMap ℚ ℂ)]
  rfl

theorem continuous_conjPt : Continuous (conjPt : (J → ℂ) → J → ℂ) := by
  exact continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)

def conjEquiv (J : Type) [Fintype J] : (J → ℂ) ≃ᵐ (J → ℂ) where
  toFun := conjPt
  invFun := conjPt
  left_inv z := by funext i; simp [conjPt]
  right_inv z := by funext i; simp [conjPt]
  measurable_toFun := continuous_conjPt.measurable
  measurable_invFun := continuous_conjPt.measurable

theorem wgt_conjPt {m : ConeMetric (C := ℂ) (ι := J)} (hm : IsConjInvariant m) (n : ℕ) (z : J → ℂ) :
    wgt m n (conjPt z) = wgt m n z := by
  unfold wgt conjPt
  rw [hm z]

theorem conj_bGram {m : ConeMetric (C := ℂ) (ι := J)} {μ : Measure (J → ℂ)} (hm : IsConjInvariant m)
    (hμ : μ.map conjPt = μ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial J ℚ) (i j : Fin r) :
    starRingEnd ℂ (bGram μ (fun k => secFun (b k)) (wgt m n) i j) =
      bGram μ (fun k => secFun (b k)) (wgt m n) i j := by
  have hμ' : μ.map (conjEquiv J) = μ := hμ
  have he : ∀ x, conjEquiv J x = conjPt x := fun x => rfl
  simp only [bGram, Matrix.of_apply]
  rw [← integral_conj]
  conv_rhs => rw [← hμ']
  rw [integral_map_equiv (conjEquiv J)]
  congr 1
  funext x
  simp [he, secFun_conjPt, wgt_conjPt hm]
  try ring

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct

theorem isReduced_tensor_finite (Ω E : Type*) [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : IsReduced (E ⊗[ℚ] Ω) := by
  haveI : Algebra.FormallyUnramified ℚ E := Algebra.FormallyUnramified.of_isSeparable ℚ E
  haveI : IsReduced (Ω ⊗[ℚ] E) := Algebra.FormallyUnramified.isReduced_of_field Ω (Ω ⊗[ℚ] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm ℚ E Ω).toRingHom
    (Algebra.TensorProduct.comm ℚ E Ω).injective

theorem eq_zero_of_sum_tmul {Ω E : Type*} [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E] {r : ℕ}
    {s : Fin r → Ω} (hs : LinearIndependent ℚ s) {e : Fin r → E}
    (h : ∑ k, e k ⊗ₜ[ℚ] s k = 0) : e = 0 := by
  classical
  let W := Submodule.span ℚ (Set.range s)
  let 𝒞 : Module.Basis (Fin r) ℚ W := Module.Basis.span hs
  have hinj : Function.Injective (LinearMap.lTensor E W.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective
  have h0 : (∑ k, e k ⊗ₜ[ℚ] 𝒞 k : E ⊗[ℚ] W) = 0 := by
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero]
    have hc : ∀ k, ((𝒞 k : W) : Ω) = s k := fun k => by
      show ((Module.Basis.span hs k : W) : Ω) = s k
      rw [Module.Basis.span_apply]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, hc]
    exact h
  have hb := TensorProduct.sum_tmul_basis_right_eq_zero 𝒞 (Finsupp.equivFunOnFinite.symm e) (by
    rw [Finsupp.sum_fintype _ _ (by intros; simp)]
    simpa using h0)
  funext k
  have hk := congrArg (fun b => b k) hb
  simpa using hk

theorem nilp_coeff_eq_zero {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ} {s : Fin r → Ω}
    (hs : LinearIndependent ℚ s) {c : Fin r → ℂ}
    (h : IsNilpotent (∑ k, c k ⊗ₜ[ℚ] s k : ℂ ⊗[ℚ] Ω)) : c = 0 := by
  classical
  let A : Subalgebra ℚ ℂ := Algebra.adjoin ℚ ((Finset.univ.image c : Finset ℂ) : Set ℂ)
  haveI : Algebra.FiniteType ℚ A := (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_adjoin_finset _)
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ) (B := A)
  have hcA : ∀ k, c k ∈ A := fun k => Algebra.subset_adjoin (by simp)
  let cA : Fin r → A := fun k => ⟨c k, hcA k⟩
  let tA : A ⊗[ℚ] Ω := ∑ k, cA k ⊗ₜ[ℚ] s k
  let ι : A ⊗[ℚ] Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω := Algebra.TensorProduct.map A.val (AlgHom.id ℚ Ω)
  have hι : Function.Injective ι := by
    have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω) (A.val.toLinearMap)
      Subtype.val_injective
    have heq : ∀ x, ι x = LinearMap.rTensor Ω A.val.toLinearMap x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [ι, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    intro x y hxy
    apply hinj
    rw [← heq, ← heq, hxy]
  have hιt : ι tA = ∑ k, c k ⊗ₜ[ℚ] s k := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [tA, ι, map_sum, Algebra.TensorProduct.map_tmul, cA]
  have hnA : IsNilpotent tA := by
    obtain ⟨m, hm⟩ := h
    refine ⟨m, hι ?_⟩
    rw [map_pow, hιt, hm, map_zero]
  have key : ∀ (E : Type) [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E] (φ : A →ₐ[ℚ] E),
      ∀ k, φ (cA k) = 0 := by
    intro E _ _ _ φ
    let π : A ⊗[ℚ] Ω →ₐ[ℚ] E ⊗[ℚ] Ω := Algebra.TensorProduct.map φ (AlgHom.id ℚ Ω)
    haveI : IsReduced (E ⊗[ℚ] Ω) := isReduced_tensor_finite Ω E
    have h0 : π tA = 0 := (hnA.map π).eq_zero
    have h1 : ∑ k, φ (cA k) ⊗ₜ[ℚ] s k = 0 := by
      rw [← h0]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [tA, π, map_sum, Algebra.TensorProduct.map_tmul]
    exact congrFun (eq_zero_of_sum_tmul hs h1)
  have hmax : ∀ M : Ideal A, M.IsMaximal → ∀ k, cA k ∈ M := by
    intro M hM k
    letI hF : Field (A ⧸ M) := Ideal.Quotient.field M
    haveI : Algebra.FiniteType ℚ (A ⧸ M) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ M) Ideal.Quotient.mk_surjective
    haveI : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
    exact Ideal.Quotient.eq_zero_iff_mem.1 (key (A ⧸ M) (Ideal.Quotient.mkₐ ℚ M) k)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance Ideal.isPrime_bot.isRadical
  funext k
  have hk : cA k ∈ (⊥ : Ideal A).jacobson := Ideal.mem_sInf.2 (fun J hJ => hmax J hJ.2 k)
  rw [hjac] at hk
  have h0 : cA k = 0 := (Submodule.mem_bot _).1 hk
  exact congrArg Subtype.val h0

section Poly

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem aeval_eq_zero_of_mem_coordIdeal {x : J → Ω} {f : MvPolynomial J ℤ}
    (hf : f ∈ coordIdeal ℤ x) : aeval x f = 0 := by
  have h0 : (aeval fun i => Polynomial.C (x i) * Polynomial.X : MvPolynomial J ℤ →ₐ[ℤ] Polynomial Ω) f = 0 :=
    RingHom.mem_ker.1 hf
  have h1 := MvPolynomial.comp_aeval_apply (fun i => Polynomial.C (x i) * Polynomial.X)
    ((Polynomial.aeval (1 : Ω)).restrictScalars ℤ) f
  rw [h0, map_zero] at h1
  simpa using h1.symm

def evalT (x : J → Ω) : MvPolynomial J ℂ →ₐ[ℂ] ℂ ⊗[ℚ] Ω :=
  aeval fun j => (1 : ℂ) ⊗ₜ[ℚ] x j

theorem evalT_map_rat (x : J → Ω) (b : MvPolynomial J ℚ) :
    evalT x (map (algebraMap ℚ ℂ) b) = (1 : ℂ) ⊗ₜ[ℚ] aeval x b := by
  unfold evalT
  rw [MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x (Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω) b
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm

theorem evalT_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    evalT x (map (Int.castRingHom ℂ) f) = (1 : ℂ) ⊗ₜ[ℚ] aeval x f := by
  unfold evalT
  rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  have h := MvPolynomial.comp_aeval_apply x
    ((Algebra.TensorProduct.includeRight : Ω →ₐ[ℚ] ℂ ⊗[ℚ] Ω).restrictScalars ℤ) f
  simpa [Algebra.TensorProduct.includeRight_apply] using h.symm

theorem coeff_eq_zero_of_vanish {x : J → Ω} {r : ℕ} {b : Fin r → MvPolynomial J ℚ}
    (hs : LinearIndependent ℚ fun k => aeval x (b k)) {c : Fin r → ℂ}
    (h : ∀ z : J → ℂ, (∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0) →
      ∑ k, c k * secFun (b k) z = 0) : c = 0 := by
  classical
  set I : Ideal (MvPolynomial J ℂ) := Ideal.map (MvPolynomial.map (Int.castRingHom ℂ)) (coordIdeal ℤ x) with hI
  set P : MvPolynomial J ℂ := ∑ k, MvPolynomial.C (c k) * MvPolynomial.map (algebraMap ℚ ℂ) (b k) with hP
  have hPmem : P ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    rw [MvPolynomial.mem_zeroLocus_iff] at hz
    have hz' : ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0 := by
      intro f hf
      have hf' := hz _ (Ideal.mem_map_of_mem _ hf)
      exact hf'
    have hsum := h z hz'
    change eval z P = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum]
    simpa [secFun] using hsum
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hPmem
  obtain ⟨n, hn⟩ := hPmem
  have hker : I ≤ RingHom.ker (evalT x : MvPolynomial J ℂ →+* ℂ ⊗[ℚ] Ω) := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change evalT x (map (Int.castRingHom ℂ) f) = 0
    rw [evalT_map_int, aeval_eq_zero_of_mem_coordIdeal hf, TensorProduct.tmul_zero]
  have hnil : IsNilpotent (evalT x P) := ⟨n, by
    rw [← map_pow]
    exact hker hn⟩
  have hev : evalT x P = ∑ k, c k ⊗ₜ[ℚ] aeval x (b k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, evalT_map_rat, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp
  rw [hev] at hnil
  exact nilp_coeff_eq_zero hs hnil

end Poly

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMDefs
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def unitDeg [DecidableEq K] (k₀ : K) : K → ℤ := fun k => if k = k₀ then 1 else 0

def blockDeg [DecidableEq K] (k₀ : K) (n : ℕ) : K → ℕ := fun k => if k = k₀ then n else 0

variable {Ω : Type} [Field Ω] [CharZero Ω]

def IsSecBasisM [DecidableEq K] (y : (Σ k, ι k) → Ω) (k₀ : K) (n : ℕ) {r : ℕ}
    (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) : Prop :=
  (∀ j, ∃ f : MRing ι, IsMultiHomog f (blockDeg k₀ n) ∧ b j = map (Int.castRingHom ℚ) f) ∧
    LinearIndependent ℤ (fun j => aeval y (b j)) ∧
    (Submodule.span ℤ (Set.range fun j => aeval y (b j))).toAddSubgroup = secM y (blockDeg k₀ n)


end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HasFDerivAtMvPolynomialEval
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Complex Filter Topology Finset Matrix

open MvPolynomial Complex Filter Topology

section

variable {D : ℕ}

theorem bilinear_real_imag_expand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (a b : Fin D → ℝ) (e f : Fin D → V) :
    B (∑ i, (a i • e i + b i • f i)) (∑ j, (a j • e j + b j • f j)) =
      ∑ i, ∑ j, (a i * a j * B (e i) (e j) + a i * b j * B (e i) (f j) +
        b i * a j * B (f i) (e j) + b i * b j * B (f i) (f j)) := by
  have key : ∀ (u w : Fin D → V), B (∑ i, u i) (∑ j, w j) = ∑ i, ∑ j, B (u i) (w j) := by
    intro u w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ContinuousLinearMap.sum_apply]
    first
      | rfl
      | exact Finset.sum_comm
  rw [key]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem decompose_real_imag_basis (v : Fin D → ℂ) :
    v = ∑ i, ((v i).re • (Pi.single i (1 : ℂ) : Fin D → ℂ) +
      (v i).im • (I • (Pi.single i (1 : ℂ) : Fin D → ℂ))) := by
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, Finset.sum_add_distrib]
  apply Complex.ext <;> simp

theorem leviForm_eq_complexHessian (φ : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) :
    (fderiv ℝ (fderiv ℝ φ) y w w + fderiv ℝ (fderiv ℝ φ) y (I • w) (I • w)) / 4 =
      (∑ i, ∑ j, starRingEnd ℂ (w i) * cxHessian φ y j i * w j).re := by
  have hw := decompose_real_imag_basis w
  have hIw : I • w = ∑ i, ((-(w i).im) • (Pi.single i (1 : ℂ) : Fin D → ℂ) +
      (w i).re • (I • (Pi.single i (1 : ℂ) : Fin D → ℂ))) := by
    rw [decompose_real_imag_basis (I • w)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
  have e1 := bilinear_real_imag_expand (fderiv ℝ (fderiv ℝ φ) y) (fun i => (w i).re) (fun i => (w i).im)
      (fun i => (Pi.single i (1 : ℂ) : Fin D → ℂ)) (fun i => I • (Pi.single i (1 : ℂ) : Fin D → ℂ))
  have e2 := bilinear_real_imag_expand (fderiv ℝ (fderiv ℝ φ) y) (fun i => -(w i).im) (fun i => (w i).re)
      (fun i => (Pi.single i (1 : ℂ) : Fin D → ℂ)) (fun i => I • (Pi.single i (1 : ℂ) : Fin D → ℂ))
  simp only [← hw] at e1
  simp only [← hIw] at e2
  rw [e1, e2, ← Finset.sum_add_distrib]
  simp only [Complex.re_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin D))) (t := Finset.univ)
    (f := fun i j => ((starRingEnd ℂ) (w i) * cxHessian φ y j i * w j).re)]
  rw [div_eq_iff (by norm_num : (4 : ℝ) ≠ 0), Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [cxHessian]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_re, Complex.div_im, Complex.conj_re,
    Complex.conj_im, Complex.normSq]
  ring

end

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

