module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsUnitInvertibleMatrixIdentificationBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem UpperTheory.KN.basis_change_matrices_algebra_map {O R R' M ι : Type} [CommRing O] [CommRing R] [CommRing R']
    [Algebra O R] [Algebra O R'] [AddCommGroup M] [Module O M] [Fintype ι] [DecidableEq ι]
    (f : R →ₐ[O] R') (b : Module.Basis ι O M) (jD : (ι → R') ≃ₗ[R'] R' ⊗[O] M) (u : R)
    (z : ι → R ⊗[O] M)
    (h : ∀ i, jD (fun j => f ((Pi.single i u : ι → R) j)) =
      TensorProduct.map f.toLinearMap LinearMap.id (z i)) :
    ∃ (m m' : Matrix ι ι R') (r : ι → ι → R), m' * m = 1 ∧ (∀ i, z i = ∑ k, r i k ⊗ₜ[O] b k) ∧
      ∀ i k, f (r i k) = f u * m i k := by
  let bA := Algebra.TensorProduct.basis R b
  let bD := Algebra.TensorProduct.basis R' b
  have hz : ∀ i, z i = ∑ k, bA.repr (z i) k ⊗ₜ[O] b k := by
    intro i
    conv_lhs => rw [← bA.sum_repr (z i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [bA, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  refine ⟨Matrix.of fun i k => bD.repr (jD (Pi.single i 1)) k, Matrix.of fun k i => jD.symm (bD k) i,
    fun i k => bA.repr (z i) k, ?_, hz, ?_⟩
  · ext k k'
    have h1 : jD.symm (bD k) = ∑ i, jD.symm (bD k) i • (Pi.single i 1 : ι → R') := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 : bD k = ∑ i, jD.symm (bD k) i • jD (Pi.single i 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← jD.apply_symm_apply (bD k), h1, map_sum]
      simp only [map_smul]
    have h3 := congrArg (fun x => bD.repr x k') h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self, Finsupp.single_apply] at h3
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact h3.symm
  · intro i k
    have e1 : (fun j => f ((Pi.single i u : ι → R) j)) = f u • (Pi.single i 1 : ι → R') := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    have e2 : TensorProduct.map f.toLinearMap LinearMap.id (z i) = ∑ k, f (bA.repr (z i) k) • bD k := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [hz i, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [bD, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
    have h3 := h i
    rw [e1, e2, map_smul] at h3
    have h4 := congrArg (fun x => bD.repr x k) h3
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_sum_self] at h4
    exact h4.symm

theorem _root_.UpperTheory.KN.exists_unit_invertible_matrix_identification_basis :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (b : Module.Basis ι ↥(OL LL) ↥T.L.T), ∃ (m m' : Matrix ι ι (OD l ↥(OL LL))) (u : OA l ↥(OL LL)) (r : ι → ι → OA l ↥(OL LL)), IsUnit (toOD l ↥(OL LL) u) ∧ m' * m = 1 ∧ (∀ i, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T (∑ k, r i k ⊗ₜ[↥(OL LL)] b k)) ∧ ∀ i k, toOD l ↥(OL LL) (r i k) = toOD l ↥(OL LL) u * m i k := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I b
  obtain ⟨jD, hjD⟩ := GlobalTheory.DeRhamIdent.main l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I
  obtain ⟨u, hu, hz⟩ := UpperTheory.KN.exists_unit_identification_single_integral l a e ϖ LL ι P T I
  choose z hz using hz
  obtain ⟨m, m', r, h1, h2, h3⟩ := UpperTheory.KN.basis_change_matrices_algebra_map (toOD l ↥(OL LL)) b jD u z
    (fun i => hjD _ _ (hz i))
  refine ⟨m, m', u, r, hu, h1, fun i => (hz i).trans ?_, h3⟩
  exact congrArg (TWincl (inclO l ↥(OL LL)) T) (h2 i)
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModCrystallineComparisonOfIsCrisCmp
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem twSmul {O R R' G Qp LL : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL]
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWincl, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]

private theorem mxMem {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
    {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {α : ℕ} (hα : ∀ m ∈ P.L, E K l e ^ α • m ∈ P.M)
    (τ : ZMod a) (i j : ι) : E K l e ^ α * P.mx τ i j ∈ A O K := by
  let m : Vec K a ι := Pi.single τ (P.mx τ *ᵥ Pi.single j 1)
  have hm : m ∈ P.L := mem_tot.2 fun σ => by
    by_cases hσ : σ = τ
    · subst hσ
      simp only [m, Pi.single_eq_same]
      exact P.mem_extc.2 ⟨_, fun k => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _], rfl⟩
    · simp only [m, Pi.single_eq_of_ne hσ]
      exact zero_mem _
  have := mem_tot.1 (hα m hm) τ i
  simpa [m] using this

theorem _root_.UpperTheory.KN.phiMod_crystalline_comparison_of_isCrisCmp :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T) (C : GlobalTheory.MemLoc.Core l) (ε : OCb l), IsEps ε → IsCrisCmp I jB →
    (∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z) →
    ∀ α : ℕ, (∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) →
    ∀ σ : P.MMl, TWincl (dRO l O) T (jD (GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • σ.1))) =
      dRO l O (GlobalTheory.GalStep.ED K t ϖ) ^ α • TWincl (iotaO O C) T (jB (toBcris t ϖ P σ)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB jD C ε hε hB hD α hα σ
  have hx : ∀ τ i j, E K l e ^ α * P.mx τ i j ∈ A O K := mxMem P hα
  have hσ : toBcris t ϖ P σ = ∑ j, ϖ.iB t K (coordL P (invL l (S O K e)) σ j) •
      (Pi.single j 1 : ι → OB l O) := by
    funext i
    rw [toBcris_apply, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro j _ hj
      rw [Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [UpperTheory.KN.phiMod_deRham_image_coord_expansion l a e O K t ϖ ι P α hx σ, hσ, map_sum, map_sum, map_sum, map_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [jD.map_smul, jB.map_smul, twSmul, twSmul,
    UpperTheory.KN.tame_phiModule_crystalline_basis_compat l a e O K t ϖ ι P T I jB jD C ε hε hB hD α hα hx j,
    UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD l a e O K t ϖ C, smul_smul, smul_smul, mul_comm]
end

