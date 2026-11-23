module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyOneTwoDualResolution
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FirstBetti

theorem finrank_homology_succ_add (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K]
    (C : CochainComplex (ModuleCat.{0} O) ℕ) [∀ i, Module.Finite O (C.X i)] (n : ℕ) :
    Module.finrank K ((((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj
        C).homology (n + 1))
      + Module.finrank K (LinearMap.range ((C.d n (n + 1)).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d (n + 1) (n + 2)).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X (n + 1)) := by
  let D := ((ModuleCat.extendScalars (algebraMap O K)).mapHomologicalComplex _).obj C
  have e1 := (D.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).toLinearEquiv
  obtain ⟨e2⟩ := GlobalTheory.Semicont.nonempty_homology_map_extendScalars_equiv K (C.sc' n (n + 1) (n + 2))
  have h := GlobalTheory.Semicont.finrank_homology_add_finrank_range
    ((C.d n (n + 1)).hom.baseChange K) ((C.d (n + 1) (n + 2)).hom.baseChange K)
    (by rw [← LinearMap.baseChange_comp, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero,
      LinearMap.baseChange_zero])
  rw [(e1.trans e2).finrank_eq]
  exact h

theorem smul_eq_zero_of_algebraMap_eq_zero {O : Type} [CommRing O] {K : Type} [Field K]
    [Algebra O K] {M : Type} [AddCommGroup M] [Module O M] {r : O} (hr : algebraMap O K r = 0)
    (z : K ⊗[O] M) : r • z = 0 := by
  rw [← algebraMap_smul K r z, hr, zero_smul]

theorem baseChange_eq_zero_of_ring {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] (e : M →ₗ[O] O)
    (he : ∀ x, algebraMap O K (e x) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, ← mul_one (e x), ← smul_eq_mul,
      TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x)]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, LinearMap.zero_apply, add_zero]

theorem baseChange_eq_zero_of_pi {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
    {M : Type} [AddCommGroup M] [Module O M] {n : ℕ} (e : M →ₗ[O] (Fin n → O))
    (he : ∀ x i, algebraMap O K (e x i) = 0) : e.baseChange K = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k x =>
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply, pi_eq_sum_univ (e x),
      TensorProduct.tmul_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [TensorProduct.tmul_smul, smul_eq_zero_of_algebraMap_eq_zero (he x i)]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, LinearMap.zero_apply, add_zero]

end GlobalTheory.FirstBetti

namespace GlobalTheory


open FirstBetti in
theorem finrank_homology_one_two_of_dual_resolution : ∀ (O : Type) [CommRing O] [IsRegularLocalRing O] (g : ℕ), ringKrullDim O = g → ∀ (f : Fin g → O), Ideal.span (Set.range f) ≠ ⊤ → IsArtinianRing (O ⧸ Ideal.span (Set.range f)) → ∀ (C : CochainComplex (ModuleCat.{0} O) ℕ), (∀ i, Module.Free O (C.X i) ∧ Module.Finite O (C.X i)) → (∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] (O ⧸ Ideal.span (Set.range f))) → ∀ (K : Type) [Field K] (φ : O →+* K), RingHom.ker φ = IsLocalRing.maximalIdeal O → Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1) = g ∧ Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2) ≤ g.choose 2 := by
  intro O _ _ g hdim f hne hart C hC hex hN K _ φ hker
  obtain ⟨eN⟩ := hN
  letI := φ.toAlgebra
  haveI : ∀ i, Module.Free O (C.X i) := fun i => (hC i).1
  haveI : ∀ i, Module.Finite O (C.X i) := fun i => (hC i).2
  have hIm : Ideal.span (Set.range f) ≤ IsLocalRing.maximalIdeal O := IsLocalRing.le_maximalIdeal hne
  have hIφ : ∀ x ∈ Ideal.span (Set.range f), algebraMap O K x = 0 := fun x hx => by
    have : x ∈ RingHom.ker φ := hker ▸ hIm hx
    exact this

  have hreg : RingTheory.Sequence.IsRegular O (List.ofFn f) := by
    refine GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le O g g f hdim
      (fun i => hIm (Ideal.subset_span ⟨i, rfl⟩)) ?_
    have h0 : ringKrullDim (O ⧸ Ideal.span (Set.range f)) ≤ 0 := Ring.krullDimLE_iff.1 inferInstance
    calc ringKrullDim (O ⧸ Ideal.span (Set.range f)) + (g : WithBot ℕ∞) ≤ 0 + (g : WithBot ℕ∞) :=
          add_le_add_left h0 _
      _ = g := zero_add _
  obtain ⟨e₁, e₂, hx1, hx2, he1, he2⟩ := _root_.GlobalTheory.koszul_resolution_three_terms O g f hreg.toIsWeaklyRegular

  let ε : Module.Dual O (C.X 0) →ₗ[O] O ⧸ Ideal.span (Set.range f) :=
    eN.toLinearMap ∘ₗ (LinearMap.range (C.d 0 1).hom.dualMap).mkQ
  have hεs : Function.Surjective ε := eN.surjective.comp (Submodule.mkQ_surjective _)
  have hεx : Function.Exact (C.d 0 1).hom.dualMap ε := by
    rw [LinearMap.exact_iff, LinearEquiv.ker_comp, Submodule.ker_mkQ]
  obtain ⟨hA, hB⟩ := _root_.GlobalTheory.AbCoh.finrank_homology_base_change_resolutions O K (O ⧸ Ideal.span (Set.range f))
    (Module.Dual O (C.X 0)) (Module.Dual O (C.X 1)) (Module.Dual O (C.X 2)) (Module.Dual O (C.X 3))
    O (Fin g → O) (Fin (g.choose 2) → O) ε (C.d 0 1).hom.dualMap (C.d 1 2).hom.dualMap
    (C.d 2 3).hom.dualMap (Ideal.span (Set.range f)).mkQ e₁ e₂ hεs hεx (hex 0) (hex 1)
    (Submodule.mkQ_surjective _) hx1 hx2

  have hz1 : e₁.baseChange K = 0 := baseChange_eq_zero_of_ring e₁ fun x => hIφ _ (he1 x)
  have hz2 : e₂.baseChange K = 0 := baseChange_eq_zero_of_pi e₂ fun x i => hIφ _ (he2 x i)
  have hk1 : Module.finrank K (LinearMap.ker (e₁.baseChange K)) = g := by
    rw [hz1, LinearMap.ker_zero, finrank_top, GlobalTheory.Semicont.finrank_baseChange_fin]
  have hr2 : Module.finrank K (LinearMap.range (e₂.baseChange K)) = 0 := by
    rw [hz2, LinearMap.range_zero, finrank_bot]
  have hc2 : Module.finrank K (K ⊗[O] (Fin (g.choose 2) → O)) = g.choose 2 :=
    GlobalTheory.Semicont.finrank_baseChange_fin _ _

  obtain ⟨r0, n0⟩ := _root_.GlobalTheory.AbCoh.finrank_range_baseChange_eq_dualMap_and_finrank_dual O K (C.X 0) (C.X 1) (C.d 0 1).hom
  obtain ⟨r1, n1⟩ := _root_.GlobalTheory.AbCoh.finrank_range_baseChange_eq_dualMap_and_finrank_dual O K (C.X 1) (C.X 2) (C.d 1 2).hom
  obtain ⟨r2, n2⟩ := _root_.GlobalTheory.AbCoh.finrank_range_baseChange_eq_dualMap_and_finrank_dual O K (C.X 2) (C.X 3) (C.d 2 3).hom
  have k1 := LinearMap.finrank_range_add_finrank_ker ((C.d 0 1).hom.dualMap.baseChange K)
  have k2 := LinearMap.finrank_range_add_finrank_ker ((C.d 1 2).hom.dualMap.baseChange K)

  have h1 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 1)
      + Module.finrank K (LinearMap.range ((C.d 0 1).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 1) := finrank_homology_succ_add O K C 0
  have h2 : Module.finrank K ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology 2)
      + Module.finrank K (LinearMap.range ((C.d 1 2).hom.baseChange K))
      + Module.finrank K (LinearMap.range ((C.d 2 3).hom.baseChange K))
      = Module.finrank K (K ⊗[O] C.X 2) := finrank_homology_succ_add O K C 1
  constructor <;> omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockColumnSubstitutionExpOfColumnDerivation
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem totalDegree_colSub_le {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    (colSub g P).totalDegree ≤ P.totalDegree := by
  have hX : ∀ y : Var ι d a, (colSub g (X y : Pol ι d a)).totalDegree ≤ 1 := by
    intro y
    rw [colSub, aeval_X]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  conv_lhs => rw [as_sum P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine le_trans ?_ (le_totalDegree hm)
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [map_pow]
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (m y) (hX y)

theorem hasDerivAt_dual_of_coeff {σ : Type} [Finite σ] (l : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (N : ℕ)
    (u : ℝ → MvPolynomial σ ℂ) (u' : MvPolynomial σ ℂ) (t : ℝ) (hu : ∀ s, (u s).totalDegree ≤ N)
    (hd : ∀ m, HasDerivAt (fun s => AddMonoidAlgebra.coeff (u s) m) (AddMonoidAlgebra.coeff u' m) t) : HasDerivAt (fun s => l (u s)) (l u') t := by
  classical
  let A : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset ∪ u'.support
  have key : ∀ P : MvPolynomial σ ℂ, P.support ⊆ A → l P = ∑ m ∈ A, AddMonoidAlgebra.coeff P m * l (monomial m 1) := by
    intro P hP
    conv_lhs => rw [as_sum P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_subset_zero_on_sdiff hP (fun m hm => ?_) (fun m _ => ?_)
    · rw [notMem_support_iff.1 (Finset.mem_sdiff.1 hm).2, zero_mul]
    · rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  have h1 : ∀ s, (u s).support ⊆ A := by
    intro s m hm
    refine Finset.mem_union_left _ ?_
    rw [Set.Finite.mem_toFinset]
    exact (le_totalDegree hm).trans (hu s)
  rw [key u' Finset.subset_union_right, funext fun s => key (u s) (h1 s)]
  exact HasDerivAt.fun_sum fun m _ => (hd m).mul_const _

omit [Fintype ι] in
theorem atPl_mul {a : ℕ} (τ : ι) (A B : Matrix (Fin a) (Fin a) ℂ) :
    atPl τ (A * B) = fun σ => atPl τ A σ * atPl τ B σ := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp [atPl]
  · simp [atPl, h]

theorem colSub_atPl_one {d a : ℕ} (τ : ι) (P : Pol ι d a) : colSub (atPl τ 1) P = P := by
  have : (colSub (atPl τ 1) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
    refine algHom_ext fun v => ?_
    have h1 : atPl τ (1 : Matrix (Fin a) (Fin a) ℂ) v.1 = 1 := by
      by_cases h : v.1 = τ
      · rw [h]; simp [atPl]
      · simp [atPl, h]
    rw [colSub, aeval_X, h1, Finset.sum_eq_single v.2.2]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne hb]
      simp
    · simp
  rw [this, AlgHom.id_apply]

theorem colSub_exp_of_colDer : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (c : ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Q),
    (∀ (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a) (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
      HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R) m)
        (AddMonoidAlgebra.coeff (GlobalTheory.ColLie.colDer τ S R) m) 0) →
    (∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P, q (GlobalTheory.ColLie.colDer τ S P) = ((c : ℂ) * S.trace) • q P) →
    ∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P,
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp S)) P) = ((NormedSpace.exp S).det ^ c) • q P := by
  intro ι _ _ d a τ c Q _ _ q hco hq S hS P
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul]
  set k : ℂ := (c : ℂ) * S.trace with hk
  let R : ℝ → Pol ι d a := fun t => colSub (atPl τ (NormedSpace.exp ((t : ℂ) • S))) P
  let f : ℝ → ℂ := fun t => l (q (R t))
  have hadd : ∀ s t : ℝ, colSub (atPl τ (NormedSpace.exp ((s : ℂ) • S))) (R t) = R (s + t) := by
    intro s t
    simp only [R]
    rw [← colSub_mul, ← atPl_mul, Complex.ofReal_add, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl S).smul_left _).smul_right _)]
  have hd : ∀ t, HasDerivAt f (f t * k) t := by
    intro t
    have h0 := hasDerivAt_dual_of_coeff (l ∘ₗ q) (R t).totalDegree
      (fun h : ℝ => colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) (R t)) (colDer τ S (R t)) 0
      (fun s => totalDegree_colSub_le _ _) (hco S (R t))
    simp only [hadd, LinearMap.comp_apply, hq S hS, map_smul, smul_eq_mul] at h0
    rw [← sub_self t] at h0
    have h1 := h0.comp_sub_const t t
    simp only [sub_add_cancel] at h1
    rw [mul_comm]
    exact h1
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * k))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * k)) (-k) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const k).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, R, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, NormedSpace.exp_zero, colSub_atPl_one,
    one_mul, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [← hc, GlobalTheory.SUVol.det_exp, ← Complex.exp_nat_mul, ← hk, mul_comm, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

end GlobalTheory.ColLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HtMapLeOfPoints
section
open Module NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.DescentFamily

open Formalism.HN

theorem numeric {a N mu muA ht mm P Λ ε t : ℝ} (ha : 0 < a) (haN : a ≤ N) (hN : N ≤ (1 + ε) * a)
    (hΛ : 0 ≤ Λ) (hε : 0 ≤ ε) (hht : ht ≤ 2 * P) (hmm : -(2 * Λ) ≤ mm) (ht' : t ≤ muA - 2 * P)
    (h : a * (muA - ht) + (N - a) * mm ≤ N * mu) : t - ε * (|t| + 2 * Λ) ≤ mu := by
  have hN0 : 0 < N := ha.trans_le haN
  have h1 : a * t ≤ a * (muA - ht) := mul_le_mul_of_nonneg_left (by linarith) ha.le
  have h2 : (N - a) * (-(2 * Λ)) ≤ (N - a) * mm := mul_le_mul_of_nonneg_left hmm (by linarith)
  have h3 : (N - a) * t ≤ (N - a) * |t| := mul_le_mul_of_nonneg_left (le_abs_self t) (by linarith)
  have h4 : N - a ≤ ε * N := by nlinarith
  have h5 : (N - a) * (|t| + 2 * Λ) ≤ ε * N * (|t| + 2 * Λ) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  refine le_of_mul_le_mul_left ?_ hN0
  nlinarith

section

variable {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

theorem htMap_le_of_points (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (φ : V →ₗ[K] W) (hφ : φ ≠ 0) (P : ℝ)
    (h : ∀ v f, Formalism.HermitianLatticesTheory.normAt b' X' v (φ f) ≤ Real.exp P * Formalism.HermitianLatticesTheory.normAt b X v f) :
    htMap b X b' X' φ ≤ 2 * P := by
  have hf : (0 : ℝ) < (nPl K : ℝ) := by
    unfold nPl
    exact_mod_cast Fintype.card_pos
  have h1 : ∀ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ 2 * P := by
    intro v
    rw [Real.log_pow]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Real.log_le_iff_le_exp (PlaceOperatorNorms.opNormAt_pos b X b' X' hX hX' v φ hφ)]
    exact Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X b' X' hX φ v _ (Real.exp_pos _).le (h v)
  unfold htMap
  have h2 : ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ (nPl K : ℝ) * (2 * P) := by
    calc _ ≤ ∑ _v : InfinitePlace K, 2 * P := Finset.sum_le_sum fun v _ => h1 v
      _ = (nPl K : ℝ) * (2 * P) := by simp [nPl]
  calc 1 / (nPl K : ℝ) * ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)
      ≤ 1 / (nPl K : ℝ) * ((nPl K : ℝ) * (2 * P)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * P := by field_simp

theorem normAt_pi_sq [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K)
    (x : Fin n → V) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v x ^ 2 =
        ∑ j, Formalism.HermitianLatticesTheory.normAt b X v (x j) ^ 2 := by
  simp only [← Formalism.ExtensionFiltration.majAt_self_re]
  rw [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_pi b X hX, Complex.re_sum]

end

theorem descent : ∀ (K V W : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (NA : (K →+* ℂ) → V → ℝ) (NB : (K →+* ℂ) → W → ℝ) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W) (n : ℕ) (φ : Fin n → V →ₗ[K] W) (P Λ ε t : ℝ), HasGram NA → HasGram NB → A.FG → B.FG → A ≠ ⊥ → (∀ h, ∀ f ∈ A, φ h f ∈ B) → (∀ f, (∀ h, φ h f = 0) → f = 0) → (∀ σ f, ∑ h, NB σ (φ h f) ^ 2 ≤ Real.exp (2 * P) * NA σ f ^ 2) → (∃ s : Set W, s ⊆ (B : Set W) ∧ (∀ y ∈ s, ∀ σ, NB σ y ≤ Real.exp Λ) ∧ (B : Set W) ⊆ (Submodule.span K s : Set W)) → 0 ≤ Λ → 0 ≤ ε → (n : ℝ) * Formalism.HN.rkK B ≤ (1 + ε) * Formalism.HN.rkK A → t ≤ slope_sq NA A - 2 * P → t - ε * (|t| + 2 * Λ) ≤ slope_sq NB B := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ NA NB A B n φ P Λ ε t hA hB hAfg hBfg hA0 hint hinj hnorm hs hΛ hε hrk ht
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨p, ⟨b, X⟩, hGA⟩⟩ := hA
  obtain ⟨⟨q, ⟨b', X'⟩, hGB⟩⟩ := hB
  change IsGram b X NA at hGA
  change IsGram b' X' NB at hGB
  have hX : ∀ v, IsUnit (X v).det := fun v => (hGA v).1
  have hX' : ∀ v, IsUnit (X' v).det := fun v => (hGB v).1
  rw [slope_sq_eq hGA hAfg] at ht
  rw [slope_sq_eq hGB hBfg]
  obtain ⟨f0, hf0A, hf0⟩ := (Submodule.ne_bot_iff A).1 hA0
  obtain ⟨h0, hh0⟩ : ∃ h, φ h f0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf0 (hinj f0 hc)
  have hn : 0 < n := h0.pos
  have hB0 : B ≠ ⊥ := (Submodule.ne_bot_iff B).2 ⟨_, hint h0 f0 hf0A, hh0⟩
  obtain ⟨p1, p2, -⟩ := Formalism.BranchingDeterminantCap.power_slope_mu K W _ b' X' hX' B n hBfg hB0 hn
  set bn : Basis (Σ _ : Fin n, Fin q) K (Fin n → W) := Pi.basis fun _ : Fin n => b' with hbn
  set Xn : InfinitePlace K → Matrix (Σ _ : Fin n, Fin q) (Σ _ : Fin n, Fin q) ℂ :=
    fun v => Matrix.blockDiagonal' fun _ : Fin n => X' v with hXndef
  set Bn : Submodule (𝓞 K) (Fin n → W) := Submodule.pi Set.univ fun _ : Fin n => B with hBn
  have hXn : ∀ v, IsUnit (Xn v).det := fun v => Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_det (X' v) (hX' v)
  have hBnfg : Bn.FG := Submodule.fg_pi fun _ => hBfg
  let Φ : V →ₗ[K] (Fin n → W) := LinearMap.pi φ
  have hΦinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    exact fun f hf => hinj f fun h => congrFun hf h
  have hΦle : A.map (Φ.restrictScalars (𝓞 K)) ≤ Bn := by
    rintro _ ⟨f, hf, rfl⟩ h -
    exact hint h f hf
  have hΦ0 : Φ ≠ 0 := fun h => hh0 (congrFun (LinearMap.congr_fun h f0) h0)
  have hBn0 : Bn ≠ ⊥ := (Submodule.ne_bot_iff Bn).2
    ⟨Φ f0, hΦle ⟨f0, hf0A, rfl⟩, fun h => hh0 (congrFun h h0)⟩
  have hht : htMap b X bn Xn Φ ≤ 2 * P := by
    refine htMap_le_of_points b X bn Xn hX hXn Φ hΦ0 P fun v f => ?_
    have n0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt b X v f := Real.sqrt_nonneg _
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [hbn, hXndef, normAt_pi_sq b' X' hX', mul_pow, ← Real.exp_nat_mul, (hGA v).2]
    simp only [(hGB v).2]
    exact_mod_cast hnorm v.embedding f
  have hmm : -(2 * Λ) ≤ muMinDef bn Xn Bn := by
    obtain ⟨s, hsB, hsn, hsp⟩ := hs
    refine Formalism.ExtensionFiltration.spanMuMin K _ _ bn Xn hXn Bn Λ hBnfg hBn0
      ⟨⋃ i : Fin n, (fun y => (Pi.single i y : Fin n → W)) '' s, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      intro j _
      by_cases hj : j = i
      · subst hj; simpa using hsB hy
      · simp [Pi.single_eq_of_ne hj]
    · intro x hx v
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      rw [hbn, hXndef, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.normAt_single b' X' hX', (hGB v).2]
      exact hsn y hy _
    · intro x hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h1 : x i ∈ Submodule.span K s := hsp (hx i trivial)
      have h2 := Submodule.mem_map_of_mem (f := LinearMap.single K (fun _ : Fin n => W) i) h1
      rw [Submodule.map_span] at h2
      exact Submodule.span_mono (Set.subset_iUnion
        (fun i : Fin n => (fun y => (Pi.single i y : Fin n → W)) '' s) i) h2
  have hd := Formalism.ExtensionFiltration.descentSlope K V _ (Fin n → W) _ b X bn Xn hX hXn Φ A Bn hAfg hBnfg hA0 hΦinj hΦle
  rw [p2] at hd
  have hle : rkK A ≤ rkK Bn := by
    haveI : Module.Finite K (Fin n → W) := Module.Finite.of_basis bn
    rw [← Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_map Φ hΦinj A]
    exact Submodule.finrank_mono (Submodule.span_mono hΦle)
  have hpos : 0 < rkK A := Nat.pos_of_ne_zero (Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b A hA0)
  refine numeric (a := rkK A) (N := rkK Bn) (by exact_mod_cast hpos) (by exact_mod_cast hle) ?_ hΛ hε hht hmm ht hd
  rw [p1]
  push_cast
  exact hrk

end GlobalTheory.DescentFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedOfLocally
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_locally : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (k : (Fin g → ℂ) → ℂ), (∀ z ∈ pre u.ex U, ∃ W : A.left.Opens, W ≤ U ∧ z ∈ pre u.ex W ∧ IsReg u.ex W k) → IsReg u.ex U k := by
  intro A _ g L u hA U k h
  choose! W hWU hzW hreg using h
  let K : Type := {z // z ∈ pre u.ex U}
  let V : K → A.left.Opens := fun z => W z.1
  have hVU : ∀ i : K, V i ≤ U := fun i => hWU i.1 i.2
  have hb : ∀ i : K, ∃ b : Γ(A.left, V i), ∀ z ∈ pre u.ex (V i), k z = val u.ex (V i) b z := fun i => hreg i.1 i.2
  choose b hb using hb
  have hcov : U ≤ ⨆ i, V i := _root_.GlobalTheory.CechPer.le_iSup_of_pre_cover A g L u hA U K V fun z hz => ⟨⟨z, hz⟩, hzW z hz⟩
  have hcompat : TopCat.Presheaf.IsCompatible A.left.sheaf.1 V b := by
    intro i j
    rw [← sub_eq_zero]
    refine _root_.GlobalTheory.ValInj.eq_zero_of_val_eq_zero A g L u hA (V i ⊓ V j) _ fun z hz => ?_
    have hz' := (GlobalTheory.top_le_preimage_inf (u.ex z).left (V i) (V j)).1 hz
    have e1 := GlobalTheory.valAt'_map (u.ex z).left (TopologicalSpace.Opens.infLELeft (V i) (V j)).op (b i) hz
    have e2 := GlobalTheory.valAt'_map (u.ex z).left (TopologicalSpace.Opens.infLERight (V i) (V j)).op (b j) hz
    refine (GlobalTheory.valAt'_sub (u.ex z).left (V i ⊓ V j) _ _).trans ?_
    rw [sub_eq_zero]
    exact e1.trans (((hb i z hz'.1).symm.trans (hb j z hz'.2)).trans e2.symm)
  obtain ⟨s, hs, -⟩ := A.left.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hVU i)) hcov b hcompat
  refine ⟨s, fun z hz => ?_⟩
  have h1 := hb ⟨z, hz⟩ z (hzW z hz)
  have h2 := GlobalTheory.valAt'_map (u.ex z).left (homOfLE (hVU ⟨z, hz⟩)).op s (hzW z hz)
  rw [h1, ← hs ⟨z, hz⟩]
  exact h2

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoNormalisationAtZeroSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isoNormalisation_at_zeroSection : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)ˣ), (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Normal t c αA βB → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ (φB' ≫ GlobalTheory.HomFixUniv.θ B)).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p) (by simp)).hom (c i j) *
          ((φA' ≫ GlobalTheory.HomFixUniv.θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (u p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' (φA' ≫ GlobalTheory.HomFixUniv.θ A) (φB' ≫ GlobalTheory.HomFixUniv.θ B)).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k := by
  first | (exact @GlobalTheory.HomFixNorm.norm_at_zero) | (exact GlobalTheory.HomFixNorm.norm_at_zero) | (intros; apply GlobalTheory.HomFixNorm.norm_at_zero  <;> assumption)
end

