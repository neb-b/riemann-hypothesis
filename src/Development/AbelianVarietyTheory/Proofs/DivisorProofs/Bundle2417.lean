module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationsSamePointDifferByIsometry
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU

theorem exists_linMap_of_periods {O : Type} [Ring O] {bar : O → O} {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D₁ D₂ : PLat O bar) (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x, P (a • x) = ρ a *ᵥ P x) (hP' : ∀ (a : O) x, P' (a • x) = ρ a *ᵥ P' x)
    (hinj : Function.Injective P') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hr : ∀ x, ∃ y, P' y = h (P x))
    (hc : ∀ (a : O) z, h (ρ a *ᵥ z) = ρ a *ᵥ h z) :
    ∃ w : D₁.La →ₗ[O] D₂.La, ∀ x, P' (w x) = h (P x) := by
  choose f hf using hr
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩
  · intro x y
    apply hinj
    rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)]
  · intro a x
    apply hinj
    rw [RingHom.id_apply, hP', hf, hf, hP, hc]

theorem int_eq_of_exp_eq (m n : ℤ)
    (H : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  set k : ℕ := (n - m).natAbs + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos _
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp (H k hk)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have E : ((n - m : ℤ) : ℂ) = ((j * k : ℤ) : ℂ) := by
    push_cast
    field_simp at hj
    linear_combination hj
  have E' : n - m = j * k := by exact_mod_cast E
  have hd : (k : ℤ) ∣ n - m := ⟨j, by rw [E', mul_comm]⟩
  have h0 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by rw [Int.natAbs_natCast]; omega)
  omega

theorem unifAt_cmp : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e e', 0 < N → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D'' t' P' y e' → ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsMarkedIsom N D' D'' t t' w ∧ (∀ x, P' (w x) = h (P x)) ∧ ∀ z, e' (h z) = e z := by
  intro O _ bar g ρ R _ σ Λ F N D' D'' t t' P P' y e e' hN U1 U2
  obtain ⟨-, hper1, hexp1, hker1, hact1, hweil1, heta1⟩ := U1
  obtain ⟨-, hper2, hexp2, hker2, hact2, hweil2, heta2⟩ := U2
  have lift := fun (e₁ e₂ : (Fin g → ℂ) → (Over.mk y ⟶ F.A)) (α : F.A ⟶ F.A) (h1 : IsExp y e₁) (h2 : IsExp y e₂)
    (hα : IsMonHom α) => _root_.GlobalTheory.ExpLin.existsUnique_linear_lift F.X F.A g F.ab F.dim y e₁ e₂ α h1 h2 hα
  obtain ⟨M, hM, -⟩ := lift e e' (𝟙 _) hexp1 hexp2 inferInstance
  obtain ⟨M', hM', -⟩ := lift e' e (𝟙 _) hexp2 hexp1 inferInstance
  simp only [Category.comp_id] at hM hM'
  have h1 : M'.comp M = LinearMap.id := by
    obtain ⟨K, -, hK⟩ := lift e e (𝟙 _) hexp1 hexp1 inferInstance
    rw [hK (M'.comp M) (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]
  have h2 : M.comp M' = LinearMap.id := by
    obtain ⟨K, -, hK⟩ := lift e' e' (𝟙 _) hexp2 hexp2 inferInstance
    rw [hK (M.comp M') (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear M M' h2 h1
  have hh : ∀ z, e' (h z) = e z := hM
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ P'.range := fun z => by rw [← hker1, ← hker2, hh]
  have hc : ∀ (a : O) z, h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
    intro a z
    obtain ⟨K, -, hK⟩ := lift e e' (F.act a) hexp1 hexp2 (F.hom a)
    have k1 := hK ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp (Matrix.mulVecLin (ρ a)))
      (fun z => by simp [hh, hact1])
    have k2 := hK ((Matrix.mulVecLin (ρ a)).comp (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)))
      (fun z => by simp [hact2, hh])
    have := congrArg (fun f : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) => f z) (k1.trans k2.symm)
    simpa using this
  have hc' : ∀ (a : O) z, h.symm (ρ a *ᵥ z) = ρ a *ᵥ h.symm z := by
    intro a z
    apply h.injective
    rw [hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨w₁, hw₁⟩ := exists_linMap_of_periods ρ D' D'' P P' hper1.1 hper2.1 hper2.2.1 h
    (fun x => (AddMonoidHom.mem_range).mp ((hrange (P x)).mp ⟨x, rfl⟩)) hc
  obtain ⟨w₂, hw₂⟩ := exists_linMap_of_periods ρ D'' D' P' P hper2.1 hper1.1 hper1.2.1 h.symm
    (fun x => (AddMonoidHom.mem_range).mp ((hrange _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact ⟨x, rfl⟩))) hc'
  let w : D'.La ≃ₗ[O] D''.La := LinearEquiv.ofLinear w₁ w₂
    (LinearMap.ext fun x => hper2.2.1 (by simp [hw₁, hw₂]))
    (LinearMap.ext fun x => hper1.2.1 (by simp [hw₁, hw₂]))
  have hw : ∀ x, P' (w x) = h (P x) := hw₁
  refine ⟨w, h, ⟨?_, ?_⟩, hw, hh⟩
  · intro x x'
    refine (int_eq_of_exp_eq _ _ fun k hk => ?_)
    have H1 := hweil1 k x x' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have H2 := hweil2 k (w x) (w x') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    rw [hw, hw, ← LinearEquiv.map_smul, ← LinearEquiv.map_smul, hh, hh] at H2
    have := _root_.GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex F.X F.A g F.ab F.dim F.L F.isLB y k _ _ _ _ H2 H1
    simpa using congrArg Units.val this
  · intro a
    have e0 : e' 0 = 1 := (hker2 0).mpr (zero_mem _)
    set v := (N : ℂ)⁻¹ • P' (t' a)
    set u := (N : ℂ)⁻¹ • P' (w (t a)) - v
    have huv : e' (u + v) = e' v := by
      rw [sub_add_cancel, hw, ← LinearEquiv.map_smul, hh, ← heta1, heta2]
    have hu : e' u = 1 := by
      have := (hexp2.1 (u + v) (-v)).symm
      rw [add_neg_cancel_right, huv, ← hexp2.1, add_neg_cancel, e0] at this
      exact this.symm
    obtain ⟨x₀, hx₀⟩ := (hker2 u).mp hu
    refine ⟨x₀, ?_⟩
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    apply hper2.2.1
    have : P' (w (t a)) - P' (t' a) = (N : ℂ) • u := by
      simp only [u, v, ← smul_sub, smul_smul, mul_inv_cancel₀ hN', one_smul]
    rw [map_add (f := _), map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, hx₀, ← this]
    abel

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsDelOperatorDbarOperator
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.SmoothCoef

theorem contDiffOn_del_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => del f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [del_apply]
  exact ((h.clm_apply contDiffOn_const).sub ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_dbar_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => dbar f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [dbar_apply]
  exact ((h.clm_apply contDiffOn_const).add ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_coef : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧
      ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  intro n s F hs hF U
  constructor
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
      Finsupp.smul_apply, smul_eq_mul]
      exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_del_dir hs (hF S) _).mul contDiffOn_const
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
      Finsupp.smul_apply, smul_eq_mul]
      exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_dbar_dir hs (hF S) _).mul contDiffOn_const

end GlobalTheory.CxForm.SmoothCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderiv
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.PullSmooth

theorem repr_mul {m : ℕ} (a b : Alt m) (S : Finset (Fin (m + m))) :
    (bas m).repr (a * b) S = ∑ S₁, ∑ S₂, (bas m).repr a S₁ * (bas m).repr b S₂ *
      (bas m).repr (bas m S₁ * bas m S₂) S := by
  conv_lhs => rw [← (bas m).sum_repr a, ← (bas m).sum_repr b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]

theorem entries_smooth {m n : ℕ} {τ : V m → V n} {U : Set (V m)} (hU : IsOpen U) (hτ : DifferentiableOn ℂ τ U)
    (v : V m) (a : Fin n) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U ∧ ContDiffOn ℝ ∞ (fun x => conj (fderiv ℂ τ x v a)) U := by
  have h₁ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x) U :=
    ContDiffOn.fderiv_of_isOpen (n := ω) (m := ∞)
      (((GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn hU).2 hτ).contDiffOn hU.uniqueDiffOn) hU le_top
  have h₂ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x v a) U :=
    (EuclideanSpace.proj a : V n →L[ℂ] ℂ).contDiff.comp_contDiffOn (h₁.clm_apply contDiffOn_const)
  have h₃ : ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U := h₂.restrict_scalars ℝ
  exact ⟨h₃, Complex.conjCLE.contDiff.comp_contDiffOn h₃⟩

theorem contDiffOn_repr_pull_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U →
    DifferentiableOn ℂ τ U → ∀ S, ContDiffOn ℝ ∞ (fun x => (bas m).repr (pull (fderiv ℂ τ x) γ) S) U := by
  intro m n τ U γ hU hτ
  induction γ using ExteriorAlgebra.induction with
  | algebraMap r =>
    intro S
    simp only [AlgHom.commutes]
    exact contDiffOn_const
  | ι u =>
    intro S
    have hcoef : ∀ x, (bas m).repr (pull (fderiv ℂ τ x) (ExteriorAlgebra.ι ℂ u)) S =
        ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)
          (Matrix.toLin' (Matrix.fromBlocks (Matrix.of fun b a => fderiv ℂ τ x (coordVec b) a) 0 0
            (Matrix.of fun b a => conj (fderiv ℂ τ x (coordVec b) a))) u) := by
      intro x
      simp [pull, ExteriorAlgebra.map_apply_ι]
    simp_rw [hcoef]
    refine (LinearMap.toContinuousLinearMap ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)).contDiff.restrict_scalars ℝ
      |>.comp_contDiffOn ?_
    refine contDiffOn_pi.2 fun i => ?_
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ contDiffOn_const
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).1
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).2
  | mul a b ha hb =>
    intro S
    have e : (fun x => (bas m).repr (pull (fderiv ℂ τ x) (a * b)) S) = fun x => ∑ S₁, ∑ S₂,
        (bas m).repr (pull (fderiv ℂ τ x) a) S₁ * (bas m).repr (pull (fderiv ℂ τ x) b) S₂ *
          (bas m).repr (bas m S₁ * bas m S₂) S := funext fun x => by rw [map_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun S₁ _ => ContDiffOn.sum fun S₂ _ =>
      ((ha S₁).mul (hb S₂)).mul contDiffOn_const
  | add a b ha hb =>
    intro S
    simp only [map_add (f := _), Finsupp.add_apply]
    exact (ha S).add (hb S)

end GlobalTheory.PullSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimsLeHeight
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup.CotDim

theorem quot_finrank_le {k A : Type} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {I J : Ideal A} (hIJ : I ≤ J) : Module.finrank k (A ⧸ J) ≤ Module.finrank k (A ⧸ I) := by
  let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at this

theorem finrank_level_one {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) :
    Module.finrank k (G.A 1) = p ^ G.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := G.rank_eq 1 q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  simpa using h

end GlobalTheory.PDivGroup.CotDim

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotent
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem coeff_single_one_mul {σ R : Type} [CommRing R] [DecidableEq σ] (i : σ) (f g : MvPowerSeries σ R) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g + coeff (Finsupp.single i 1) f * constantCoeff g := by
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  rw [show (Finset.HasAntidiagonal.antidiagonal (1 : ℕ) : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} by decide]
  rw [Finset.sum_pair (by simp)]
  simp only [Function.Embedding.coe_prodMap, Prod.map_apply, Function.Embedding.coeFn_mk,
    Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply]

theorem counit_dUnit_evA : ∀ (k : Type) [CommRing k] (d : ℕ) (A : Type) [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)), (∀ i, Coalgebra.counit (R := k) (x i) = 0) → ∀ f : MvPowerSeries (Fin d) k, Coalgebra.counit (R := k) (evA k x hx f) = constantCoeff f ∧ dUnit (R := k) (evA k x hx f) = ∑ i, lin f i • dUnit (R := k) (x i) := by
  intro k _ d A _ _ x hx h0 f
  have hev : ∀ i, evA k x hx (X i) = x i := GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k (Fin d) A x hx
  let c0 : MvPowerSeries (Fin d) k →ₐ[k] k :=
    { (constantCoeff : MvPowerSeries (Fin d) k →+* k) with
      commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }
  have hc0 : ∀ g, c0 g = constantCoeff g := fun _ => rfl
  have h1 : (Bialgebra.counitAlgHom k A).comp (evA k x hx) = c0 :=
    _root_.GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent k (Fin d) k _ _ (fun i => by simp [hev, h0]) (fun i => by simp [hev, h0, hc0])
  refine ⟨(AlgHom.congr_fun h1 f).trans (hc0 f), ?_⟩
  letI : Module kᵐᵒᵖ (Cot k A) := Module.compHom _ ((RingHom.id k).fromOpposite mul_comm)
  haveI : IsCentralScalar k (Cot k A) := ⟨fun _ _ => rfl⟩
  let D : MvPowerSeries (Fin d) k →ₗ[k] Cot k A :=
    ∑ i, LinearMap.smulRight (coeff (Finsupp.single i 1)) (dUnit (R := k) (x i))
  have hD : ∀ g, D g = ∑ i, lin g i • dUnit (R := k) (x i) := fun g => by simp [D, lin]
  have hlin1 : ∀ i, lin (1 : MvPowerSeries (Fin d) k) i = 0 := fun i => by
    simp [lin, coeff_one]
  have hlinmul : ∀ (a b : MvPowerSeries (Fin d) k) i,
      lin (a * b) i = constantCoeff a * lin b i + lin a i * constantCoeff b := fun a b i =>
    coeff_single_one_mul i a b
  let L : MvPowerSeries (Fin d) k →ₗ[k] TrivSqZeroExt k (Cot k A) :=
    (TrivSqZeroExt.inlAlgHom k k (Cot k A)).toLinearMap ∘ₗ c0.toLinearMap +
        TrivSqZeroExt.inrHom k (Cot k A) ∘ₗ D
  have hLf : ∀ g, (L g).fst = constantCoeff g := fun g => by simp [L, hc0]
  have hLs : ∀ g, (L g).snd = ∑ i, lin g i • dUnit (R := k) (x i) := fun g => by simp [L, hD, TrivSqZeroExt.snd_sum]
  let ψ : MvPowerSeries (Fin d) k →ₐ[k] TrivSqZeroExt k (Cot k A) :=
    AlgHom.ofLinearMap L
      (by ext <;> simp [hLf, hLs, hlin1])
      (fun a b => by
        ext
        · simp [hLf]
        · rw [TrivSqZeroExt.snd_mul, hLs, hLs, hLs, hLf, hLf]
          simp only [hlinmul, add_smul, mul_smul, Finset.smul_sum, Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [op_smul_eq_smul, smul_comm])
  have hψf : ∀ g, (ψ g).snd = ∑ i, lin g i • dUnit (R := k) (x i) := hLs
  let φ : MvPowerSeries (Fin d) k →ₐ[k] TrivSqZeroExt k (Cot k A) :=
    (AugCot.toSqZero (Bialgebra.counitAlgHom k A) (LinearMap.id (M := Cot k A))).comp (evA k x hx)
  have hφf : ∀ g, (φ g).fst = Coalgebra.counit (R := k) (evA k x hx g) := fun g => by simp [φ]
  have hφs : ∀ g, (φ g).snd = dUnit (R := k) (evA k x hx g) := fun g => by simp [φ]
  have hlinX : ∀ i j, lin (X i : MvPowerSeries (Fin d) k) j = if j = i then 1 else 0 := fun i j => by
    simp [lin, coeff_X, Finsupp.single_left_inj one_ne_zero]
  have hφψ : φ = ψ := by
    refine _root_.GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent k (Fin d) _ _ _ (fun i => ⟨2, ?_⟩) (fun i => ?_)
    · ext
      · simp [pow_two, hφf, hev, h0]
      · simp [pow_two, TrivSqZeroExt.snd_mul, hφf, hev, h0]
    · ext
      · rw [hφf, hev, h0]; exact (constantCoeff_X i).symm.trans (hLf (X i)).symm
      · rw [hφs, hψf, hev]
        simp [hlinX]
  rw [← hφs, ← hψf, hφψ]

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two
open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cubeLB_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (f' g' : G₁ ⟶ G₁) (fA gA : A₁.A ⟶ A₂.A) (fA' gA' : A₁.A ⟶ A₁.A), Gen₀ U₁ U₂ f fA → Gen₀ U₁ U₂ g gA → Gen₀ U₁ U₁ f' fA' → Gen₀ U₁ U₁ g' gA' → LBIso (cubeLB G₂ ![fst G₁ G₁ ≫ f, snd G₁ G₁ ≫ g] U₂.LG.L) (cubeLB G₁ ![fst G₁ G₁ ≫ f', snd G₁ G₁ ≫ g'] U₁.LG.L) → LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ fA, snd A₁.A A₁.A ≫ gA] A₂.L) (cubeLB A₁.A ![fst A₁.A A₁.A ≫ fA', snd A₁.A A₁.A ≫ gA'] A₁.L) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ f g f' g' fA gA fA' gA' hf hg hf' hg' H
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G₁ G₁
  let u := lift (fst ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G₁) ((Over.pullback (jK R)).obj G₁) ≫ U₁.gen.hom)
  have key : ∀ {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
      (U : UnifPre I D A G) (x y : G₁ ⟶ G) (cx cy : A₁.A ⟶ A.A), Gen₀ U₁ U x cx → Gen₀ U₁ U y cy →
      CechPic.pull (pullback.fst (G₁ ⊗ G₁).hom (jK R)) (cubeCls G ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (cls U.LG.L U.LG.isLB)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A₁.A A₁.A ≫ cx, snd A₁.A A₁.A ≫ cy] (cls A.L A.isLB))) := by
    intro D A G _ _ U x y cx cy hx hy
    have hL := U.LG.isLB
    have hA := A.isLB
    have hgen := U.gen_hom
    have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    have hu : u.left ≫ (A₁.A ⊗ A₁.A).hom =
        ((Over.pullback (jK R)).obj G₁ ⊗ (Over.pullback (jK R)).obj G₁).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G₁ ⊗ G₁))
      (T := G₁ ⊗ G₁) (fun i => (Over.pullback (jK R)).map (![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] i))
      ![fst G₁ G₁ ≫ x, snd G₁ G₁ ≫ y] (pullback.fst (G₁ ⊗ G₁).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U.gen.hom).left = (u ≫ fst A₁.A A₁.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U.gen.hom).left = (u ≫ snd A₁.A A₁.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have eG := (cls_cubeLB G₂ _ U₂.LG.isLB).symm.trans (((cls_eq_iff (LB.isLB_linComb U₂.LG.isLB _ _)
    (LB.isLB_linComb U₁.LG.isLB _ _)).2 H).trans (cls_cubeLB G₁ _ U₁.LG.isLB))
  have e := (key U₂ f g fA gA hf hg).symm.trans ((congrArg _ eG).trans (key U₁ f' g' fA' gA' hf' hg'))
  let v := lift (fst A₁.A A₁.A ≫ U₁.gen.inv) (snd A₁.A A₁.A ≫ U₁.gen.inv)
  have hv : v ≫ u = 𝟙 _ := by ext <;> simp [u, v]
  have canc : ∀ c : Pic (A₁.A ⊗ A₁.A).left,
      CechPic.pull v.left (CechPic.pull (inv δ).left (CechPic.pull δ.left (CechPic.pull u.left c))) = c := by
    intro c
    rw [← pull_comp (inv δ).left δ.left, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left, pull_id,
      ← pull_comp v.left u.left, ← Over.comp_left, hv, Over.id_left, pull_id]
  have eA := (canc _).symm.trans ((congrArg (fun c => CechPic.pull v.left (CechPic.pull (inv δ).left c)) e).trans (canc _))
  exact (cls_eq_iff (LB.isLB_linComb A₂.isLB _ _) (LB.isLB_linComb A₁.isLB _ _)).1
    ((cls_cubeLB A₂.A _ A₂.isLB).trans (eA.trans (cls_cubeLB A₁.A _ A₁.isLB).symm))

end GlobalTheory.Mum.Two
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommute
section
set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.FormMul

theorem leibniz_of_comm : ∀ (n : ℕ) (F G : V n → Alt n) (v : V n) (F' : Alt n),
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
    ((∀ a, dz a * F v = F' * dz a) → delAt (fun x => F x * G x) v = delAt F v * G v + F' * delAt G v) ∧
    ((∀ a, dzb a * F v = F' * dzb a) → dbarAt (fun x => F x * G x) v = dbarAt F v * G v + F' * dbarAt G v) := by
  intro n F G v F' hF hG
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold delAt
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_mul (T := fun f => del f v (coordVec a))
      (fun f hf => by rw [del_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
      (fun f g hf hg => del_mul hf hg _) (fun c => by rw [del_const]; rfl) hF hG]
    simp only [mul_add, ← mul_assoc, h]
  · unfold dbarAt
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_mul (T := fun f => dbar f v (coordVec a))
      (fun f hf => by rw [dbar_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
      (fun f g hf hg => dbar_mul hf hg _) (fun c => by rw [dbar_const]; rfl) hF hG]
    simp only [mul_add, ← mul_assoc, h]

end GlobalTheory.CxForm.FormMul
end
end

