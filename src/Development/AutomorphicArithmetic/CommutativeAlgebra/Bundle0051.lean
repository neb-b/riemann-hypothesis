module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointsNonemptyUnitaryGaussian
public import Development.AutomorphicArithmetic.RealSpanData.RealData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.LiftBaseChangeRealBijectiveOfLattice
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

theorem UpperTheory.liftBaseChange_real_bijective_of_lattice :
    ∀ (g : ℕ) (V La : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup La] [Module.Finite ℤ La] [Module.Free ℤ La] (j : La →+ V), Function.Injective j → Submodule.span ℚ (Set.range j) = ⊤ → ∀ P : La →+ (Fin g → ℂ), Function.Injective P → DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → ∀ Pq : V →ₗ[ℚ] (Fin g → ℂ), (∀ z, Pq (j z) = P z) → Function.Bijective (LinearMap.liftBaseChange ℝ Pq) := by
  intro g V La _ _ _ _ _ j hj hspan P hP hdisc hPspan Pq hPq
  classical
  have hsurj : Function.Surjective (LinearMap.liftBaseChange ℝ Pq) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hPspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact ⟨(1 : ℝ) ⊗ₜ j z, by simp [LinearMap.liftBaseChange_tmul, hPq]⟩
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using hPspan⟩
  have hrank : Module.finrank ℤ La = Module.finrank ℝ (Fin g → ℂ) := by
    rw [← ZLattice.rank ℝ L]
    exact LinearEquiv.finrank_eq (LinearEquiv.ofInjective P.toIntLinearMap hP)
  let b := Module.Free.chooseBasis ℤ La
  have hsub : ∀ z, j z ∈ Submodule.span ℚ (Set.range (j ∘ b)) := by
    intro z
    have htop : ((Submodule.span ℚ (Set.range (j ∘ b))).restrictScalars ℤ).comap j.toIntLinearMap = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    have : z ∈ ((Submodule.span ℚ (Set.range (j ∘ b))).restrictScalars ℤ).comap j.toIntLinearMap := by
      rw [htop]; trivial
    exact this
  have hVspan : Submodule.span ℚ (Set.range (j ∘ b)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact hsub z
  haveI : Module.Finite ℚ V := ⟨⟨Finset.univ.image (j ∘ b), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hVspan⟩⟩
  have hV : Module.finrank ℚ V ≤ Module.finrank ℤ La := by
    rw [Module.finrank_eq_card_chooseBasisIndex ℤ La, ← finrank_top, ← hVspan]
    exact finrank_range_le_card (b := j ∘ b)
  have hdim : Module.finrank ℝ (ℝ ⊗[ℚ] V) = Module.finrank ℝ (Fin g → ℂ) := by
    refine le_antisymm ?_ ?_
    · rw [Module.finrank_baseChange]; omega
    · calc Module.finrank ℝ (Fin g → ℂ)
          = Module.finrank ℝ (⊤ : Submodule ℝ (Fin g → ℂ)) := (finrank_top ℝ _).symm
        _ = Module.finrank ℝ (LinearMap.range (LinearMap.liftBaseChange ℝ Pq)) := by
          rw [LinearMap.range_eq_top.mpr hsurj]
        _ ≤ _ := LinearMap.finrank_range_le _
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TraceActionEqSumPlaces
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private def psiE {p : ℕ} [Fact p.Prime] (G : HTGroup p) (σ : G.F →+* ℂ) : G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ :=
  if (InfinitePlace.mk σ).embedding = σ then G.psi (InfinitePlace.mk σ)
  else ((starRingEnd ℂ).mapMatrix).comp (G.psi (InfinitePlace.mk σ))

private theorem psiE_F {p : ℕ} [Fact p.Prime] (G : HTGroup p) (σ : G.F →+* ℂ) (x : G.F) :
    psiE G σ (algebraMap G.F G.C x) = Matrix.scalar (Fin G.n) (σ x) := by
  unfold psiE
  split_ifs with h
  · rw [G.psi_F, h]
  · have h2 : (InfinitePlace.mk σ).embedding = ComplexEmbedding.conjugate σ :=
      (InfinitePlace.embedding_mk_eq σ).resolve_left h
    rw [RingHom.comp_apply, G.psi_F, h2]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, ComplexEmbedding.conjugate_coe_eq]

private theorem sum_psiE {p : ℕ} [Fact p.Prime] (G : HTGroup p) (c : G.C) :
    ∑ σ : G.F →+* ℂ, Matrix.trace (psiE G σ c) =
      ∑ v : InfinitePlace G.F, ((2 * (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : G.F →+* ℂ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hne : ComplexEmbedding.conjugate v.embedding ≠ v.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex v)) h
  have hf : (Finset.univ.filter fun σ : G.F →+* ℂ => InfinitePlace.mk σ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq σ with h | h
      · exact Or.inl h.symm
      · refine Or.inr ?_
        rw [h]
        exact (star_star σ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne.symm]
  have h1 : psiE G v.embedding = G.psi v := by
    unfold psiE
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  have h2 : psiE G (ComplexEmbedding.conjugate v.embedding) = ((starRingEnd ℂ).mapMatrix).comp (G.psi v) := by
    unfold psiE
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne.symm]
  rw [h1, h2, RingHom.comp_apply]
  have h3 : Matrix.trace (((starRingEnd ℂ).mapMatrix) (G.psi v c)) = (starRingEnd ℂ) (Matrix.trace (G.psi v c)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, map_sum]
  rw [h3, Complex.add_conj]

private theorem trace_rep {p : ℕ} [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (c : G.C) :
    ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) =
      2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psi v c)).re := by
  have h3 : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    (AlgEquiv.ofRingEquiv (f := L.e) (fun r => by simp)).toLinearEquiv.finrank_eq.symm
  have h4 : Module.finrank ℚ (VQ D) = D.m * G.n * Module.finrank ℚ G.F := by
    haveI := D.freeLa
    rw [h3, L.n_eq, ← D.rankLa]
    exact Module.finrank_baseChange
  haveI : FiniteDimensional ℚ (VQ D) := by
    haveI := D.finLa
    infer_instance
  have hq := GlobalTheory.QTrace.q_trace (F := G.F) (A := G.C) (V := VQ D) G.n G.rankC L.rep.toRingHom (psiE G) (psiE_F G) c
  rw [sum_psiE, h4] at hq
  have hn : (G.n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 G.n_pos.ne'
  have hd : ((Module.finrank ℚ G.F : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  push_cast at hq
  have hq' : ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℂ) =
      (D.m : ℂ) * ∑ v : InfinitePlace G.F, ((2 * (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
    have : (G.n : ℂ) * (Module.finrank ℚ G.F : ℂ) ≠ 0 := mul_ne_zero hn hd
    apply mul_left_cancel₀ this
    push_cast
    linear_combination hq
  have : (((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) : ℂ) =
      ((2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
    push_cast at hq' ⊢
    rw [hq', Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  exact_mod_cast this

theorem UpperTheory.trace_action_eq_sum_places :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : ℝ ⊗[ℚ] G.C), LinearMap.trace ℝ (ℝ ⊗[ℚ] VQ D) (actOn L.rep ℝ x) = 2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psiR v x)).re := by
  intro p _ D G L x
  haveI : FiniteDimensional ℚ (VQ D) := by
    haveI := D.finLa
    infer_instance
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), Matrix.trace_add, Complex.add_re, Finset.sum_add_distrib, hx, hy, mul_add]
  | tmul r c =>
    have h1 : actOn L.rep ℝ (r ⊗ₜ[ℚ] c) = r • (L.rep c).baseChange ℝ := by
      rw [Algebra.smul_def]
      exact Algebra.TensorProduct.lift_tmul _ _ _ r c
    rw [h1, map_smul, LinearMap.trace_baseChange, smul_eq_mul]
    have h2 : (algebraMap ℚ ℝ) (LinearMap.trace ℚ (VQ D) (L.rep c)) = ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) := rfl
    rw [h2, trace_rep]
    simp only [HTGroup.psiR_tmul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ← Finset.mul_sum]
    ring
end
end

