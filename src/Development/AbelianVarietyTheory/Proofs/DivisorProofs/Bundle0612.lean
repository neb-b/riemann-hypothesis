module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0583

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqNearFibreOfQuotContracts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem eq_near_fibre_of_quot_contracts : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ t : S, (∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t) → ∃ V : S.Opens, t ∈ V ∧ (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left := by
  intro S A B _ _ _ _ u v hA hB hu hv t ht
  have := hA.proper
  have hε : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  obtain ⟨V, htV, hV⟩ := GlobalTheory.local_rigidity A.left S B.left A.hom (η[A] : 𝟙_ (Over S) ⟶ A).left
    (u * v⁻¹).left hε inferInstance
    (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns A hA) t _ ht
  refine ⟨V, htV, ?_⟩
  have h1 : (η[A] : 𝟙_ (Over S) ⟶ A) ≫ (u * v⁻¹) = η[B] := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel, Hom.one_def,
      toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let i : Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ⟶ A := Over.homMk (A.hom ⁻¹ᵁ V).ι rfl
  have h2 : i ≫ (u * v⁻¹) = 1 := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Hom.one_def, Over.comp_left]
    change (A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left = _
    rw [hV, ← Over.comp_left, h1]
    have e : (toUnit (Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom))).left = (A.hom ⁻¹ᵁ V).ι ≫ A.hom :=
      by simpa using Over.w (toUnit (Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom)))
    rw [e, Category.assoc]
  have h3 : i ≫ u = i ≫ v := by
    have := congrArg (· * (i ≫ v)) h2
    simpa [MonObj.comp_mul, GrpObj.comp_inv] using this
  exact congrArg (·.left) h3

end GlobalTheory.EndLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory

theorem etale_isFinite_of_comp_etale_surjective :
    ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) →
      IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → Etale f ∧ IsFinite f := by
  intro X Y Z h f h1 h2 h3 h4 h5 h6
  have : LocallyOfFinitePresentation f := GlobalTheory.T.locally_finite_presentation_of_etale_cover X Y Z h f h1 h2 h3 h4 h5 h6
  exact ⟨etale_of_comp_of_etale_of_surjective h f, isFinite_of_comp_surjective h f⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvResCounitCompat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.EvRes

theorem comp_eval_eq {σ O A A' : Type} [Fintype σ] [CommRing O] [CommRing A] [CommRing A']
    [Algebra O A] [Algebra O A'] (p : ℕ) [IsHausdorff (Ideal.span {(p : A')}) A']
    (g : A →ₐ[O] A') (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A) (hE : IsEval p x E)
    (ψ : MvPowerSeries σ O →+* A') (hC : ∀ c, ψ (C c) = algebraMap O A' c)
    (hX : ∀ i, ψ (X i) = g (x i))
    (hψ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A') ^ m ∣ ψ f)
    (f : MvPowerSeries σ O) : g (E f) = ψ f :=
  CEval.ext_of_cont p ((g : A →+* A').comp (E : MvPowerSeries σ O →+* A)) ψ
    (fun c => by
      show g (E (C c)) = ψ (C c)
      rw [hC, c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes])
    (fun i => by
      show g (E (X i)) = ψ (X i)
      rw [hX, hE.1])
    (fun m => by
      obtain ⟨N, hN⟩ := hE.2 m
      exact ⟨N, fun f hf => by
        show (p : A') ^ m ∣ g (E f)
        have := map_dvd g (hN f hf)
        rwa [map_pow, map_natCast] at this⟩)
    hψ f

theorem constantCoeff_cont {σ O : Type} [CommRing O] (p : ℕ) :
    ∀ m : ℕ, ∃ N : ℕ, ∀ f : MvPowerSeries σ O, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : O) ^ m ∣ constantCoeff f := fun _ =>
  ⟨1, fun f hf => by
    rw [← coeff_zero_eq_constantCoeff_apply, hf 0 (by simp)]
    exact dvd_zero _⟩

end GlobalTheory.EvRes


open GlobalTheory.EvRes in
theorem GlobalTheory.QLog.Chart.ev_res_counit : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, G.res n (c.ev (n + 1) f) = c.ev n f ∧ Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O (G.A n)) (Bialgebra.counitAlgHom O (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  intro p O _ _ G d c n
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) :=
    FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n)
  refine ⟨fun f => ⟨?_, ?_⟩, fun s => ?_⟩
  · exact comp_eval_eq p (G.res n : G.A (n + 1) →ₐ[O] G.A n) (c.x (n + 1)) (c.ev (n + 1))
      (c.isEval (n + 1)) (c.ev n : MvPowerSeries (Fin d) O →+* G.A n)
      (fun a => by rw [c_eq_algebraMap]; exact (c.ev n).commutes a)
      (fun i => by
        show c.ev n (X i) = G.res n (c.x (n + 1) i)
        rw [(c.isEval n).1, c.res])
      (c.isEval n).2 f
  · exact comp_eval_eq p (Bialgebra.counitAlgHom O (G.A n)) (c.x n) (c.ev n) (c.isEval n)
      constantCoeff (fun a => by rw [constantCoeff_C]; rfl)
      (fun i => by
        rw [constantCoeff_X]
        exact (c.aug n i).symm)
      (constantCoeff_cont p) f
  · exact comp_eval_eq p _ _ (c.ev₂ n) (c.isEval₂ n) constantCoeff
      (fun a => by rw [constantCoeff_C]; rfl)
      (fun i => by
        rw [constantCoeff_X]
        rcases i with i | i <;> simp [Bialgebra.counitAlgHom_apply, c.aug n i])
      (constantCoeff_cont p) s
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSwapEq
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CommSwap

theorem eval_swap_eq : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  intro p O A _ _ _ _ _ d x E₂ μ hnil hE hμ i
  set y : Fin d ⊕ Fin d → A ⊗[O] A := Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i with hy
  have hny : ∀ j, ∃ N : ℕ, (p : A ⊗[O] A) ∣ y j ^ N := by
    intro j
    rcases j with j | j
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, a ⊗ₜ[O] 1, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inl, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, 1 ⊗ₜ[O] a, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeRight_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inr, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
  set T := (Algebra.TensorProduct.comm O A A).toAlgHom
  set E' := T.comp E₂
  set u : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) O :=
    Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)) with hu
  have hu0 : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [hu]
  have hE' : IsEval p (fun j => E₂ (u j)) E' := by
    refine ⟨?_, ?_⟩
    · intro j
      rcases j with j | j
      · simp [E', T, hu, hE.1, hy]
      · simp [E', T, hu, hE.1, hy]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨c, hc⟩ := hN f hf
      refine ⟨T c, ?_⟩
      simp [E', hc, map_mul, map_pow, map_natCast]
  have key := ((GlobalTheory.CEval.continuous_eval p O (A ⊗[O] A) (Fin d ⊕ Fin d) y hny).2 E₂ hE).1 (Fin d ⊕ Fin d) u E' hu0 hE' (μ i)
  have hs : swap (μ i) = subst u (μ i) := rfl
  rw [hs, key, hμ i]
  simp only [E', T, AlgHom.comp_apply, hμ i]
  exact Coalgebra.comm_comul (R := O) (x i)

end GlobalTheory.CommSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointPrimeToPSimilitude
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_adjoint_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : D.La →ₗ[D.O] D.La) (c k : ℕ),
    c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) →
    c ∣ k ^ 2 → ∃ g' : D.La →ₗ[D.O] D.La, (∀ x, g (g' x) = k • x) ∧ (∀ x, g' (g x) = k • x) ∧
      (∀ x y, D.EF (g' x) (g' y) = (k ^ 2 / c) * D.EF x y) ∧ (∀ x, ∃ y, g' y = k • x) ∧
      (k ^ 2 / c).Coprime p ∧ (k ^ 2 / c) ∣ k ^ 2 ∧ c * (k ^ 2 / c) = k ^ 2 := by
  intro p _ D g c k hc hk hE himg hck
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hp1 (by simpa using hc)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hp1 (by simpa using hk)
  have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0

  have ginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply D.nondeg
    ext y
    have h := hE x y
    rw [hx, map_zero, LinearMap.zero_apply] at h
    simp only [map_zero, LinearMap.zero_apply]
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hcZ
    · exact h'
  choose f hf using himg
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y => ginj (by rw [map_add (f := _), hf, hf, hf, smul_add])
  have fsmul : ∀ (b : D.O) x, f (b • x) = b • f x := fun b x => ginj (by
    rw [map_smul, hf, hf, smul_comm])
  let g' : D.La →ₗ[D.O] D.La :=
    { toFun := f, map_add' := fadd, map_smul' := fsmul }
  have h1 : ∀ x, g (g' x) = k • x := hf
  have h2 : ∀ x, g' (g x) = k • x := fun x => ginj (by rw [h1, map_nsmul])
  obtain ⟨q, hq⟩ := hck
  have hdiv : k ^ 2 / c = q := by rw [hq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hc0)]
  refine ⟨g', h1, h2, ?_, fun x => ⟨g x, h2 x⟩, ?_, ?_, ?_⟩
  · intro x y
    have h := hE (g' x) (g' y)
    rw [h1, h1, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul] at h
    push_cast [hdiv]
    have hqZ : ((k : ℤ) ^ 2 / c) = q := by
      rw [show (k : ℤ) ^ 2 = ((k ^ 2 : ℕ) : ℤ) by push_cast; ring, hq]
      push_cast
      exact Int.mul_ediv_cancel_left _ hcZ
    have hqI : (k : ℤ) ^ 2 = c * q := by exact_mod_cast hq
    rw [hqZ]
    apply mul_left_cancel₀ hcZ
    rw [← h, nsmul_eq_mul]
    push_cast
    rw [← sq, hqI]
    ring
  · rw [hdiv]
    have : q ∣ k ^ 2 := ⟨c, by rw [hq, mul_comm]⟩
    exact Nat.Coprime.coprime_dvd_left this (Nat.Coprime.pow_left 2 hk)
  · rw [hdiv]; exact ⟨c, by rw [hq, mul_comm]⟩
  · rw [hdiv, hq]

end GlobalTheory.UPel.HT.Hecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualTangentOfCoboundaryOneEqSmulStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDual_tangent_of_coboundaryOne_eq_smul : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (b : A) (z : A ⊗[O] A), cobOne O A b = a • z → ∃ u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}, ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := by
  first | exact @GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul | exact GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul | (intros; apply GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeFiniteIntersectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_finite_intersection : ∀ (H : Scheme.{0}) (Idx : Type) [Finite Idx] (Z : Idx → Scheme.{0}) (i : ∀ k, Z k ⟶ H), (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h := by
  first | (exact @GlobalTheory.closedSubscheme_iInter_exists) | (exact GlobalTheory.closedSubscheme_iInter_exists) | (intros; apply GlobalTheory.closedSubscheme_iInter_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeIntersectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_intersection : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H), IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h := by
  first | (exact @GlobalTheory.closedSubscheme_inter_exists) | (exact GlobalTheory.closedSubscheme_inter_exists) | (intros; apply GlobalTheory.closedSubscheme_inter_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePDivGroupLevelCoordinatesStatement
section
open GlobalTheory GlobalTheory.PDivGroup
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_pDivGroup_level_coordinates : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n), (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n, Submodule.span O (Set.range fun i => PDiv.dUnit (R := O) (x n i)) = ⊤) ∧ ∀ n, ∃ l : Fin d → (PDiv.Cot O (G.A n) →ₗ[O] O ⧸ Ideal.span {(p : O) ^ n}), ∀ i j, l i (PDiv.dUnit (R := O) (x n j)) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.PDiv.exists_compatible_coordinates | exact GlobalTheory.PDiv.exists_compatible_coordinates | (intros; apply GlobalTheory.PDiv.exists_compatible_coordinates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimePowerRoots
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_prime_power_roots : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharZero k], ∃ ζ : ℕ → kˣ, (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) ∧ ∀ r, ζ (r + 1) ^ p = ζ r := by
  first | (exact @GlobalTheory.exists_compatible_primitive_prime_pow_roots) | (exact GlobalTheory.exists_compatible_primitive_prime_pow_roots) | (intros; apply GlobalTheory.exists_compatible_primitive_prime_pow_roots  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSimilitudeLevelTowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_similitude_level_tower : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 → W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p) → (∀ r, ∃ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧ ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y) → ∃ ev : ℕ → D.La → Q, (∀ r, ((∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) ∧ ∀ x y, W r (ev r x) (ev r y) = ζ r ^ D.EF x y) ∧ ∀ r x, ev (r + 1) x ^ p = ev r x := by
  first | (exact @GlobalTheory.TowerLev.exists_compatible) | (exact GlobalTheory.TowerLev.exists_compatible) | (intros; apply GlobalTheory.TowerLev.exists_compatible  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIdempotentModPrimePowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_idempotent_mod_prime_pow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℕ), ∃ ε u v : 𝓞 D.F, ε + D.bar ε = 1 + (p : 𝓞 D.F) ^ r * u ∧ ε * D.bar ε = (p : 𝓞 D.F) ^ r * v := by
  first | (exact @GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem) | (exact GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem) | (intros; apply GlobalTheory.UPel.HT.SplitIdem.exists_conj_idem  <;> assumption)
end

