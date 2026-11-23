module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFreeness
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

universe u v w

namespace GenericFreeness

theorem isGenericallyFree_of_primes {A : Type u} [CommRing A] [IsDomain A] {R : Type u} [CommRing R]
    [IsNoetherianRing R] [Algebra A R] (hq : ∀ p : PrimeSpectrum R, IsGenericallyFree A (R ⧸ p.asIdeal))
    (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] [Module.Finite R M] :
    IsGenericallyFree A M := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R (M := M) inferInstance
    (motive := fun N _ _ _ ↦ ∀ (_ : Module A N) (_ : IsScalarTower A R N), IsGenericallyFree A N)
    ?_ ?_ ?_ ‹Module A M› ‹IsScalarTower A R M›
  · intro N _ _ _ _ _ _
    exact ⟨1, one_ne_zero, inferInstance⟩
  · intro N _ _ _ p e _ _
    exact (hq p).of_linearEquiv (e.restrictScalars A).symm
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ _ _
    letI : Module A N₁ := Module.compHom N₁ (algebraMap A R)
    letI : Module A N₃ := Module.compHom N₃ (algebraMap A R)
    have t₁ : IsScalarTower A R N₁ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    have t₃ : IsScalarTower A R N₃ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    exact IsGenericallyFree.of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg
      (h₁ inferInstance t₁) (h₃ inferInstance t₃)

theorem isGenericallyFree_of_comap_ne_bot {A : Type u} [CommRing A] {σ : Type*} (q : Ideal (MvPolynomial σ A))
    (h : q.comap (C : A →+* MvPolynomial σ A) ≠ ⊥) : IsGenericallyFree A (MvPolynomial σ A ⧸ q) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine isGenericallyFree_of_smul_eq_zero a ha0 fun d ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have e : a • Ideal.Quotient.mk q x = Ideal.Quotient.mk q (a • x) :=
    (map_smul (Ideal.Quotient.mkₐ A q) a x).symm
  rw [e, Ideal.Quotient.eq_zero_iff_mem, smul_eq_C_mul]
  exact q.mul_mem_right x ha

theorem isGenericallyFree_quotient_bot {A : Type u} [CommRing A] [IsDomain A] (σ : Type*) :
    IsGenericallyFree A (MvPolynomial σ A ⧸ (⊥ : Ideal (MvPolynomial σ A))) :=
  (isGenericallyFree_of_free (M := MvPolynomial σ A)).of_linearEquiv
    (AlgEquiv.quotientBot A (MvPolynomial σ A)).toLinearEquiv.symm

theorem isGenericallyFree_quotient (hNN : GenericNoetherNormalisation.Statement.{u}) (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (q : Ideal (MvPolynomial (Fin n) A)),
      q.IsPrime → IsGenericallyFree A (MvPolynomial (Fin n) A ⧸ q) := by
  set_option synthInstance.maxHeartbeats 400000 in
  induction n with
  | zero =>
    intro A _ _ _ q _
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin 0) A) = ⊥
    · have hq : q = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : C (AddMonoidAlgebra.coeff x 0) ∈ q := by rwa [← eq_C_of_isEmpty x]
        have : AddMonoidAlgebra.coeff x 0 ∈ q.comap (C : A →+* MvPolynomial (Fin 0) A) := hx'
        rw [hc, Ideal.mem_bot] at this
        rw [Ideal.mem_bot, eq_C_of_isEmpty x, this, map_zero]
      subst hq
      exact isGenericallyFree_quotient_bot _
    · exact isGenericallyFree_of_comap_ne_bot q hc
  | succ n ih =>
    intro A _ _ _ q hqp
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥
    · by_cases hq : q = ⊥
      · subst hq
        exact isGenericallyFree_quotient_bot _
      obtain ⟨a, ha, z, s, hspan⟩ := hNN A n q hqp hq hc
      let D := MvPolynomial (Fin (n + 1)) A ⧸ q
      let Rn := MvPolynomial (Fin n) A
      letI : Algebra Rn D := (aeval z : Rn →ₐ[A] D).toRingHom.toAlgebra
      have : IsScalarTower A Rn D := IsScalarTower.of_algebraMap_eq (R := A) (S := Rn) (A := D)
        fun x ↦ ((aeval z : Rn →ₐ[A] D).commutes x).symm
      let N : Submodule Rn D := Submodule.span Rn (s : Set D)
      have hN : IsGenericallyFree A N :=
        isGenericallyFree_of_primes (R := Rn) (fun p ↦ ih A p.asIdeal p.isPrime) N
      refine hN.of_injective (N.subtype.restrictScalars A) Subtype.val_injective a ha fun d ↦ ?_
      obtain ⟨k, c, hk⟩ := hspan d
      refine ⟨k, ⟨⟨a ^ k • d, ?_⟩, rfl⟩⟩
      rw [hk]
      exact Submodule.sum_mem _ fun t ht ↦ Submodule.smul_mem _ (c t) (Submodule.subset_span ht)
    · exact isGenericallyFree_of_comap_ne_bot q hc

end GenericFreeness

theorem GenericFreeness.proof (hNN : GenericNoetherNormalisation.Statement.{u}) :
    GenericFreeness.Statement.{u, v, w} := by
  intro A _ _ _ B _ _ _ M _ _ _ _ _
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›
  letI : Algebra (MvPolynomial (Fin n) A) B := g.toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin n) A) M := Module.compHom M (algebraMap (MvPolynomial (Fin n) A) B)
  have : IsScalarTower (MvPolynomial (Fin n) A) B M := ⟨fun x b m ↦ by
    show (g x * b) • m = g x • b • m
    rw [mul_smul]⟩
  have : IsScalarTower A (MvPolynomial (Fin n) A) M := ⟨fun a x m ↦ by
    show g (a • x) • m = a • g x • m
    rw [map_smul, smul_assoc]⟩
  have : Module.Finite (MvPolynomial (Fin n) A) B := RingHom.Finite.of_surjective g.toRingHom hg
  have : Module.Finite (MvPolynomial (Fin n) A) M := Module.Finite.trans B M
  exact GenericFreeness.isGenericallyFree_of_primes (R := MvPolynomial (Fin n) A)
    (fun p ↦ GenericFreeness.isGenericallyFree_quotient hNN n A p.asIdeal p.isPrime) M

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericPrimitive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

open MvPolynomial

def linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) : MvPolynomial (Fin n) k :=
  ∑ j, C (φ (Pi.single j 1)) * X j

theorem eval_linearFormPoly {k : Type*} [Field k] {n : ℕ} (φ : (Fin n → k) →ₗ[k] k) (c : Fin n → k) :
    eval c (linearFormPoly φ) = φ c := by
  have hc : c = ∑ j, c j • (Pi.single j 1 : Fin n → k) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linearFormPoly, map_sum, mul_comm]

theorem GenericPrimitive.proof : GenericPrimitive.Statement := by
  intro k K L _ _ _ _ _ _ _ _ _ n x hx
  have hfin : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L (Field.exists_primitive_element K L)
  have := Fintype.ofFinite (IntermediateField K L)
  classical

  let f : (Fin n → k) →ₗ[k] L := Fintype.linearCombination k x
  have hf : ∀ c, f c = ∑ j, c j • x j := fun c => Fintype.linearCombination_apply k x c

  let W : IntermediateField K L → Submodule k (Fin n → k) := fun M =>
    (M.toSubalgebra.toSubmodule.restrictScalars k).comap f
  have hW : ∀ M : IntermediateField K L, M ≠ ⊤ → W M < ⊤ := by
    intro M hM
    refine lt_top_iff_ne_top.2 fun htop => hM ?_
    have hxM : Set.range x ⊆ M := by
      rintro _ ⟨j, rfl⟩
      have hj : (Pi.single j 1 : Fin n → k) ∈ W M := htop ▸ Submodule.mem_top
      have : f (Pi.single j 1) = x j := by
        rw [hf]; simp [Pi.single_apply]
      simpa [W, this] using hj
    exact eq_top_iff.2 (hx ▸ IntermediateField.adjoin_le_iff.2 hxM)
  have hφ : ∀ M : IntermediateField K L, ∃ φ : (Fin n → k) →ₗ[k] k,
      M ≠ ⊤ → φ ≠ 0 ∧ W M ≤ LinearMap.ker φ := by
    intro M
    by_cases hM : M = ⊤
    · exact ⟨0, fun h => (h hM).elim⟩
    · obtain ⟨φ, h0, hle⟩ := (W M).exists_le_ker_of_lt_top (hW M hM)
      exact ⟨φ, fun _ => ⟨h0, hle⟩⟩
  choose φ hφ using hφ
  let S : Finset (IntermediateField K L) := Finset.univ.filter (· ≠ ⊤)
  refine ⟨∏ M ∈ S, linearFormPoly (φ M), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro M hM
    have hM' : M ≠ ⊤ := (Finset.mem_filter.1 hM).2
    obtain ⟨c, hc⟩ : ∃ c, φ M c ≠ 0 := by
      by_contra h
      exact (hφ M hM').1 (LinearMap.ext fun c => by simpa using not_not.1 (not_exists.1 h c))
    intro h0
    apply hc
    rw [← eval_linearFormPoly, h0, map_zero]
  · intro c hc
    by_contra hne
    rw [map_prod, Finset.prod_ne_zero_iff] at hc
    have hmem : IntermediateField.adjoin K {∑ j, c j • x j} ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
    apply hc _ hmem
    rw [eval_linearFormPoly]
    apply (hφ _ hne).2
    show f c ∈ IntermediateField.adjoin K {∑ j, c j • x j}
    rw [hf]
    exact IntermediateField.mem_adjoin_simple_self K _

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGraphJacContinuous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open scoped InnerProductSpace

theorem det_one_add_adjoint_comp_self_pos {k m : ℕ}
    (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
      LinearMap.adjoint B ∘ₗ B) := by
  set S : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) := 1 + LinearMap.adjoint B ∘ₗ B
    with hSdef
  have hBB : (LinearMap.adjoint B ∘ₗ B).IsPositive := LinearMap.isPositive_adjoint_comp_self B
  have hS : S.IsPositive := LinearMap.isPositive_one.add hBB
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  rw [hS.isSymmetric.det_eq_prod_eigenvalues hn]
  refine Finset.prod_pos fun i _ => ?_
  set v := hS.isSymmetric.eigenvectorBasis hn i
  have hv : ‖v‖ = 1 := (hS.isSymmetric.eigenvectorBasis hn).orthonormal.1 i
  have h1 : ⟪S v, v⟫_ℝ = hS.isSymmetric.eigenvalues hn i := by
    rw [hS.isSymmetric.apply_eigenvectorBasis hn i]
    simp [real_inner_smul_left, hv, v]
  have h2 : ⟪S v, v⟫_ℝ = ‖v‖ ^ 2 + ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    rw [hSdef, LinearMap.add_apply, inner_add_left, Module.End.one_apply, real_inner_self_eq_norm_sq]
  have h3 : 0 ≤ ⟪(LinearMap.adjoint B ∘ₗ B) v, v⟫_ℝ := by
    simpa using hBB.re_inner_nonneg_left v
  have : 0 < (hS.isSymmetric.eigenvalues hn i : ℝ) := by
    rw [← h1, h2, hv]; linarith
  simpa using this

theorem graphJac_pos {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < graphJac B :=
  Real.sqrt_pos.mpr (det_one_add_adjoint_comp_self_pos B)

theorem continuous_graphJac (k m : ℕ) :
    Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  have hc : Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      (1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
    continuous_const.add ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)
  have heq : (fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) =
      fun B => √((1 + (ContinuousLinearMap.adjoint B).comp B :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)).det) := by
    funext B
    rfl
  rw [heq]
  exact (ContinuousLinearMap.continuous_det.comp hc).sqrt

theorem GraphJacContinuous.proof : GraphJacContinuous.Statement := by
  intro k m A ε hε
  set g := fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
    graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) with hg
  have hgA : 0 < g A := graphJac_pos _
  set η := ε * g A / (1 + ε) with hη
  have hη0 : 0 < η := by positivity
  have hηe : (1 + ε) * η = ε * g A := by rw [hη]; field_simp
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuous_iff.mp (continuous_graphJac k m) A η hη0
  refine ⟨δ / 2, half_pos hδ, fun B hB => ?_⟩
  have hd : dist B A < δ := by rw [dist_eq_norm]; linarith
  have h := hδη B hd
  rw [Real.dist_eq, abs_lt] at h
  change g B ≤ (1 + ε) * g A ∧ g A ≤ (1 + ε) * g B
  constructor
  · nlinarith
  · nlinarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGridProductLowerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology MvPolynomial

theorem GridProductLowerBound.exists_grid_prod_ne_zero {σ : Type} [Fintype σ] {N k : ℕ} (hk : k ≤ N)
    (v : Fin k → σ → ℂ) (hv : ∀ m, v m ≠ 0) :
    ∃ u : σ → Fin (N + 1), ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i ≠ 0 := by
  classical
  set P : MvPolynomial σ ℂ := ∏ m, ∑ i, X i * C (v m i) with hP
  have hlin : ∀ m, ∑ i, X i * C (v m i) ≠ (0 : MvPolynomial σ ℂ) := by
    intro m h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (hv m)
    have := congrArg (eval (Pi.single i 1)) h
    simp [Pi.single_apply] at this
    exact hi this
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun m _ => hlin m
  let S : σ → Finset ℂ := fun _ => Finset.univ.image fun j : Fin (N + 1) => ((j : ℕ) : ℂ)
  have hS : ∀ i, (S i).card = N + 1 := fun i => by
    simp only [S]
    rw [Finset.card_image_of_injective _ fun a b h => Fin.ext (by exact_mod_cast h)]
    simp
  have htot : P.totalDegree ≤ k := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ m, (∑ i, X i * C (v m i) : MvPolynomial σ ℂ).totalDegree ≤ ∑ _m : Fin k, 1 :=
          Finset.sum_le_sum fun m _ => totalDegree_finsetSum_le fun j _ =>
            (totalDegree_mul _ _).trans (by simp [totalDegree_X, totalDegree_C])
      _ = k := by simp
  have hdeg : ∀ i, P.degreeOf i < (S i).card := fun i => by
    rw [hS i]
    exact Nat.lt_succ_of_le (((degreeOf_le_totalDegree _ _).trans htot).trans hk)
  by_contra hne
  push Not at hne
  refine hP0 (eq_zero_of_eval_zero_at_prod_finset P S hdeg fun x hx => ?_)
  choose u _ hu using fun i => Finset.mem_image.1 (hx i)
  have := hne u
  simp only [hu] at this
  simpa [hP, map_prod] using this

theorem GridProductLowerBound.proof : GridProductLowerBound.Statement := by
  classical
  intro σ _ N Z z₀ hZ hz₀
  obtain ⟨ε, hε, hεZ⟩ : ∃ ε > 0, ∀ x ∈ Z, ε ≤ dist z₀ x := by
    rw [Metric.mem_closure_iff] at hz₀
    push Not at hz₀
    exact hz₀
  obtain ⟨R, hR⟩ := hZ.subset_closedBall z₀
  set K : Set (σ → ℂ) := Metric.closedBall 0 (R + ε / 2) \ Metric.ball 0 (ε / 2) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hK0 : ∀ w ∈ K, w ≠ 0 := by
    rintro w hw rfl
    simp [hK, hε] at hw
  let g : (k : ℕ) → (Fin k → σ → ℂ) → ℝ := fun k v =>
    Finset.univ.sup' Finset.univ_nonempty fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖
  have hbd : ∀ k, ∃ μ > (0 : ℝ), k ≤ N → ∀ v ∈ Set.univ.pi (fun _ : Fin k => K), μ ≤ g k v := by
    intro k
    by_cases hk : k ≤ N
    · rcases (Set.univ.pi fun _ : Fin k => K).eq_empty_or_nonempty with he | hne
      · exact ⟨1, one_pos, fun _ v hv => by simp [he] at hv⟩
      have hgc : Continuous (g k) := Continuous.finset_sup'_apply
        (f := fun (u : σ → Fin (N + 1)) (v : Fin k → σ → ℂ) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖) _
        fun u _ => continuous_norm.comp (continuous_finsetProd _ fun m _ => continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((continuous_apply i).comp (continuous_apply m)))
      obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_univ_pi fun _ => hKc).exists_isMinOn hne hgc.continuousOn
      obtain ⟨u, hu⟩ := GridProductLowerBound.exists_grid_prod_ne_zero hk v₀
        fun m => hK0 _ (hv₀ m (Set.mem_univ _))
      exact ⟨g k v₀, (norm_pos_iff.2 hu).trans_le (Finset.le_sup' (fun u : σ → Fin (N + 1) =>
        ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v₀ m i‖) (Finset.mem_univ u)), fun _ v hv => isMinOn_iff.1 hmin v hv⟩
    · exact ⟨1, one_pos, fun h => absurd h hk⟩
  choose μf hμf0 hμf using hbd
  refine ⟨(Finset.range (N + 1)).inf' ⟨0, Finset.mem_range.2 N.succ_pos⟩ μf,
    (Finset.lt_inf'_iff _).2 fun k _ => hμf0 k, Metric.ball z₀ (ε / 2), Metric.ball_mem_nhds _ (by positivity), ?_⟩
  intro z hz s hs hcard
  set e := s.equivFin
  set v : Fin s.card → σ → ℂ := fun m => z - (e.symm m : σ → ℂ) with hvdef
  have hv : v ∈ Set.univ.pi fun _ : Fin s.card => K := by
    intro m _
    have hx := hs (e.symm m).2
    have h1 := hεZ _ hx
    have h2 := Metric.mem_closedBall.1 (hR hx)
    have h3 := Metric.mem_ball.1 hz
    have h4 := dist_triangle z₀ z (e.symm m : σ → ℂ)
    have h5 := dist_triangle z z₀ (e.symm m : σ → ℂ)
    rw [dist_comm z₀ z] at h4
    rw [dist_comm] at h2
    simp only [hK, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, hvdef, ← dist_eq_norm,
      not_lt]
    constructor <;> linarith
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖)
  refine ⟨u, ?_⟩
  have hprod : ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) = ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i := by
    rw [← Finset.prod_coe_sort, ← e.symm.prod_comp]
    rfl
  rw [hprod]
  have hle := (Finset.inf'_le μf (Finset.mem_range_succ_iff.2 hcard)).trans (hμf _ hcard v hv)
  simp only [g] at hle
  rwa [hu] at hle

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicIsolatedFibreOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

theorem HolomorphicIsolatedFibreOpen.proof (hPS : ProperHolomorphicSurjective.Statement) :
    HolomorphicIsolatedFibreOpen.Statement := by
  intro k U g u hU hu hg ⟨W, hW, hiso⟩ V hV
  obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall u r ⊆ U ∩ W ∩ V :=
    nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hu) hW) hV)
  have hgc : ContinuousOn g (closedBall u r) := hg.continuousOn.mono fun x hx => (hrsub hx).1.1

  have hSc : IsCompact (g '' sphere u r) :=
    (isCompact_sphere u r).image_of_continuousOn (hgc.mono sphere_subset_closedBall)
  have hnot : g u ∉ g '' sphere u r := by
    rintro ⟨s, hs, hgs⟩
    have hsK := hrsub (sphere_subset_closedBall hs)
    have := hiso s hsK.1.2 hsK.1.1 hgs
    subst this
    rw [mem_sphere, dist_self] at hs
    exact hr.ne' hs.symm
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hSc.isClosed.isOpen_compl (g u) hnot

  have key : ∀ v ∈ closedBall u r, g v ∈ ball (g u) ε → v ∈ ball u r := by
    intro v hv hgv
    rcases (mem_closedBall.1 hv).lt_or_eq with h | h
    · exact h
    · exact (hεsub hgv ⟨v, mem_sphere.2 h, rfl⟩).elim
  have hΩ : IsOpen (ball u r ∩ g ⁻¹' ball (g u) ε) :=
    (hgc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_ball
  have hproper : ∀ L ⊆ ball (g u) ε, IsCompact L →
      IsCompact ((ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L) := by
    intro L hLD hL
    have heq : (ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L = closedBall u r ∩ g ⁻¹' L := by
      ext v
      constructor
      · rintro ⟨⟨hv, _⟩, hvL⟩
        exact ⟨ball_subset_closedBall hv, hvL⟩
      · rintro ⟨hv, hvL⟩
        exact ⟨⟨key v hv (hLD hvL), hLD hvL⟩, hvL⟩
    rw [heq]
    exact (isCompact_closedBall u r).of_isClosed_subset
      (hgc.preimage_isClosed_of_isClosed isClosed_closedBall hL.isClosed) Set.inter_subset_left
  have hsurj := hPS k _ _ g hΩ ⟨u, by exact Set.mem_preimage.mpr (mem_ball_self hr), by exact Set.mem_preimage.mpr (mem_ball_self hε)⟩ isOpen_ball
    (convex_ball _ _).isPreconnected (hg.mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).1.1)
    (fun x hx => hx.2) hproper
  refine Filter.mem_of_superset (ball_mem_nhds _ hε) ?_
  rw [← hsurj]
  exact Set.image_mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace InjectiveHolomorphicOpen

theorem finrank_eq (k : ℕ) :
    Module.finrank ℝ (Fin k → ℂ) = Module.finrank ℝ (Fin (2 * k) → ℝ) := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

theorem proof (hID : InvarianceOfDomain.Statement) : InjectiveHolomorphicOpen.Statement := by
  intro k U f hU hf hinj
  let e : (Fin k → ℂ) ≃L[ℝ] (Fin (2 * k) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (finrank_eq k)
  have hU' : IsOpen (e '' U) := e.toHomeomorph.isOpenMap U hU
  have hcont : ContinuousOn (fun y => e (f (e.symm y))) (e '' U) := by
    refine e.continuous.comp_continuousOn (hf.continuousOn.comp e.symm.continuous.continuousOn ?_)
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hinj' : Set.InjOn (fun y => e (f (e.symm y))) (e '' U) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h
    rw [hinj hx hx' (e.injective h)]
  have himage : (fun y => e (f (e.symm y))) '' (e '' U) = e '' (f '' U) := by
    rw [Set.image_image, Set.image_image]
    simp
  have hopen := hID (2 * k) (e '' U) (fun y => e (f (e.symm y))) hU' hcont hinj'
  rw [himage] at hopen
  have hpre : e ⁻¹' (e '' (f '' U)) = f '' U := Set.preimage_image_eq _ e.injective
  rw [← hpre]
  exact hopen.preimage e.continuous

end InjectiveHolomorphicOpen

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

