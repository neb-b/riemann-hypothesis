module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsBaseChangeAwayOfIntertwine
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

section

variable {R₀ R A₀ A : Type} [CommRing R₀] [CommRing R] [CommRing A₀] [CommRing A] [Algebra R₀ R]
  [Algebra R₀ A₀] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  {N₀ N : Type} [AddCommGroup N₀] [Module R₀ N₀] [Module A₀ N₀] [IsScalarTower R₀ A₀ N₀]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Module R₀ N]
  [IsScalarTower R₀ R N] [IsScalarTower R₀ A N]

theorem exists_awayFrac_common {f : A₀} (z w : LocalizedModule.Away f N₀) :
    ∃ k m m', awayFrac N₀ f k m = z ∧ awayFrac N₀ f k m' = w := by
  obtain ⟨k, m, rfl⟩ := exists_awayFrac z
  obtain ⟨j, m', rfl⟩ := exists_awayFrac w
  exact ⟨k + j, f ^ j • m, f ^ k • m', awayFrac_add_pow_smul _ _ _ _,
    by rw [add_comm, awayFrac_add_pow_smul]⟩


omit [Algebra R A] [IsScalarTower R₀ R A] [Module R N] [IsScalarTower R A N]
  [IsScalarTower R₀ R N] in
theorem exists_away_map_of_intertwine (ψ : N₀ →ₗ[R₀] N) (x₀ : A₀) (x : A)
    (h : ∀ (k : ℕ) y, ψ (x₀ ^ k • y) = x ^ k • ψ y) :
    ∃ θ : LocalizedModule.Away x₀ N₀ →ₗ[R₀] LocalizedModule.Away x N,
      ∀ (k : ℕ) y, θ (awayFrac N₀ x₀ k y) = awayFrac N x k (ψ y) := by
  choose d n hdn using fun z : LocalizedModule.Away x₀ N₀ => exists_awayFrac z
  have key (k : ℕ) (y : N₀) :
      awayFrac N x (d (awayFrac N₀ x₀ k y)) (ψ (n (awayFrac N₀ x₀ k y))) =
        awayFrac N x k (ψ y) := by
    obtain ⟨l, hl⟩ := awayFrac_eq_iff.1 (hdn (awayFrac N₀ x₀ k y))
    exact awayFrac_eq_iff.2 ⟨l, by rw [← h, ← h, hl]⟩
  refine ⟨⟨⟨fun z => awayFrac N x (d z) (ψ (n z)), fun z w => ?_⟩, fun r z => ?_⟩, key⟩
  · obtain ⟨k, m, m', rfl, rfl⟩ := exists_awayFrac_common z w
    rw [← map_add (f := _), key, key, key, map_add (f := _), map_add (f := _)]
  · obtain ⟨k, m, rfl⟩ := exists_awayFrac z
    simp only [RingHom.id_apply]
    rw [← LinearMap.map_smul_of_tower, key, key, map_smul, LinearMap.map_smul_of_tower]

theorem isBaseChange_away_of_intertwine (ψ : N₀ →ₗ[R₀] N) (hψ : IsBaseChange R ψ) (x₀ : A₀)
    (x : A) (h : ∀ (k : ℕ) y, ψ (x₀ ^ k • y) = x ^ k • ψ y)
    (θ : LocalizedModule.Away x₀ N₀ →ₗ[R₀] LocalizedModule.Away x N)
    (hθ : ∀ (k : ℕ) y, θ (awayFrac N₀ x₀ k y) = awayFrac N x k (ψ y)) : IsBaseChange R θ := by
  let F (k : ℕ) : R ⊗[R₀] N₀ →ₗ[R] R ⊗[R₀] LocalizedModule.Away x₀ N₀ :=
    ((awayFrac N₀ x₀ k).restrictScalars R₀).baseChange R
  let P (k : ℕ) : R ⊗[R₀] N₀ →ₗ[R] R ⊗[R₀] N₀ :=
    ((LinearMap.lsmul A₀ N₀ (x₀ ^ k)).restrictScalars R₀).baseChange R
  have hFP (k l : ℕ) (t : R ⊗[R₀] N₀) : F (k + l) (P l t) = F k t := by
    induction t with
    | tmul r y => exact congrArg (r ⊗ₜ[R₀] ·) (awayFrac_add_pow_smul x₀ k l y)
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hP (l : ℕ) (t : R ⊗[R₀] N₀) : hψ.equiv (P l t) = x ^ l • hψ.equiv t := by
    induction t with
    | tmul r y => simp [P, IsBaseChange.equiv_tmul, h, smul_comm r]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, smul_add]
  have hF (k : ℕ) (t : R ⊗[R₀] N₀) :
      θ.liftBaseChange R (F k t) = awayFrac N x k (hψ.equiv t) := by
    induction t with
    | tmul r y => simp [F, IsBaseChange.equiv_tmul, hθ, LinearMap.map_smul_of_tower]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hsurj (z : R ⊗[R₀] LocalizedModule.Away x₀ N₀) : ∃ k t, F k t = z := by
    induction z with
    | tmul r z =>
      obtain ⟨k, y, rfl⟩ := exists_awayFrac z
      exact ⟨k, r ⊗ₜ y, by simp [F]⟩
    | add a b ha hb =>
      obtain ⟨k, t, rfl⟩ := ha
      obtain ⟨j, u, rfl⟩ := hb
      exact ⟨k + j, P j t + P k u, by rw [map_add (f := _), hFP, add_comm k j, hFP]⟩
  suffices hb : Function.Bijective (θ.liftBaseChange R) from
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hb) fun z => by simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨k, t, rfl⟩ := hsurj z
    rw [hF, awayFrac_eq_zero_iff] at hz
    obtain ⟨l, hl⟩ := hz
    rw [← hP, map_eq_zero_iff _ hψ.equiv.injective] at hl
    rw [← hFP k l, hl, map_zero]
  · intro z
    obtain ⟨k, y, rfl⟩ := exists_awayFrac z
    obtain ⟨t, rfl⟩ := hψ.equiv.surjective y
    exact ⟨F k t, hF k t⟩

end

theorem exists_isBaseChange_away_xProd :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ N : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (s : Finset ι), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → ∃ θ : LocalizedModule.Away (xProd R₀ s) N₀ →ₗ[R₀] LocalizedModule.Away (xProd R s) N, IsBaseChange R θ ∧ ∀ (k : ℕ) y, θ (awayFrac N₀ (xProd R₀ s) k y) = awayFrac N (xProd R s) k (ψ y) := by
  intro ι R₀ R _ _ _ N₀ N _ _ _ _ _ _ _ _ _ _ _ ψ s hψ hX
  classical
  have h₁ (y : N₀) : ψ (xProd R₀ s • y) = xProd R s • ψ y := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp only [xProd] at ih ⊢; simp only [Finset.prod_insert hi, mul_smul, hX, ih]
  have h (k : ℕ) (y : N₀) : ψ (xProd R₀ s ^ k • y) = xProd R s ^ k • ψ y := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, h₁, ih]
  obtain ⟨θ, hθ⟩ := exists_away_map_of_intertwine ψ _ _ h
  exact ⟨θ, isBaseChange_away_of_intertwine ψ hψ _ _ h θ hθ, hθ⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsBaseChangeCokerMatrixMvPolynomial
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_isBaseChange_coker {R₀ R A₀ A M₁ M₂ N₁ N₂ : Type*} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [Ring A₀] [Ring A] [Algebra R₀ A₀] [Algebra R A] [SMul R₀ A]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R₀ M₁] [Module R₀ M₂] [Module A₀ M₁] [Module A₀ M₂]
    [IsScalarTower R₀ A₀ M₁] [IsScalarTower R₀ A₀ M₂]
    [Module R₀ N₁] [Module R₀ N₂] [Module R N₁] [Module R N₂] [Module A N₁] [Module A N₂]
    [IsScalarTower R₀ R N₁] [IsScalarTower R₀ R N₂] [IsScalarTower R A N₁] [IsScalarTower R A N₂]
    [IsScalarTower R₀ A N₂]
    (f₀ : M₁ →ₗ[A₀] M₂) (f : N₁ →ₗ[A] N₂) (h₁ : M₁ →ₗ[R₀] N₁) (h₂ : M₂ →ₗ[R₀] N₂)
    (b₁ : IsBaseChange R h₁) (b₂ : IsBaseChange R h₂) (hcomm : ∀ x, h₂ (f₀ x) = f (h₁ x)) :
    ∃ ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f),
      IsBaseChange R ψ ∧ ∀ y, ψ (Submodule.Quotient.mk y) = Submodule.Quotient.mk (h₂ y) := by
  let q₀ : M₂ →ₗ[R₀] (M₂ ⧸ LinearMap.range f₀) := (LinearMap.range f₀).mkQ.restrictScalars R₀
  let q : N₂ →ₗ[R] (N₂ ⧸ LinearMap.range f) := (LinearMap.range f).mkQ.restrictScalars R
  have hq₀ : Function.Surjective q₀ := (LinearMap.range f₀).mkQ_surjective
  have hq : Function.Surjective q := (LinearMap.range f).mkQ_surjective
  have hex₀ : Function.Exact (f₀.restrictScalars R₀) q₀ := LinearMap.exact_map_mkQ_range f₀
  have hex : Function.Exact (f.restrictScalars R) q := LinearMap.exact_map_mkQ_range f
  have hker : LinearMap.ker q₀ ≤ LinearMap.ker ((q.restrictScalars R₀).comp h₂) := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hex₀ y).1 hy
    exact (hex _).2 ⟨h₁ x, (hcomm x).symm⟩
  let ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[R₀] (N₂ ⧸ LinearMap.range f) :=
    ((LinearMap.ker q₀).liftQ _ hker).comp (q₀.quotKerEquivOfSurjective hq₀).symm.toLinearMap
  have hψ : ∀ y, ψ (q₀ y) = q (h₂ y) := by
    intro y
    have : (q₀.quotKerEquivOfSurjective hq₀).symm (q₀ y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  exact ⟨ψ, IsBaseChange.of_right_exact R (f := f₀.restrictScalars R₀) (g := q₀)
    (f' := f.restrictScalars R) (g' := q) h₁ h₂ ψ (LinearMap.ext hcomm) (LinearMap.ext hψ)
    b₁ b₂ hex₀ hq₀ hex hq, hψ⟩

theorem isBaseChange_coker_matrix_mvPolynomial :
    ∀ (ι : Type) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (a b : ℕ)
      (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀))
      (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      Φ₀.map (MvPolynomial.map (algebraMap R₀ R)) = Φ →
      ∃ ψ : ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin) →ₗ[R₀]
          ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin),
        IsBaseChange R ψ ∧ ∀ y : Fin a → MvPolynomial ι R₀,
          ψ (Submodule.Quotient.mk y) =
            Submodule.Quotient.mk fun l => MvPolynomial.map (algebraMap R₀ R) (y l) := by
  intro ι R₀ R _ _ _ a b Φ₀ Φ hΦ
  have hm : IsBaseChange R (mapAlgHom (σ := ι) (Algebra.ofId R₀ R)).toLinearMap :=
    IsBaseChange.of_equiv (algebraTensorAlgEquiv R₀ R).toLinearEquiv fun p => by
      simp [mapAlgHom_apply]
  refine exists_isBaseChange_coker Φ₀.mulVecLin Φ.mulVecLin _ _
    (IsBaseChange.finitePow (Fin b) hm) (IsBaseChange.finitePow (Fin a) hm) fun x => ?_
  funext l
  rw [← hΦ]
  exact RingHom.map_mulVec (MvPolynomial.map (algebraMap R₀ R)) Φ₀ x l

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsBaseChangeGradedPiece
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem isBaseChange_gradedPiece : ∀ (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ N : Type) [AddCommGroup N₀] [Module R₀ N₀] [AddCommGroup N] [Module R₀ N] [Module R N] [IsScalarTower R₀ R N] (𝒩₀ : ℤ → Submodule R₀ N₀) [Decomposition 𝒩₀] (𝒩 : ℤ → Submodule R N) [Decomposition 𝒩] (ψ : N₀ →ₗ[R₀] N) (n : ℤ) (θ : 𝒩₀ n →ₗ[R₀] 𝒩 n), IsBaseChange R ψ → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → (∀ y, (θ y : N) = ψ y) → IsBaseChange R θ := by
  intro R₀ R _ _ _ N₀ N _ _ _ _ _ _ 𝒩₀ _ 𝒩 _ ψ n θ h hdeg hθ
  let p₀ : N₀ →ₗ[R₀] 𝒩₀ n :=
    DirectSum.component R₀ ℤ (fun i => 𝒩₀ i) n ∘ₗ (decomposeLinearEquiv 𝒩₀).toLinearMap
  let p : N →ₗ[R] 𝒩 n :=
    DirectSum.component R ℤ (fun i => 𝒩 i) n ∘ₗ (decomposeLinearEquiv 𝒩).toLinearMap
  have hp₀ : ∀ y, p₀ y = decompose 𝒩₀ y n := fun _ => rfl
  have hp : ∀ y, p y = decompose 𝒩 y n := fun _ => rfl
  have hp₀i : ∀ y : 𝒩₀ n, p₀ (y : N₀) = y := fun y => by
    apply Subtype.ext
    rw [hp₀]
    exact decompose_of_mem_same 𝒩₀ y.2
  have hpi : ∀ y : 𝒩 n, p (y : N) = y := fun y => by
    apply Subtype.ext
    rw [hp]
    exact decompose_of_mem_same 𝒩 y.2
  have hcomm : ∀ y, θ (p₀ y) = p (ψ y) := by
    intro y
    induction y using Decomposition.inductionOn 𝒩₀ with
    | zero => simp
    | @homogeneous j y =>
      by_cases hj : j = n
      · subst hj
        rw [hp₀i, ← hθ, hpi]
      · have h1 : p₀ (y : N₀) = 0 := by
          apply Subtype.ext
          rw [hp₀]
          exact decompose_of_mem_ne 𝒩₀ y.2 hj
        have h2 : p (ψ y) = 0 := by
          apply Subtype.ext
          rw [hp]
          exact decompose_of_mem_ne 𝒩 (hdeg j y y.2) hj
        rw [h1, h2, map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let L : R ⊗[R₀] 𝒩₀ n →ₗ[R] 𝒩 n := LinearMap.liftBaseChange R θ
  have hL1 : ∀ x, L (p₀.baseChange R x) = p (h.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hcomm]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hL2 : ∀ x, (L x : N) = h.equiv ((𝒩₀ n).subtype.baseChange R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [L, hθ]
    | add a b ha hb => simp only [map_add (f := _), Submodule.coe_add, ha, hb]
  have hret : ∀ x, p₀.baseChange R ((𝒩₀ n).subtype.baseChange R x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [hp₀i]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hbij : Function.Bijective L := by
    constructor
    · intro a b hab
      have h1 : h.equiv ((𝒩₀ n).subtype.baseChange R a)
          = h.equiv ((𝒩₀ n).subtype.baseChange R b) := by
        rw [← hL2, ← hL2, hab]
      rw [← hret a, h.equiv.injective h1, hret]
    · intro z
      refine ⟨p₀.baseChange R (h.equiv.symm z), ?_⟩
      rw [hL1, LinearEquiv.apply_symm_apply, hpi]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective L hbij) fun x => ?_
  simp [L]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsHomogeneousRangeMulVecLin
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem isGradedMap_mulVecLin {ι : Type} {R : Type*} [CommRing R] {κ μ : Type*} [Fintype μ]
    {d : κ → ℤ} {e : μ → ℤ} {Φ : Matrix κ μ (MvPolynomial ι R)}
    (h : ∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) :
    IsGradedMap (grFree ι R e) (grFree ι R d) Φ.mulVecLin := by
  intro n v hv
  refine mem_grPi.2 fun l => ?_
  rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, grShift_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have := grSMul_mem (polyGrading ι R) (h l j) (mem_grPi.1 hv j)
  rwa [smul_eq_mul, show n + -e j + (e j - d l) = n + -d l by ring] at this

theorem isHomogeneous_range_mulVecLin :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (a b : ℕ) (d : Fin a → ℤ)
      (e : Fin b → ℤ) (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)),
      (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) →
        (LinearMap.range Φ.mulVecLin).IsHomogeneous (grFree ι R d) :=
  fun _ _ _ _ _ _ _ _ _ _ h => (isGradedMap_mulVecLin h).isHomogeneous_range

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LinearIndependentLaurentMonomial
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem linearIndependent_laurentMonomial :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (s : Finset ι) (n : ℤ) (v : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → LocalizedModule.Away (xProd R s) (MvPolynomial ι R)), (∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0) → v a = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1)) → LinearIndependent R v := by
  intro ι _ _ R _ s n v hv
  rw [linearIndependent_iff']
  intro T g hg j hj
  let k : ℕ := T.sup fun a => Finset.univ.sup fun i => (a.1 i).natAbs
  let m : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → (ι →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm fun i => (a.1 i + if i ∈ s then (k : ℤ) else 0).toNat
  have hm : ∀ a ∈ T, ∀ i, (m a i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0 := by
    intro a ha i
    have hk : (a.1 i).natAbs ≤ k :=
      (Finset.le_sup (f := fun i => (a.1 i).natAbs) (Finset.mem_univ i)).trans
        (Finset.le_sup (f := fun a : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} =>
          Finset.univ.sup fun i => (a.1 i).natAbs) ha)
    refine Int.toNat_of_nonneg ?_
    split_ifs with hi
    · omega
    · simpa using a.2.2 i hi
  have hinj : ∀ a ∈ T, m a = m j → a = j := by
    intro a ha e
    refine Subtype.ext (funext fun i => ?_)
    have h1 := hm a ha i
    have h2 := hm j hj i
    rw [e, h2] at h1
    exact (add_right_cancel h1).symm
  have h0 : awayFrac (MvPolynomial ι R) (xProd R s) k
      (∑ a ∈ T, g a • monomial (m a) (1 : R)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hg]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hv a k (m a) (hm a ha), LinearMap.map_smul_of_tower]
  have h1 := congrArg (AddMonoidAlgebra.coeff · (m j))
    ((map_eq_zero_iff _ (awayFrac_injective (xProd_smul_injective s) k)).1 h0)
  rw [coeff_sum, Finset.sum_eq_single j, coeff_smul, coeff_monomial, if_pos rfl] at h1
  · simpa using h1
  · intro a ha hne
    rw [coeff_smul, coeff_monomial, if_neg fun e => hne (hinj a ha e), smul_zero]
  · exact fun h => absurd hj h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanLaurentMonomialEqHomLoc
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem span_laurentMonomial_eq_homLoc :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (s : Finset ι) (n : ℤ)
      (v : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} →
        LocalizedModule.Away (xProd R s) (MvPolynomial ι R)),
      (∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0) →
        v a = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1)) →
      Submodule.span R (Set.range v) = homLoc (polyGrading ι R) s n := by
  intro ι _ _ R _ s n v hv
  have hsum (k : ℤ) : ∑ i, (if i ∈ s then k else 0) = k * s.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hdeg (m : ι →₀ ℕ) : ((m.degree : ℕ) : ℤ) = ∑ i, (m i : ℤ) := by
    rw [Finsupp.degree_eq_sum]; push_cast; rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    let k : ℕ := ∑ i, (a.1 i).natAbs
    have hk (i : ι) : 0 ≤ a.1 i + if i ∈ s then (k : ℤ) else 0 := by
      split_ifs with h
      · have : (a.1 i).natAbs ≤ k :=
          Finset.single_le_sum (f := fun i => (a.1 i).natAbs) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
        omega
      · simpa using a.2.2 i h
    let m : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm
      fun i => (a.1 i + if i ∈ s then (k : ℤ) else 0).toNat
    have hm (i : ι) : (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0 :=
      Int.toNat_of_nonneg (hk i)
    rw [hv a k m hm]
    refine awayFrac_mem_homLoc (monomial_mem_polyGrading m 1) ?_
    rw [hdeg, Finset.sum_congr rfl fun i _ => hm i, Finset.sum_add_distrib, a.2.1, hsum]
  · rintro _ ⟨k, p, hp, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hd := mem_polyGrading_iff.1 hp m (mem_support_iff.1 hm)
    have e : monomial m (AddMonoidAlgebra.coeff p m) = AddMonoidAlgebra.coeff p m • (monomial m 1 : MvPolynomial ι R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, LinearMap.map_smul_of_tower]
    refine Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨fun i => m i - if i ∈ s then (k : ℤ) else 0, ?_, fun i hi => ?_⟩, hv _ k m fun i => ?_⟩)
    · rw [Finset.sum_sub_distrib, hsum, ← hdeg, hd, add_sub_cancel_right]
    · simp [hi]
    · simp

end GlobalTheory
end

