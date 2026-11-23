module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittExistsEquivOfCharpolyEqHypotheses
section
noncomputable section

namespace GlobalTheory.CharpolyIso

open Module Polynomial GlobalTheory.TraceIso

variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def cp (k : Type) [Field k] {A : Type} [Ring A] [Algebra k A] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Module A V] [IsScalarTower k A V] (a : A) : k[X] :=
  LinearMap.charpoly (Algebra.lsmul k k V a)

section

variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [FiniteDimensional k V] [FiniteDimensional k W]

theorem cp_congr (e : V ≃ₗ[A] W) (a : A) : cp k V a = cp k W a := by
  unfold cp
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k) (Algebra.lsmul k k V a)]
  congr 1
  ext w
  simp [LinearEquiv.conj_apply]

theorem cp_prod (a : A) : cp k (V × W) a = cp k V a * cp k W a := by
  unfold cp
  rw [← LinearMap.charpoly_prodMap]
  congr 1

theorem charpoly_one_eq (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    LinearMap.charpoly (1 : V →ₗ[k] V) = (X - 1 : k[X]) ^ finrank k V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis k V), LinearMap.toMatrix_one,
    Matrix.charpoly_one]
  simp

theorem charpoly_zero_eq (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    LinearMap.charpoly (0 : V →ₗ[k] V) = (X : k[X]) ^ finrank k V := by
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis k V), map_zero, Matrix.charpoly_zero]
  simp

theorem finrank_eq_zero_of_hom
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (h : ∀ a : A, cp k V a = cp k W a)
    (h₁ : ∀ f : V →ₗ[A] W, f = 0) (h₂ : ∀ f : W →ₗ[A] V, f = 0) : finrank k V = 0 := by
  classical
  let p : End A (V × W) := (LinearMap.inl A V W).comp (LinearMap.fst A V W)
  let F : End (End A (V × W)) (V × W) :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := by
        rintro φ ⟨v, w⟩
        have e₁ := LinearMap.congr_fun
          (h₁ ((LinearMap.snd A V W).comp (φ.comp (LinearMap.inl A V W)))) v
        have e₂ := LinearMap.congr_fun
          (h₂ ((LinearMap.fst A V W).comp (φ.comp (LinearMap.inr A V W)))) w
        have e₃ : φ (v, w) = φ (v, 0) + φ (0, w) := by rw [← map_add (f := _)]; simp
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.snd_apply,
          LinearMap.fst_apply, LinearMap.zero_apply] at e₁ e₂
        change ((φ (v, w)).1, (0 : W)) = φ (v, 0)
        rw [e₃]
        ext
        · simp [e₂]
        · exact e₁.symm }
  let b := Module.finBasis k (V × W)
  haveI : IsSemisimpleModule A (V × W) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A V W))
      (IsSemisimpleModule.range (LinearMap.inr A V W))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have hall : (p.restrictScalars k) = Algebra.lsmul k k (V × W) r :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hV : Algebra.lsmul k k V r = 1 := by
    ext v
    exact (congrArg Prod.fst (LinearMap.congr_fun hall (v, 0))).symm
  have hW : Algebra.lsmul k k W r = 0 := by
    ext w
    exact (congrArg Prod.snd (LinearMap.congr_fun hall (0, w))).symm
  have key := h r
  unfold cp at key
  rw [hV, hW, charpoly_one_eq, charpoly_zero_eq] at key
  have hdeg : finrank k V = finrank k W := by
    have := congrArg natDegree key
    have h1 : (X - 1 : k[X]).natDegree = 1 := by
      simpa using natDegree_X_sub_C (1 : k)
    simpa [natDegree_pow, h1] using this
  have h0 := congrArg (Polynomial.eval 0) key
  simp only [eval_pow, eval_sub, eval_X, eval_one, zero_sub] at h0
  by_contra hne
  have hW0 : finrank k W ≠ 0 := hdeg ▸ hne
  rw [zero_pow hW0] at h0
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h0

end

theorem nonempty_linear_equiv_of_charpoly_eq (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
    finrank k V + finrank k W ≤ n → (∀ a : A, cp k V a = cp k W a) → Nonempty (V ≃ₗ[A] W) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
      finrank k V + finrank k W ≤ n → (∀ a : A, cp k V a = cp k W a) → ∀ f : V →ₗ[A] W, f ≠ 0 →
      Nonempty (V ≃ₗ[A] W) := by
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h f hf
    obtain ⟨P, Q, S, ⟨e₁⟩, ⟨e₂⟩, hP, hQ⟩ := split_of_hom (k := k) f hf
    haveI := finiteDimensional_sub (k := k) P
    haveI := finiteDimensional_sub (k := k) Q
    haveI := finiteDimensional_sub (k := k) S
    obtain ⟨e⟩ := ih (finrank k P + finrank k Q) (by omega) P Q le_rfl fun a => by
      have := h a
      rw [cp_congr e₁, cp_congr e₂, cp_prod, cp_prod] at this
      have hS : cp k S a ≠ 0 := (LinearMap.charpoly_monic _).ne_zero
      exact mul_right_cancel₀ hS this
    exact ⟨e₁.trans ((e.prodCongr (LinearEquiv.refl A _)).trans e₂.symm)⟩
  intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h
  by_cases h₁ : ∀ f : V →ₗ[A] W, f = 0
  · by_cases h₂ : ∀ f : W →ₗ[A] V, f = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom h h₁ h₂)
      haveI : Subsingleton W :=
        Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom (fun a => (h a).symm) h₂ h₁)
      exact ⟨LinearEquiv.ofSubsingleton V W⟩
    · push_neg at h₂
      obtain ⟨f, hf⟩ := h₂
      obtain ⟨e⟩ := step W V (by omega) (fun a => (h a).symm) f hf
      exact ⟨e.symm⟩
  · push_neg at h₁
    obtain ⟨f, hf⟩ := h₁
    exact step V W hn h f hf

theorem cp_asModule {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k Γ V) (a : MonoidAlgebra k Γ) :
    haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
    cp k ρ.asModule a = LinearMap.charpoly (ρ.asAlgebraHom a) := by
  haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  unfold cp
  rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv.symm (ρ.asAlgebraHom a)]
  congr 1

theorem exists_equiv_of_charpoly_eq {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) (hρ : ρ.IsSemisimpleRepresentation)
    (hσ : σ.IsSemisimpleRepresentation)
    (h : ∀ a : MonoidAlgebra k Γ,
      LinearMap.charpoly (ρ.asAlgebraHom a) = LinearMap.charpoly (σ.asAlgebraHom a)) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 hρ
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 hσ
  haveI : FiniteDimensional k ρ.asModule := ρ.asModuleEquiv.symm.finiteDimensional
  haveI : FiniteDimensional k σ.asModule := σ.asModuleEquiv.symm.finiteDimensional
  have key : ∀ a : MonoidAlgebra k Γ, cp k ρ.asModule a = cp k σ.asModule a := fun a => by
    rw [cp_asModule, cp_asModule, h]
  obtain ⟨e⟩ := nonempty_linear_equiv_of_charpoly_eq (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule σ.asModule le_rfl key
  refine ⟨ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv), fun g v => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul]
  simp

theorem exists_equiv_of_charpoly_eq' : ∀ {k Γ V W : Type} [Field k] [Monoid Γ] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k Γ V)
    (σ : Representation k Γ W), ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation →
    (∀ a : MonoidAlgebra k Γ, LinearMap.charpoly (ρ.asAlgebraHom a) =
      LinearMap.charpoly (σ.asAlgebraHom a)) →
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) :=
  fun ρ σ hρ hσ h => exists_equiv_of_charpoly_eq ρ σ hρ hσ h

end GlobalTheory.CharpolyIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CDvdOfDvdXPowMul
section
noncomputable section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT.EEBasic

section General
variable {B : Type} [CommRing B] (b : B)

theorem pow_dvd_iff_eval (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣ x ↔
      AdicCompletion.eval (Ideal.span {b}) B k x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval
    (Submodule.fg_span_singleton b), Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton,
    map_pow]

theorem eval_algebraMap (k : ℕ) (c : B) :
    AdicCompletion.eval (Ideal.span {b}) B k (algebraMap B (AdicCompletion (Ideal.span {b}) B) c)
      = Submodule.Quotient.mk c := by
  rw [AdicCompletion.algebraMap_apply]
  rfl

theorem pow_dvd_of_pow_dvd (k : ℕ) (c : B)
    (h : (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      algebraMap B (AdicCompletion (Ideal.span {b}) B) c) : b ^ k ∣ c := by
  rw [pow_dvd_iff_eval, eval_algebraMap, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
    Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  exact h

theorem exists_pow_dvd_sub (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    ∃ c : B, (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      x - algebraMap B (AdicCompletion (Ideal.span {b}) B) c := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (Ideal.span {b}) B k x)
  exact ⟨c, by rw [pow_dvd_iff_eval, map_sub, eval_algebraMap, hc, sub_self]⟩

theorem complete : IsAdicComplete
    (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b})
    (AdicCompletion (Ideal.span {b}) B) := by
  have h : Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b} =
      (Ideal.span {b}).map (algebraMap B (AdicCompletion (Ideal.span {b}) B)) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton b)

end General

variable {O : Type} [CommRing O]

theorem C_dvd_iff (c : O) (a : O⟦X⟧) : C c ∣ a ↔ ∀ n, c ∣ coeff n a := by
  constructor
  · rintro ⟨q, rfl⟩ n
    rw [coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose q hq using h
    exact ⟨PowerSeries.mk q, PowerSeries.ext fun n => by rw [coeff_C_mul, coeff_mk, hq]⟩

theorem C_dvd_of_dvd_X_pow_mul (c : O) (m : ℕ) (a : O⟦X⟧) (h : C c ∣ X ^ m * a) : C c ∣ a := by
  rw [C_dvd_iff] at h ⊢
  intro n
  have := h (n + m)
  rwa [coeff_X_pow_mul] at this

theorem C_dvd_of_dvd_away (c : O) (a : O⟦X⟧)
    (h : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c) ∣
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) : C c ∣ a := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) z
  have h1 : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (X ^ m * a) =
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c * q) := by
    rw [map_mul, map_mul, map_pow, hz, ← hq]; ring
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (X : O⟦X⟧) h1
  refine C_dvd_of_dvd_X_pow_mul c (n + m) a ⟨X ^ n * q, ?_⟩
  rw [pow_add, mul_assoc, hn]; ring

theorem algebraMap_EE (l : ℕ) (a : O⟦X⟧) : algebraMap O⟦X⟧ (EE O l) a =
    algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)
      (algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]; rfl

theorem saturated (l : ℕ) (a : O⟦X⟧) (k : ℕ)
    (h : (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a) : (l : O⟦X⟧) ^ k ∣ a := by
  rw [algebraMap_EE, ← map_natCast (algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)) l] at h
  have h2 := pow_dvd_of_pow_dvd _ k _ h
  have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
  rw [e]
  apply C_dvd_of_dvd_away
  rwa [← e, map_pow, map_natCast]

end GlobalTheory.NB.LT.EEBasic

namespace GlobalTheory.NB.LT

open EEBasic

theorem EE_basic : ∀ {l : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O], l.Prime → ¬ IsUnit (l : O) → Function.Injective (algebraMap O⟦X⟧ (EE O l)) ∧ IsUnit (algebraMap O⟦X⟧ (EE O l) X) ∧ IsAdicComplete (Ideal.span {(l : EE O l)}) (EE O l) ∧ (∀ (x : EE O l) (k : ℕ), ∃ (a : O⟦X⟧) (m : ℕ), (l : EE O l) ^ k ∣ x * algebraMap O⟦X⟧ (EE O l) (X ^ m) - algebraMap O⟦X⟧ (EE O l) a) ∧ (∀ (a : O⟦X⟧) (k : ℕ), (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a → (l : O⟦X⟧) ^ k ∣ a) := by
  intro l O _ _ _ _ _ _ hl
  refine ⟨?_, ?_, ?_, ?_, saturated l⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) inferInstance _ fun k => ?_
    have h1 := saturated l a k (by rw [ha]; exact dvd_zero _)
    have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
    rw [e, C_dvd_iff] at h1
    obtain ⟨q, hq⟩ := h1 n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hq]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).2 hl) k)
  · rw [algebraMap_EE]
    exact (IsLocalization.Away.algebraMap_isUnit (X : O⟦X⟧)).map _
  · have := complete (l : Localization.Away (X : O⟦X⟧))
    rwa [map_natCast] at this
  · intro x k
    obtain ⟨c, hc⟩ := exists_pow_dvd_sub (l : Localization.Away (X : O⟦X⟧)) k x
    rw [map_natCast] at hc
    obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) c
    refine ⟨q, m, ?_⟩
    rw [algebraMap_EE l q, ← hq, map_mul, algebraMap_EE, map_pow (algebraMap O⟦X⟧ _), ← sub_mul]
    exact hc.mul_right _

end GlobalTheory.NB.LT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CMemCoeffSub
section
open scoped BigOperators

namespace GlobalTheory.BlockDetPoly

def coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ) :
    Subalgebra (MvPolynomial (Fin m) O) (X → MvPolynomial (Fin m) O) where
  carrier := {f | ∀ d, (fun x => AddMonoidAlgebra.coeff (f x) d) ∈ T}
  mul_mem' := by
    intro f g hf hg d
    have : (fun x => AddMonoidAlgebra.coeff ((f * g) x) d) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal d,
        (fun x => AddMonoidAlgebra.coeff (f x) p.1) * (fun x => AddMonoidAlgebra.coeff (g x) p.2) := by
      funext x
      simp [MvPolynomial.coeff_mul, Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg d
    have : (fun x => AddMonoidAlgebra.coeff ((f + g) x) d) =
        (fun x => AddMonoidAlgebra.coeff (f x) d) + (fun x => AddMonoidAlgebra.coeff (g x) d) := by
      funext x
      simp
    rw [this]
    exact T.add_mem (hf _) (hg _)
  algebraMap_mem' := fun p d => T.algebraMap_mem (AddMonoidAlgebra.coeff p d)

theorem C_mem_coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (t : X → O) (ht : t ∈ T) : (fun x => MvPolynomial.C (t x)) ∈ coeffSub T m := by
  show ∀ d : Fin m →₀ ℕ,
    (fun x => AddMonoidAlgebra.coeff (MvPolynomial.C (t x) : MvPolynomial (Fin m) O) d) ∈ T
  intro d
  rcases eq_or_ne d 0 with rfl | hd
  · simpa using ht
  · have h0 : (fun x => AddMonoidAlgebra.coeff (MvPolynomial.C (t x) : MvPolynomial (Fin m) O) d) = 0 := by
      funext x
      simp [MvPolynomial.coeff_C, Ne.symm hd]
    rw [h0]
    exact T.zero_mem

theorem det_comb_mem {O X Q : Type} [CommRing O] [CommRing Q] (T : Subalgebra O (X → O)) {n : ℕ}
    (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O))
    (hR : ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) →
      ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T)
    (φ : O →+* Q) (S : Subalgebra Q (X → Q)) (hS : ∀ t ∈ T, (fun x => φ (t x)) ∈ S)
    {J : Type} [Fintype J] (b : J → X → Matrix (Fin n) (Fin n) O) (hb : ∀ j, b j ∈ R)
    (c : J → Q) : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) ∈ S := by
  classical

  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a : Fin (Fintype.card J) → X → Matrix (Fin n) (Fin n) O := fun k => b (e k)

  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Fintype.card J)) (X → O)) :=
    Matrix.of fun i j => ∑ k, MvPolynomial.X k * MvPolynomial.C (fun x => a k x i j)
  have hcoef : ∀ d, AddMonoidAlgebra.coeff A.det d ∈ T := by
    intro d
    have h1 : AddMonoidAlgebra.coeff A.det d = fun x => AddMonoidAlgebra.coeff (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
          (a k x).map MvPolynomial.C)) d := by
      funext x
      have h2 : MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) A.det =
          Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
            (a k x).map MvPolynomial.C) := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        simp [A, Matrix.sum_apply]
      rw [← h2, MvPolynomial.coeff_map]
      rfl
    rw [h1]
    exact hR _ a (fun k => hb (e k)) d

  have h3 : ∀ x, Matrix.det (∑ j, c j • (b j x).map φ) =
      MvPolynomial.eval₂ (φ.comp (Pi.evalRingHom (fun _ : X => O) x)) (fun k => c (e k)) A.det := by
    intro x
    rw [← MvPolynomial.coe_eval₂Hom, RingHom.map_det]
    congr 1
    ext i j
    simp only [A, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_C, RingHom.comp_apply, Pi.evalRingHom_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    exact (e.sum_comp (fun j' => c j' * φ (b j' x i j))).symm
  have key : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) =
      ∑ d ∈ A.det.support, (fun x => φ (AddMonoidAlgebra.coeff A.det d x)) *
        algebraMap Q (X → Q) (∏ k, c (e k) ^ d k) := by
    funext x
    rw [h3, MvPolynomial.eval₂_eq', Finset.sum_apply]
    simp
  rw [key]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hcoef d)) (S.algebraMap_mem _)

private theorem mem_coeffSub_iff_forall_coeff_mem {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (f : X → MvPolynomial (Fin m) O) :
    f ∈ coeffSub T m ↔ ∀ d, (fun x => AddMonoidAlgebra.coeff (f x) d) ∈ T := Iff.rfl

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T) → ∀ (m g : ℕ) (Θ : Fin m → Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ k p q, Θ k p q ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) * MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2))) d) ∈ T := by
  intro O X _ T n R hR m g Θ hΘ d
  classical

  let ψ : (X → Matrix (Fin n) (Fin n) O) →+* (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    RingHom.compLeft (MvPolynomial.C : O →+* MvPolynomial (Fin m) O).mapMatrix X
  have hψ : ∀ (a : X → Matrix (Fin n) (Fin n) O) x, ψ a x = (a x).map MvPolynomial.C :=
    fun _ _ => rfl
  let s : Submonoid (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) := R.toSubmonoid.map ψ
  let R' : Subalgebra (MvPolynomial (Fin m) O) (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    Algebra.adjoin (MvPolynomial (Fin m) O) (s : Set _)

  have hrep : ∀ F ∈ R', ∃ (N : ℕ) (c : Fin N → MvPolynomial (Fin m) O)
      (b : Fin N → X → Matrix (Fin n) (Fin n) O), (∀ j, b j ∈ R) ∧ F = ∑ j, c j • ψ (b j) := by
    intro F hF
    have hF' : F ∈ Submodule.span (MvPolynomial (Fin m) O) (s : Set _) := by
      have h := Algebra.adjoin_eq_span (R := MvPolynomial (Fin m) O)
        (s : Set (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)))
      rw [Submonoid.closure_eq] at h
      rw [← h]
      exact hF
    obtain ⟨N, c, b, hsum⟩ := Submodule.mem_span_set'.mp hF'
    choose b' hb' hbe using fun j => Submonoid.mem_map.mp (b j).2
    refine ⟨N, c, b', fun j => hb' j, ?_⟩
    rw [← hsum]
    simp [hbe]

  have hR' : ∀ (m' : ℕ) (a : Fin m' → X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)),
      (∀ k, a k ∈ R') → ∀ d' : Fin m' →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C)) d') ∈ coeffSub T m := by
    intro m' a ha d'
    choose N c b hb hab using fun k => hrep (a k) (ha k)
    have hS : ∀ t ∈ T, (fun x => ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (t x)) ∈ coeffSub (coeffSub T m) m' :=
      fun t ht => C_mem_coeffSub (coeffSub T m) m' _ (C_mem_coeffSub T m t ht)
    have h := det_comb_mem T R hR ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (coeffSub (coeffSub T m) m') hS
      (J := Σ k, Fin (N k)) (fun kj => b kj.1 kj.2) (fun kj => hb kj.1 kj.2)
      (fun kj => MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2))
    have heq : ∀ x, (∑ kj : (Σ k, Fin (N k)), (MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2) :
          MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) • (b kj.1 kj.2 x).map
          ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
            (MvPolynomial (Fin m) O)).comp MvPolynomial.C)) =
        ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C := by
      intro x
      ext i j
      simp [hab, hψ, Matrix.sum_apply, Fintype.sum_sigma, Finset.mul_sum, mul_assoc, Finset.sum_apply]
    simp only [heq] at h
    exact (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp h d'

  have hblk : ∀ p q, (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
      (Θ k p q x).map MvPolynomial.C) ∈ R' := by
    intro p q
    have h4 : (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
        (Θ k p q x).map MvPolynomial.C) = ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • ψ (Θ k p q) := by
      funext x
      simp [Finset.sum_apply, hψ]
    rw [h4]
    exact R'.sum_mem fun k _ =>
      R'.smul_mem (Algebra.subset_adjoin (Submonoid.mem_map.mpr ⟨Θ k p q, hΘ k p q, rfl⟩)) _
  have h5 := (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp (GlobalTheory.BlockDet.main (coeffSub T m) n R' hR' g _ hblk) d
  have h6 : ∀ x, (Matrix.of fun (pa qb : Fin g × Fin n) => (∑ k, (MvPolynomial.X k :
        MvPolynomial (Fin m) O) • (Θ k pa.1 qb.1 x).map MvPolynomial.C) pa.2 qb.2) =
      Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) *
        MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2) := by
    intro x
    ext pa qb
    simp [Matrix.sum_apply]
  simp only [h6] at h5
  exact h5

end GlobalTheory.BlockDetPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatibleSeqOfFiniteNonemptyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_seq_of_finite_nonempty' : ∀ (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n)), (∀ n, (Y n).Finite) → (∀ n, (Y n).Nonempty) → (∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) → ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by
  first | exact @GlobalTheory.exists_compatible_seq_of_finite_nonempty | exact GlobalTheory.exists_compatible_seq_of_finite_nonempty | (intros; apply GlobalTheory.exists_compatible_seq_of_finite_nonempty <;> assumption)
end

