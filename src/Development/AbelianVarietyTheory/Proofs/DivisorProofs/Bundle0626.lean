module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjOfStrictHenselisationPolynomial
section
open IsLocalRing Polynomial
open GlobalTheory.EtC

namespace GlobalTheory

theorem surj_of_strictHenselisation_polynomial : ∀ (T : Type) [CommRing T] (A : Type) [CommRing A]
    [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A →
    (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E)
      (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) →
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra T O) (_ : Algebra (Polynomial T) O)
      (_ : IsScalarTower T (Polynomial T) O) (_ : HenselianLocalRing O)
      (_ : IsSepClosed (IsLocalRing.ResidueField O)) (π : O →ₐ[Polynomial T] A),
      Function.Surjective π ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·))
        (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧
        (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E)
          (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E)
          (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) := by
  intro T _ A _ _ _ _ hSH hA
  obtain ⟨hHA, hsepA⟩ := hSH
  let y : Ideal (Polynomial T) := (maximalIdeal A).comap (algebraMap (Polynomial T) A)
  haveI : y.IsPrime := Ideal.comap_isPrime _ _
  set_option synthInstance.maxHeartbeats 400000 in
  obtain ⟨O, _, algRO, _, hloc, hsc, -, -, -, hind⟩ :=
    GlobalTheory.exists_strictHenselisation (Localization.AtPrime y)
      (SeparableClosure (ResidueField (Localization.AtPrime y)))
  letI algPO : Algebra (Polynomial T) O :=
    ((algebraMap (Localization.AtPrime y) O).comp
      (algebraMap (Polynomial T) (Localization.AtPrime y))).toAlgebra
  letI algTO : Algebra T O := ((algebraMap (Polynomial T) O).comp (algebraMap T (Polynomial T))).toAlgebra
  haveI t1 : IsScalarTower T (Polynomial T) O := IsScalarTower.of_algebraMap_eq' rfl
  haveI t2 : IsScalarTower (Polynomial T) (Localization.AtPrime y) O :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hP := GlobalTheory.indEtale_localPieces_trans (Polynomial T) (Localization.AtPrime y) O
    ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤, monotone_const,
      fun _ => ⟨(), Algebra.mem_top⟩,
      fun _ => ⟨Polynomial T, inferInstance, inferInstance, inferInstance, y, inferInstance,
        ⟨Subalgebra.topEquiv.symm⟩⟩⟩ hind

  have hRO : (maximalIdeal O).comap (algebraMap (Localization.AtPrime y) O) =
      maximalIdeal (Localization.AtPrime y) := by
    ext x
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  have hyO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = y := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) (Localization.AtPrime y) O, ← Ideal.comap_comap,
      hRO]
    exact Localization.AtPrime.under_maximalIdeal
  have hkO : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField O) r = 0 ↔ r ∈ y := by
    intro r
    rw [IsScalarTower.algebraMap_apply (Polynomial T) O (ResidueField O), ResidueField.algebraMap_eq,
      residue_eq_zero_iff, ← hyO, Ideal.mem_comap]
  have hkA : ∀ r : Polynomial T, algebraMap (Polynomial T) (ResidueField A) r = 0 ↔ r ∈ y := by
    intro r
    rw [IsScalarTower.algebraMap_apply (Polynomial T) A (ResidueField A), ResidueField.algebraMap_eq,
      residue_eq_zero_iff]
    rfl
  letI algyO : Algebra y.ResidueField (ResidueField O) :=
    (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField O)) (fun r hr => (hkO r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hkO r).1 h)))).toAlgebra
  haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm
  letI algyA : Algebra y.ResidueField (ResidueField A) :=
    (Ideal.ResidueField.lift y (algebraMap (Polynomial T) (ResidueField A)) (fun r hr => (hkA r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hkA r).1 h)))).toAlgebra
  haveI : IsScalarTower (Polynomial T) y.ResidueField (ResidueField A) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap y _ _ _ r).symm

  have hsepO : ∀ s : O, IsSeparable y.ResidueField (algebraMap O (ResidueField O) s) := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hpc⟩ := hP
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hpc i
    let F : Localization.AtPrime q →ₐ[Polynomial T] ResidueField O :=
      (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O)).comp ((Si i).val.comp e.toAlgHom)
    let f : B →ₐ[Polynomial T] ResidueField O :=
      F.comp (IsScalarTower.toAlgHom (Polynomial T) B (Localization.AtPrime q))
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)
    have hs : algebraMap O (ResidueField O) s = F (IsLocalization.mk' _ a t) := by
      simp only [F, AlgHom.comp_apply, hat]
      simp
    have hft : f t ≠ 0 := by
      have : IsUnit (f t) :=
        (IsLocalization.map_units (Localization.AtPrime q) t).map F
      exact this.ne_zero
    have hmul : F (IsLocalization.mk' _ a t) * f t = f a := by
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul,
        IsLocalization.mk'_spec]
    have hx : algebraMap O (ResidueField O) s = f a * (f t)⁻¹ := by
      rw [hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]
    rw [hx, ← mem_separableClosure_iff]
    refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>
      exact GlobalTheory.Specialise.sepEtale (Polynomial T) B y _ f _
  haveI : Algebra.IsSeparable y.ResidueField (ResidueField O) := ⟨fun x => by
    obtain ⟨s, rfl⟩ := residue_surjective x
    have := hsepO s
    rwa [ResidueField.algebraMap_eq] at this⟩
  haveI : IsSepClosure y.ResidueField (ResidueField O) := ⟨hsc, inferInstance⟩
  let L := separableClosure y.ResidueField (ResidueField A)
  let e : ResidueField O ≃ₐ[y.ResidueField] L := IsSepClosure.equiv y.ResidueField (ResidueField O) L
  let ι : ResidueField O →ₐ[y.ResidueField] ResidueField A := L.val.comp e.toAlgHom
  let ψ₀ : O →ₐ[Polynomial T] ResidueField A :=
    (ι.restrictScalars (Polynomial T)).comp (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O))
  obtain ⟨π, hπ⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp (Polynomial T) O A hP).2 ψ₀
  refine ⟨O, inferInstance, algTO, algPO, t1, inferInstance, hsc, π, ?_, hP⟩
  intro b
  obtain ⟨E, _, _, _, φ, hb⟩ := hA b
  obtain ⟨e0, rfl⟩ := (AlgHom.mem_range φ).1 hb
  let f : E →ₐ[Polynomial T] ResidueField A :=
    (IsScalarTower.toAlgHom (Polynomial T) A (ResidueField A)).comp φ
  have hfL : ∀ x, f x ∈ L := fun x =>
    mem_separableClosure_iff.2 (GlobalTheory.Specialise.sepEtale (Polynomial T) E y (ResidueField A) f x)
  let g : E →ₐ[Polynomial T] ResidueField O :=
    { toRingHom := (e.symm : L →+* ResidueField O).comp (f.toRingHom.codRestrict L hfL)
      commutes' := fun r => by
        apply e.injective
        change e (e.symm ⟨f (algebraMap _ E r), hfL _⟩) = _
        rw [AlgEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField O),
          AlgEquiv.commutes]
        change f (algebraMap _ E r) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (Polynomial T) y.ResidueField (ResidueField A)]
        rfl }
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E O).2 g
  have hcomp : π.comp ψ = φ := by
    apply (GlobalTheory.EtaleHensel.bijective_residue_comp (Polynomial T) E A).1
    dsimp only
    ext x
    have h1 := DFunLike.congr_fun hπ (ψ x)
    have h2 := DFunLike.congr_fun hψ x
    simp only [AlgHom.comp_apply] at h1 h2 ⊢
    rw [h1]
    change ι (IsScalarTower.toAlgHom (Polynomial T) O (ResidueField O) (ψ x)) = f x
    rw [h2]
    change ((e (e.symm ⟨f x, hfL x⟩) : L) : ResidueField A) = f x
    rw [AlgEquiv.apply_symm_apply]
  exact ⟨ψ e0, DFunLike.congr_fun hcomp e0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveEvalTmul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SurjTens

variable {O σ ι : Type} [CommRing O]


open Classical in
def pushVars (j : σ → ι) (f : MvPowerSeries σ O) : MvPowerSeries ι O :=
  fun β => if h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β then coeff h.choose f else 0

theorem coeff_pushVars_mapDomain {j : σ → ι} (hj : Function.Injective j) (f : MvPowerSeries σ O)
    (α : σ →₀ ℕ) : coeff (Finsupp.mapDomain j α) (pushVars j f) = coeff α f := by
  have h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = Finsupp.mapDomain j α := ⟨α, rfl⟩
  rw [coeff_apply]
  unfold pushVars
  rw [dite_eq_left h, Finsupp.mapDomain_injective hj h.choose_spec]

theorem coeff_pushVars_of_not {j : σ → ι} (f : MvPowerSeries σ O) (β : ι →₀ ℕ)
    (h : ¬∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β) : coeff β (pushVars j f) = 0 := by
  rw [coeff_apply]
  unfold pushVars
  rw [dite_eq_right h]

theorem pushVars_add {j : σ → ι} (hj : Function.Injective j) (f g : MvPowerSeries σ O) :
    pushVars j (f + g) = pushVars j f + pushVars j g := by
  ext β
  by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
  · obtain ⟨α, rfl⟩ := h
    simp only [map_add (f := _), coeff_pushVars_mapDomain hj]
  · simp only [map_add (f := _), coeff_pushVars_of_not _ _ h, add_zero]

theorem pushVars_monomial {j : σ → ι} (hj : Function.Injective j) (α : σ →₀ ℕ) (c : O) :
    pushVars j (monomial α c) = monomial (Finsupp.mapDomain j α) c := by
  classical
  ext β
  by_cases h : ∃ α' : σ →₀ ℕ, Finsupp.mapDomain j α' = β
  · obtain ⟨α', rfl⟩ := h
    rw [coeff_pushVars_mapDomain hj, coeff_monomial, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hj).eq_iff]
  · rw [coeff_pushVars_of_not _ _ h, coeff_monomial, if_neg]
    rintro rfl
    exact h ⟨α, rfl⟩

theorem pushVars_coe {j : σ → ι} (hj : Function.Injective j) (P : MvPolynomial σ O) :
    pushVars j (P : MvPowerSeries σ O) = ((MvPolynomial.rename j P : MvPolynomial ι O) : MvPowerSeries ι O) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [MvPolynomial.coe_monomial, MvPolynomial.rename_monomial, MvPolynomial.coe_monomial,
      pushVars_monomial hj]
  | add P Q hP hQ =>
    rw [MvPolynomial.coe_add, pushVars_add hj, hP, hQ, map_add (f := _), MvPolynomial.coe_add]

theorem eval_coe {R A κ : Type} [CommRing R] [CommRing A] [Algebra R A] (z : κ → A)
    (E : MvPowerSeries κ R →ₐ[R] A) (hE : ∀ i, E (X i) = z i) (P : MvPolynomial κ R) :
    E (P : MvPowerSeries κ R) = MvPolynomial.aeval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom R) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

theorem exists_eval_pushVars (p : ℕ) {A C : Type} [CommRing A] [CommRing C] [Algebra O A] [Algebra O C]
    [Fintype σ] [IsHausdorff (Ideal.span {(p : C)}) C] (j : σ → ι) (hj : Function.Injective j)
    (x : σ → A) (z : ι → C) (φ : A →ₐ[O] C) (evA : MvPowerSeries σ O →ₐ[O] A)
    (E : MvPowerSeries ι O →ₐ[O] C) (hA : IsEval p x evA) (hE : IsEval p z E)
    (hz : ∀ i, z (j i) = φ (x i)) (f : MvPowerSeries σ O) :
    E (pushVars j f) = φ (evA f) := by
  classical
  have hpoly : ∀ P : MvPolynomial σ O, E (pushVars j (P : MvPowerSeries σ O)) = φ (evA P) := by
    intro P
    rw [pushVars_coe hj, eval_coe z E hE.1, eval_coe x evA hA.1, MvPolynomial.aeval_rename]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have hzj : z ∘ j = fun i => φ (x i) := funext hz
    rw [hzj]
  refine sub_eq_zero.1 (IsHausdorff.haus (I := Ideal.span {(p : C)}) inferInstance _ fun m => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨N1, hN1⟩ := hE.2 m
  obtain ⟨N2, hN2⟩ := hA.2 m
  set N := max N1 N2
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  set P : MvPolynomial σ O := trunc' O n f
  set g : MvPowerSeries σ O := f - (P : MvPowerSeries σ O)
  have hg : ∀ α : σ →₀ ℕ, α.degree < N → coeff α g = 0 := by
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  have hgA : (p : A) ^ m ∣ evA g := hN2 g fun α hα => hg α (lt_of_lt_of_le hα (le_max_right _ _))
  have hgE : (p : C) ^ m ∣ E (pushVars j g) := by
    apply hN1
    intro β hβ
    by_cases h : ∃ α : σ →₀ ℕ, Finsupp.mapDomain j α = β
    · obtain ⟨α, rfl⟩ := h
      rw [coeff_pushVars_mapDomain hj]
      apply hg
      rw [Finsupp.degree_mapDomain] at hβ
      exact lt_of_lt_of_le hβ (le_max_left _ _)
    · exact coeff_pushVars_of_not _ _ h
  have hgφ : (p : C) ^ m ∣ φ (evA g) := by
    have := map_dvd φ hgA
    simpa only [map_pow, map_natCast] using this
  have hf : f = g + (P : MvPowerSeries σ O) := by simp [g]
  have key : E (pushVars j f) - φ (evA f) = E (pushVars j g) - φ (evA g) := by
    rw [hf, pushVars_add hj, map_add (f := _), map_add (f := _), map_add (f := _), hpoly P]
    ring
  rw [key]
  exact dvd_sub hgE hgφ

theorem surjective_eval_tmul : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] [IsHausdorff (Ideal.span {(p : A ⊗[O] B)}) (A ⊗[O] B)] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → Function.Surjective E := by
  intro p O A B σ τ _ _ _ _ _ _ _ _ x y evA evB E hA hB hE sA sB
  have hl : ∀ a : A, a ⊗ₜ[O] (1 : B) ∈ E.range := by
    intro a
    obtain ⟨f, rfl⟩ := sA a
    refine ⟨pushVars Sum.inl f, ?_⟩
    have := exists_eval_pushVars p Sum.inl Sum.inl_injective x _ Algebra.TensorProduct.includeLeft
      evA E hA hE (fun i => by simp) f
    simpa using this
  have hr : ∀ b : B, (1 : A) ⊗ₜ[O] b ∈ E.range := by
    intro b
    obtain ⟨g, rfl⟩ := sB b
    refine ⟨pushVars Sum.inr g, ?_⟩
    have := exists_eval_pushVars p Sum.inr Sum.inr_injective y _ Algebra.TensorProduct.includeRight
      evB E hB hE (fun i => by simp) g
    simpa using this
  intro t
  have : t ∈ E.range := by
    induction t using TensorProduct.induction_on with
    | zero => exact Subalgebra.zero_mem _
    | tmul a b =>
      have h := Subalgebra.mul_mem _ (hl a) (hr b)
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
    | add s t hs ht => exact Subalgebra.add_mem _ hs ht
  exact this

end GlobalTheory.SurjTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCharacterExtAndExistsOfIntegralPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacterExt


open Algebra.TensorProduct in
theorem tensor_eq_zero_of_forall_pair (O F : Type) [CommRing O] [Field F] [IsAlgClosed F]
    [Algebra O F] [Module.Flat O F] (hinj : Function.Injective (algebraMap O F)) (A : Type)
    [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A]
    [_root_.IsReduced (F ⊗[O] A)] (t : A ⊗[O] A)
    (ht : ∀ x y : A →ₐ[O] F, lift x y (fun _ _ => Commute.all _ _) t = 0)
    (hmul : Function.Injective (LinearMap.mul' O F)) : t = 0 := by
  refine tensor_eq_zero_of_forall_geometric_point O F hinj A A t fun x => ?_
  apply (TensorProduct.comm O F A).injective
  rw [map_zero]
  refine tensor_eq_zero_of_forall_geometric_point O F hinj A F _ fun y => ?_
  apply hmul
  rw [map_zero, ← ht x y]
  clear ht
  induction t with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a b => simp [mul_comm]

variable {O : Type} [CommRing O]

theorem exists_pair {A : Type} [CommRing A] [Algebra O A] {T : Over (Spec (CommRingCat.of O))}
    (x y : T ⟶ specO O A) : ∃ t : T ⟶ specO O (A ⊗[O] A),
      t ≫ ptMap Algebra.TensorProduct.includeLeft = x ∧
        t ≫ ptMap Algebra.TensorProduct.includeRight = y := by
  have h1 : ((lift x y).left ≫ (pullbackSpecIso O A A).hom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = x.left := by
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    exact congrArg Over.Hom.left (lift_fst x y)
  have h2 : ((lift x y).left ≫ (pullbackSpecIso O A A).hom) ≫
      (ptMap (Algebra.TensorProduct.includeRight : A →ₐ[O] A ⊗[O] A)).left = y.left := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((lift x y).left ≫ ·) (pullbackSpecIso_hom_snd O A A)).trans ?_
    exact congrArg Over.Hom.left (lift_snd x y)
  refine ⟨Over.homMk ((lift x y).left ≫ (pullbackSpecIso O A A).hom) ?_,
    Over.OverMorphism.ext h1, Over.OverMorphism.ext h2⟩
  rw [← Over.w y, ← h2, Category.assoc _ (ptMap _).left, Over.w]

end GlobalTheory.TorsionCharacterExt

namespace GlobalTheory


open KernelNoTorsion TangentPow TorsionCharacter GmPoints in
theorem torsionCharacter_ext_and_exists_of_integral_points :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G], ∀ N : ℕ, 1 ≤ N → IsFinite (torsion G N).hom → Flat (torsion G N).hom → (∀ f f' : torsion G N ⟶ Gm (Spec (CommRingCat.of O)), (∀ w : specO O O ⟶ torsion G N, w ≫ f = w ≫ f') → f = f') ∧ ∀ κ : (specO O O ⟶ G) → Cˣ, (∀ x y : specO O O ⟶ G, x ^ N = 1 → y ^ N = 1 → κ (x * y) = κ x * κ y) → ∃ f : torsion G N ⟶ Gm (Spec (CommRingCat.of O)), IsCharTors G N f ∧ ∀ w : specO O O ⟶ torsion G N, algebraMap O C (unitOf (w ≫ f) : O) = (κ (w ≫ torsion.ι G N) : C) := by
  intro C _ _ _ v O _ _ hv G _ _ N hN hfin hflat
  have hinj := hv.hom_inj
  have : IsDomain O := hinj.isDomain _
  have := ValuationRing.of_integers v hv
  have := hv.isFractionRing
  have : IsIntegrallyClosed O := inferInstance
  obtain ⟨A, _, _, _, _, ⟨e⟩⟩ := exists_finite_free (torsion G N)
  have hred := isReduced_torsion_geometric_fibre O C G N (Nat.cast_ne_zero.2 (by omega)) hfin
  have h0 : IsIso (specO O C ◁ e.hom).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O C ◁ e.hom)))
  have h3 : IsReduced (specO O C ⊗ specO O A).left :=
    isReduced_of_isOpenImmersion (specO O C ◁ e.hom).left
  have h4 : IsReduced (Spec (CommRingCat.of (C ⊗[O] A))) :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O C A).inv _ h3
  have hA : _root_.IsReduced (C ⊗[O] A) := (affine_isReduced_iff _).mp h4

  have hint : ∀ x : A →ₐ[O] C, ∃ ψ : A →ₐ[O] O, ∀ a, algebraMap O C (ψ a) = x a := fun x => by
    have h : ∀ a, ∃ y, algebraMap O C y = x a := fun a =>
      IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := O) a).map x)
    choose g hg using h
    exact ⟨{ toFun := g
             map_one' := hinj (by simp [hg])
             map_mul' := fun a b => hinj (by simp [hg])
             map_zero' := hinj (by simp [hg])
             map_add' := fun a b => hinj (by simp [hg])
             commutes' := fun r => hinj (by simp [hg]) }, hg⟩
  choose σ hσ using hint
  have hσu : ∀ (x : A →ₐ[O] C) (ψ : A →ₐ[O] O), (∀ a, algebraMap O C (ψ a) = x a) → σ x = ψ :=
    fun x ψ h => AlgHom.ext fun a => hinj ((hσ x a).trans (h a).symm)
  have hsep : ∀ a b : A, (∀ x : A →ₐ[O] C, x a = x b) → a = b := fun a b h =>
    sub_eq_zero.1 (FlatPoints.eq_zero_of_forall_point O C hinj A _ fun x => by
      rw [map_sub, h, sub_self])
  refine ⟨fun f f' h => ?_, fun κ hκ => ?_⟩
  · rw [← cancel_epi e.hom]
    refine unitOf_bijective.1 (Units.ext (hsep _ _ fun x => ?_))
    rw [← hσ, ← hσ, ← unitOf_ptMap, ← unitOf_ptMap, ← Category.assoc, h, Category.assoc]
  let j : specO O A ⟶ G := e.hom ≫ torsion.ι G N
  have hj : j ^ N = 1 := by rw [← MonObj.comp_pow, torsionι_pow, comp_one]
  have hp : ∀ {T} (t : T ⟶ specO O A), (t ≫ j) ^ N = 1 := fun t => by
    rw [← MonObj.comp_pow, hj, comp_one]
  have hjm : ∀ {T} (s t : T ⟶ specO O A), s ≫ j = t ≫ j → s = t := fun s t h =>
    (cancel_mono e.hom).1 (torsion_hom_ext (by simpa [j] using h))
  have hl : ∀ {T} (s : T ⟶ G), s ^ N = 1 → ∃ t : T ⟶ specO O A, t ≫ j = s := fun s hs =>
    ⟨torsionLift s hs ≫ e.inv, by simp [j, torsionLift_ι]⟩
  let i₁ : A →ₐ[O] A ⊗[O] A := Algebra.TensorProduct.includeLeft
  let i₂ : A →ₐ[O] A ⊗[O] A := Algebra.TensorProduct.includeRight
  obtain ⟨d, hd⟩ := hl ((ptMap i₁ ≫ j) * (ptMap i₂ ≫ j)) (by rw [mul_pow, hp, hp, _root_.mul_one])
  obtain ⟨Δ, rfl⟩ := exists_ptMap d
  obtain ⟨d, hε⟩ := hl (1 : specO O O ⟶ G) (one_pow N)
  obtain ⟨ε, rfl⟩ := exists_ptMap d
  let k : (A →ₐ[O] C) → Cˣ := fun x => κ (ptMap (σ x) ≫ j)
  have hk : ∀ x y : A →ₐ[O] C, k ((Algebra.TensorProduct.lift x y
      (fun _ _ => Commute.all _ _)).comp Δ) = k x * k y := fun x y => by
    have h1 : σ ((Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)).comp Δ) =
        (Algebra.TensorProduct.lift (σ x) (σ y) (fun _ _ => Commute.all _ _)).comp Δ := by
      refine hσu _ _ fun a => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply]
      generalize Δ a = t
      induction t with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul a b => simp only [Algebra.TensorProduct.lift_tmul, map_mul, hσ]
    simp only [k]
    rw [h1, ← ptMap_comp_ptMap, Category.assoc, hd, comp_mul, ← Category.assoc _ _ j,
      ← Category.assoc _ _ j, ptMap_comp_ptMap, ptMap_comp_ptMap, Algebra.TensorProduct.lift_comp_includeLeft,
      Algebra.TensorProduct.lift_comp_includeRight']
    exact hκ _ _ (hp _) (hp _)
  have hk1 : k ((Algebra.ofId O C).comp ε) = 1 := by
    have h1 : σ ((Algebra.ofId O C).comp ε) = ε := hσu _ _ fun a => rfl
    have h2 := hκ 1 1 (one_pow N) (one_pow N)
    rw [_root_.mul_one] at h2
    simp only [k]
    rw [h1, hε]
    exact left_eq_mul.1 h2
  obtain ⟨b, hb⟩ := GlobalTheory.exists_eval_eq_of_multiplicative_on_points O C A hA Δ ε (fun x => k x)
    (fun x y => by rw [hk, Units.val_mul]) (by rw [hk1, Units.val_one])
  obtain ⟨b', hb'⟩ := GlobalTheory.exists_eval_eq_of_multiplicative_on_points O C A hA Δ ε (fun x => ((k x)⁻¹ : Cˣ))
    (fun x y => by rw [hk, mul_inv, Units.val_mul]) (by rw [hk1, inv_one, Units.val_one])
  have hbb : b * b' = 1 := hsep _ _ fun x => by
    rw [map_mul, hb, hb', map_one, Units.mul_inv]
  obtain ⟨f₀, hf₀⟩ := (unitOf_bijective (O := O) (R := A)).2 (Units.mkOfMulEqOne b b' hbb)
  have hf : (unitOf f₀ : A) = b := by rw [hf₀]; rfl
  have hΔ : Δ b = i₁ b * i₂ b := by
    have : Module.Flat O C := IsLocalization.flat C (nonZeroDivisors O)
    refine sub_eq_zero.1 (TorsionCharacterExt.tensor_eq_zero_of_forall_pair O C hinj A _
      (fun x y => ?_) ?_)
    · have h := hb ((Algebra.TensorProduct.lift x y (fun _ _ => Commute.all _ _)).comp Δ)
      rw [hk, AlgHom.comp_apply, Units.val_mul, ← hb, ← hb] at h
      rw [map_sub, h]
      simp [i₁, i₂]
    · exact (IsLocalization.bijective_linearMap_mul' (nonZeroDivisors O) C).1
  have hmul : ptMap Δ ≫ f₀ = (ptMap i₁ ≫ f₀) * (ptMap i₂ ≫ f₀) := by
    refine unitOf_bijective.1 (Units.ext ?_)
    rw [unitOf_mul, Units.val_mul, unitOf_ptMap, unitOf_ptMap, unitOf_ptMap, hf, hΔ]
  refine ⟨e.inv ≫ f₀, fun T x y z h => ?_, fun w => ?_⟩
  · obtain ⟨t, ht₁, ht₂⟩ := TorsionCharacterExt.exists_pair (x ≫ e.inv) (y ≫ e.inv)
    have hz : z ≫ e.inv = t ≫ ptMap Δ := hjm _ _ (by
      rw [Category.assoc t, hd, comp_mul, ← Category.assoc t, ← Category.assoc t, ht₁, ht₂]
      simpa [j] using h)
    rw [← Category.assoc, hz, Category.assoc, hmul, comp_mul, ← Category.assoc t,
      ← Category.assoc t, ht₁, ht₂, Category.assoc, Category.assoc]
  · obtain ⟨ψ, hψ⟩ := exists_ptMap (w ≫ e.inv)
    have h1 : σ ((Algebra.ofId O C).comp ψ) = ψ := hσu _ _ fun a => rfl
    have h2 := hb ((Algebra.ofId O C).comp ψ)
    simp only [k] at h2
    rw [h1, ← hψ] at h2
    rw [← Category.assoc, hψ, unitOf_ptMap, hf]
    simpa [j] using h2

end GlobalTheory
end

