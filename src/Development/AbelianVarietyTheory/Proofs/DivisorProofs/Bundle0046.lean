module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjPiQuotPowKerEq
section
open scoped TensorProduct
open TensorProduct

namespace GlobalTheory

theorem exists_surj_pi_quot_pow_ker_eq {A M : Type} [CommRing A] [IsDedekindDomain A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Projective A M] (P : Ideal A) :
    P.IsMaximal → ∀ (r d : ℕ), Module.finrank A M = d →
      ∃ g : M →ₗ[A] (Fin d → A ⧸ P ^ r), Function.Surjective g ∧
        ∀ x, g x = 0 ↔ x ∈ (P ^ r) • (⊤ : Submodule A M) := by
  intro hP r d hd
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨0, ?_, ?_⟩
    · intro y
      refine ⟨0, ?_⟩
      funext i
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y i)
      rw [← ha]
      exact (Ideal.Quotient.eq_zero_iff_mem.2 (by simp)).symm
    · intro x
      simp
  haveI : P.IsPrime := hP.isPrime
  have hPr : P ^ r ≠ ⊤ := by
    intro h
    exact hP.ne_top (eq_top_iff.mpr (h ▸ Ideal.pow_le_self hr.ne'))
  haveI : Nontrivial (A ⧸ P ^ r) := Ideal.Quotient.nontrivial_iff.2 hPr
  let Ap := Localization.AtPrime P
  let φ : Ap →ₐ[A] A ⧸ P ^ r := IsLocalization.liftAlgHom (M := P.primeCompl)
    (f := Ideal.Quotient.mkₐ A (P ^ r)) fun u ↦
      Ideal.Quotient.isUnit_mk_pow_of_notMem _ (Ideal.mem_primeCompl_iff.mp u.prop)
  letI : Algebra Ap (A ⧸ P ^ r) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower A Ap (A ⧸ P ^ r) := IsScalarTower.of_algebraMap_eq fun a ↦ (φ.commutes a).symm

  haveI : Module.Free Ap (Ap ⊗[A] M) := Module.free_of_flat_of_isLocalRing
  have hle := Ideal.primeCompl_le_nonZeroDivisors P
  have hAp : Module.finrank Ap (Ap ⊗[A] M) = d := by
    rw [IsLocalization.finrank_eq Ap P.primeCompl hle,
      IsLocalizedModule.finrank_eq P.primeCompl (TensorProduct.mk A Ap M 1) hle, hd]
  let e0 := TensorProduct.AlgebraTensorModule.cancelBaseChange A Ap (A ⧸ P ^ r) (A ⧸ P ^ r) M
  haveI : Module.Free (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) := Module.Free.of_equiv e0
  haveI : Module.Finite (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) := inferInstance
  have hB : Module.finrank (A ⧸ P ^ r) ((A ⧸ P ^ r) ⊗[A] M) = d := by
    rw [← e0.finrank_eq, Module.finrank_baseChange, hAp]
  let e : (A ⧸ P ^ r) ⊗[A] M ≃ₗ[A ⧸ P ^ r] (Fin d → A ⧸ P ^ r) :=
    (Module.finBasisOfFinrankEq _ _ hB).equivFun
  let g : M →ₗ[A] (Fin d → A ⧸ P ^ r) :=
    (e.restrictScalars A).toLinearMap ∘ₗ TensorProduct.mk A (A ⧸ P ^ r) M 1
  refine ⟨g, ?_, ?_⟩
  · exact e.surjective.comp (TensorProduct.mk_surjective A M (A ⧸ P ^ r) Ideal.Quotient.mk_surjective)
  · intro x
    have h1 : g x = 0 ↔ (1 : A ⧸ P ^ r) ⊗ₜ[A] x = 0 := by
      simp [g, e.map_eq_zero_iff]
    rw [h1, ← (quotTensorEquivQuotSMul M (P ^ r)).map_eq_zero_iff]
    have h2 : (1 : A ⧸ P ^ r) = Ideal.Quotient.mk (P ^ r) 1 := rfl
    rw [h2, quotTensorEquivQuotSMul_mk_tmul, one_smul, Submodule.Quotient.mk_eq_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectivePiAdjoinRootKerEqRange
section
open Polynomial

namespace GlobalTheory

theorem exists_equiv_pi_adjoinRoot_of_aeval_eq_zero (F : Type) [Field F] (Q : Type) [AddCommGroup Q]
    [Module F Q] [FiniteDimensional F Q] (g : Module.End F Q) (f : F[X]) [Fact (Irreducible f)]
    (h : aeval g f = 0) :
    ∃ (t : ℕ) (e : Q ≃ₗ[F] (Fin t → AdjoinRoot f)),
      (∀ v, e (g v) = AdjoinRoot.root f • e v) ∧ Module.finrank F Q = f.natDegree * t := by
  have hf : f ≠ 0 := (Fact.out : Irreducible f).ne_zero
  let φ : AdjoinRoot f →+* Module.End F Q :=
    Ideal.Quotient.lift (Ideal.span {f}) (aeval g : F[X] →ₐ[F] Module.End F Q).toRingHom (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [h])
  have hφ : ∀ p : F[X], φ (AdjoinRoot.mk f p) = aeval g p := fun p => rfl
  letI : Module (AdjoinRoot f) Q := Module.compHom Q φ
  have hs : ∀ (a : AdjoinRoot f) (v : Q), a • v = φ a v := fun _ _ => rfl
  haveI : IsScalarTower F (AdjoinRoot f) Q := ⟨fun c a v => by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hs, hs, AdjoinRoot.smul_mk, hφ, hφ]
    simp⟩
  haveI : Module.Finite (AdjoinRoot f) Q := Module.Finite.of_restrictScalars_finite F _ _
  refine ⟨Module.finrank (AdjoinRoot f) Q,
    (Module.finBasis (AdjoinRoot f) Q).equivFun.restrictScalars F, fun v => ?_, ?_⟩
  · have : g v = AdjoinRoot.root f • v := by
      rw [hs, ← AdjoinRoot.mk_X, hφ]; simp
    rw [this]
    exact map_smul (Module.finBasis (AdjoinRoot f) Q).equivFun _ _
  · rw [← Module.finrank_mul_finrank F (AdjoinRoot f) Q, (AdjoinRoot.powerBasis hf).finrank,
      AdjoinRoot.powerBasis_dim]

theorem exists_surjective_pi_adjoinRoot_ker_eq_range (F : Type) [Field F] (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X])
    [Fact (Irreducible f)] :
    ∃ (t : ℕ) (π : V →ₗ[F] (Fin t → AdjoinRoot f)), Function.Surjective π ∧
      (∀ v, π (g v) = AdjoinRoot.root f • π v) ∧
      LinearMap.ker π = LinearMap.range (aeval g f) ∧
      Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t := by
  set N : Submodule F V := LinearMap.range (aeval g f) with hN
  have hg : N ≤ N.comap g := by
    rintro _ ⟨v, rfl⟩
    refine ⟨g v, ?_⟩
    have h1 : aeval g f * g = g * aeval g f := by
      have : aeval g (f * X) = aeval g (X * f) := by rw [mul_comm]
      simpa using this
    exact congrArg (fun u : Module.End F V => u v) h1
  let gq : Module.End F (V ⧸ N) := N.mapQ N g hg
  have hq : ∀ v, gq (N.mkQ v) = N.mkQ (g v) := fun v => rfl
  have hp : ∀ (p : F[X]) (v : V), aeval gq p (N.mkQ v) = N.mkQ (aeval g p v) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a => intro v; simp [Module.algebraMap_end_apply]
    | add p q hp hq => intro v; simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
    | monomial n a ih =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval g), aeval_X, aeval_X,
        Module.End.mul_apply, Module.End.mul_apply, hq, ih]
  have h0 : aeval gq f = 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := N.mkQ_surjective x
    rw [hp]
    exact (Submodule.Quotient.mk_eq_zero N).2 ⟨v, rfl⟩
  obtain ⟨t, e, he, hd⟩ := exists_equiv_pi_adjoinRoot_of_aeval_eq_zero F (V ⧸ N) gq f h0
  refine ⟨t, e.toLinearMap ∘ₗ N.mkQ, e.surjective.comp N.mkQ_surjective, fun v => ?_, ?_, ?_⟩
  · have := he (N.mkQ v)
    rw [hq] at this
    exact this
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]
  · have h1 := LinearMap.finrank_range_add_finrank_ker (aeval g f)
    have h2 := Submodule.finrank_quotient_add_finrank N
    rw [← hN] at h1
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfFlatOfIsPushout
section
open CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.FlatFibreProduct

open TensorProduct

theorem injective_exact_of_isBaseChange {R R' M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] [Module.Flat R R']
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [Module R M₁] [Module R M₂] [Module R M₃]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R N₁] [Module R N₂] [Module R N₃]
    [Module R' N₁] [Module R' N₂] [Module R' N₃]
    [IsScalarTower R R' N₁] [IsScalarTower R R' N₂] [IsScalarTower R R' N₃]
    {ι₁ : M₁ →ₗ[R] N₁} {ι₂ : M₂ →ₗ[R] N₂} {ι₃ : M₃ →ₗ[R] N₃}
    (h₁ : IsBaseChange R' ι₁) (h₂ : IsBaseChange R' ι₂) (h₃ : IsBaseChange R' ι₃)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (f' : N₁ →ₗ[R'] N₂) (g' : N₂ →ₗ[R'] N₃)
    (hf : ∀ m, f' (ι₁ m) = ι₂ (f m)) (hg : ∀ m, g' (ι₂ m) = ι₃ (g m))
    (hinj : Function.Injective f) (hex : Function.Exact f g) :
    Function.Injective f' ∧ Function.Exact f' g' := by
  have k₁ : ∀ x, h₂.equiv (f.lTensor R' x) = f' (h₁.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [IsBaseChange.equiv_tmul, hf]
    | add x y hx hy => simp_all
  have k₂ : ∀ x, h₃.equiv (g.lTensor R' x) = g' (h₂.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [IsBaseChange.equiv_tmul, hg]
    | add x y hx hy => simp_all
  have inj := Module.Flat.lTensor_preserves_injective_linearMap (M := R') f hinj
  have ex := Module.Flat.lTensor_exact R' hex
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · apply h₁.equiv.symm.injective
    apply inj
    apply h₂.equiv.injective
    rw [k₁, k₁]
    simpa using hab
  · obtain ⟨x, rfl⟩ := h₂.equiv.surjective y
    rw [← k₂, LinearEquiv.map_eq_zero_iff, ex x]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨h₁.equiv z, (k₁ z).symm⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := h₁.equiv.surjective z
      refine ⟨w, h₂.equiv.injective ?_⟩
      rw [k₁, hz]

theorem exists_unique_of_flat_of_isPushout : ∀ {A B C D A' B' C' D' : CommRingCat.{0}} (fB : A ⟶ B) (fC : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D) (e : A ⟶ A') (eB : B ⟶ B') (eC : C ⟶ C') (eD : D ⟶ D') (aB : A' ⟶ B') (aC : A' ⟶ C') (u' : B' ⟶ D') (v' : C' ⟶ D'), e.hom.Flat → IsPushout e fB aB eB → IsPushout e fC aC eC → IsPushout e (fB ≫ u) (aB ≫ u') eD → eB ≫ u' = u ≫ eD → eC ≫ v' = v ≫ eD → aB ≫ u' = aC ≫ v' → fB ≫ u = fC ≫ v → (∀ (b : B) (c : C), u.hom b = v.hom c → ∃! a : A, fB.hom a = b ∧ fC.hom a = c) → ∀ (b' : B') (c' : C'), u'.hom b' = v'.hom c' → ∃! a' : A', aB.hom a' = b' ∧ aC.hom a' = c' := by
  intro A B C D A' B' C' D' fB fC u v e eB eC eD aB aC u' v' hfl hB hC hD h1 h2 h3 h4 hfib
  letI : Algebra A A' := e.hom.toAlgebra
  letI : Algebra A B := fB.hom.toAlgebra
  letI : Algebra A C := fC.hom.toAlgebra
  letI : Algebra A D := (fB ≫ u).hom.toAlgebra
  letI : Algebra A' B' := aB.hom.toAlgebra
  letI : Algebra A' C' := aC.hom.toAlgebra
  letI : Algebra A' D' := (aB ≫ u').hom.toAlgebra
  letI : Algebra B B' := eB.hom.toAlgebra
  letI : Algebra C C' := eC.hom.toAlgebra
  letI : Algebra D D' := eD.hom.toAlgebra
  letI : Algebra A B' := (e ≫ aB).hom.toAlgebra
  letI : Algebra A C' := (e ≫ aC).hom.toAlgebra
  letI : Algebra A D' := (e ≫ aB ≫ u').hom.toAlgebra
  haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A A' D' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hB.w)
  haveI : IsScalarTower A C C' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hC.w)
  haveI : IsScalarTower A D D' :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun φ => φ.hom x) hD.w)
  haveI : Module.Flat A A' := hfl
  have PB : Algebra.IsPushout A A' B B' := CommRingCat.isPushout_iff_isPushout.mp hB
  have PC : Algebra.IsPushout A A' C C' := CommRingCat.isPushout_iff_isPushout.mp hC
  have PD : Algebra.IsPushout A A' D D' := CommRingCat.isPushout_iff_isPushout.mp hD
  have hb₁ : IsBaseChange A' (Algebra.linearMap A A') := IsBaseChange.linearMap A A'
  have hb₂ := IsBaseChange.prodMap _ _ PB.out PC.out
  have hb₃ := PD.out
  let uL : B →ₗ[A] D :=
    { toFun := u.hom, map_add' := map_add _
      map_smul' := fun a b => by
        change u.hom (fB.hom a * b) = (fB ≫ u).hom a * u.hom b
        rw [map_mul]; rfl }
  let vL : C →ₗ[A] D :=
    { toFun := v.hom, map_add' := map_add _
      map_smul' := fun a c => by
        change v.hom (fC.hom a * c) = (fB ≫ u).hom a * v.hom c
        rw [map_mul, h4]; rfl }
  let u'L : B' →ₗ[A'] D' :=
    { toFun := u'.hom, map_add' := map_add _
      map_smul' := fun a b => by
        change u'.hom (aB.hom a * b) = (aB ≫ u').hom a * u'.hom b
        rw [map_mul]; rfl }
  let v'L : C' →ₗ[A'] D' :=
    { toFun := v'.hom, map_add' := map_add _
      map_smul' := fun a c => by
        change v'.hom (aC.hom a * c) = (aB ≫ u').hom a * v'.hom c
        rw [map_mul, h3]; rfl }
  let f : A →ₗ[A] B × C := (Algebra.linearMap A B).prod (Algebra.linearMap A C)
  let g : B × C →ₗ[A] D := uL.coprod (-vL)
  let f' : A' →ₗ[A'] B' × C' := (Algebra.linearMap A' B').prod (Algebra.linearMap A' C')
  let g' : B' × C' →ₗ[A'] D' := u'L.coprod (-v'L)
  have hf : ∀ m, f' (Algebra.linearMap A A' m) =
      ((IsScalarTower.toAlgHom A B B').toLinearMap.prodMap
        (IsScalarTower.toAlgHom A C C').toLinearMap) (f m) := by
    intro m
    refine Prod.ext ?_ ?_
    · exact congrArg (fun φ => φ.hom m) hB.w
    · exact congrArg (fun φ => φ.hom m) hC.w
  have hg : ∀ m, g' (((IsScalarTower.toAlgHom A B B').toLinearMap.prodMap
        (IsScalarTower.toAlgHom A C C').toLinearMap) m) =
      (IsScalarTower.toAlgHom A D D').toLinearMap (g m) := by
    rintro ⟨b, c⟩
    change u'.hom (eB.hom b) + -v'.hom (eC.hom c) = eD.hom (u.hom b + -v.hom c)
    have e₁ : u'.hom (eB.hom b) = eD.hom (u.hom b) := congrArg (fun φ => φ.hom b) h1
    have e₂ : v'.hom (eC.hom c) = eD.hom (v.hom c) := congrArg (fun φ => φ.hom c) h2
    rw [map_add (f := _), map_neg, e₁, e₂]
  have hinj : Function.Injective f := by
    intro a₁ a₂ h
    have hb : fB.hom a₁ = fB.hom a₂ := congrArg Prod.fst h
    have hc : fC.hom a₁ = fC.hom a₂ := congrArg Prod.snd h
    obtain ⟨a, -, ha⟩ := hfib (fB.hom a₁) (fC.hom a₁)
      (by simpa using congrArg (fun φ => φ.hom a₁) h4)
    exact (ha a₁ ⟨rfl, rfl⟩).trans (ha a₂ ⟨hb.symm, hc.symm⟩).symm
  have hex : Function.Exact f g := by
    rintro ⟨b, c⟩
    change u.hom b + -v.hom c = 0 ↔ _
    rw [← sub_eq_add_neg, sub_eq_zero]
    constructor
    · intro h
      obtain ⟨a, ⟨ha₁, ha₂⟩, -⟩ := hfib b c h
      exact ⟨a, Prod.ext ha₁ ha₂⟩
    · rintro ⟨a, ha⟩
      have hb : fB.hom a = b := congrArg Prod.fst ha
      have hc : fC.hom a = c := congrArg Prod.snd ha
      subst hb hc
      simpa using congrArg (fun φ => φ.hom a) h4
  obtain ⟨inj', ex'⟩ := injective_exact_of_isBaseChange hb₁ hb₂ hb₃ f g f' g' hf hg hinj hex
  intro b' c' h
  have h0 : g' (b', c') = 0 := by
    change u'.hom b' + -v'.hom c' = 0
    rw [h, add_neg_cancel]
  obtain ⟨a', ha'⟩ := (ex' (b', c')).1 h0
  refine ⟨a', ⟨congrArg Prod.fst ha', congrArg Prod.snd ha'⟩, fun y hy => inj' ?_⟩
  rw [ha']
  exact Prod.ext hy.1 hy.2

end GlobalTheory.FlatFibreProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitApproximationAdicCompletion
section
namespace GlobalTheory

theorem finite_alg_hom_ker_coker_killed_of_onto_mod_ideal
    (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M]
    [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N]
    (φ : M →ₐ[A] N) :
    (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) →
    (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) →
    ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧
      ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by
  intro h1 h2

  set R : Submodule A N := LinearMap.range φ.toLinearMap with hR
  have hQ : (⊤ : Submodule A (N ⧸ R)) ≤ J • ⊤ := by
    rintro q -
    obtain ⟨y, rfl⟩ := R.mkQ_surjective q
    obtain ⟨t, ht⟩ := h1 y
    have hz : y - φ t ∈ J • (⊤ : Submodule A N) := by
      rw [Ideal.smul_top_eq_map]; exact ht
    have hm : R.mkQ (y - φ t) ∈ J • (⊤ : Submodule A (N ⧸ R)) := by
      have := Submodule.mem_map_of_mem (f := R.mkQ) hz
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
      exact this
    have he : R.mkQ (y - φ t) = R.mkQ y := by
      rw [map_sub, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨t, rfl⟩
    rwa [he] at hm
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J
    (⊤ : Submodule A (N ⧸ R)) (Module.Finite.fg_top) hQ
  have hrR : ∀ y : N, r • y ∈ R := by
    intro y
    have := hr (R.mkQ y) trivial
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

  set K : Submodule A M := LinearMap.ker φ.toLinearMap with hK
  have hKfg : K.FG := IsNoetherian.noetherian K
  have hKle : K ≤ J • K := by
    intro t ht
    have hφ : φ t = 0 := ht
    have hmem : t ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule A M) := by
      rw [Submodule.mem_iInf]
      intro i
      rw [Ideal.smul_top_eq_map]
      exact h2 i t (by rw [hφ]; exact Ideal.zero_mem _)
    obtain ⟨⟨s, hs⟩, hst⟩ := (J.mem_iInf_smul_pow_eq_bot_iff t).1 hmem
    simp only at hst
    rw [← hst]
    exact Submodule.smul_mem_smul hs ht
  obtain ⟨u, hu1, hu⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J K hKfg hKle
  refine ⟨r * u, ?_, ?_, ?_⟩
  · have : r * u - 1 = r * (u - 1) + (r - 1) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left r hu1) hr1
  · intro y
    rw [← Algebra.smul_def, mul_comm, mul_smul]
    obtain ⟨t, ht⟩ := hrR y
    exact ⟨u • t, by
      change φ (u • t) = u • (r • y)
      rw [map_smul]
      congr 1⟩
  · intro t ht
    rw [← Algebra.smul_def, mul_smul, hu t ht, smul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationRingDominatingSpecialization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem exists_valuationRing_of_specializes (X : Scheme.{0}) (x' x : X) (h : x' ⤳ x) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V)
      (g : Spec (CommRingCat.of V) ⟶ X),
      g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by
  let φ : X.presheaf.stalk x ⟶ X.residueField x' :=
    X.presheaf.stalkSpecializes h ≫ X.residue x'
  obtain ⟨A, hA, hA_local⟩ := IsLocalRing.exists_factor_valuationRing φ.hom
  let ψ : X.presheaf.stalk x ⟶ .of A := CommRingCat.ofHom (φ.hom.codRestrict _ hA)
  have w : X.fromSpecResidueField x' =
      Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) ≫
        Spec.map ψ ≫ X.fromSpecStalk x := by
    rw [Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨A, inferInstance, inferInstance, inferInstance, Spec.map ψ ≫ X.fromSpecStalk x, ?_, ?_⟩
  · simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have : Spec.map ψ (IsLocalRing.closedPoint A) =
        IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
    rw [this, X.fromSpecStalk_closedPoint]
  · have h1 : Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x')))
        (IsLocalRing.closedPoint (X.residueField x')) = (⊥ : PrimeSpectrum A) := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap A (X.residueField x'))
        (IsLocalRing.maximalIdeal (X.residueField x')) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ Subtype.val_injective
    rw [← h1, ← Scheme.Hom.comp_apply, ← w, Scheme.fromSpecResidueField_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringComplexOverPrime
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

theorem exists_valuationSubring_complex_over_prime :
    ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)),
      ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  intro F _ w
  set R := w.valuationSubringAtPrime F with hR
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing
    ((algebraMap F ℂ).comp R.subtype)
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hV ⟨x, hx⟩⟩⟩
  by_contra hxR
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxR R.zero_mem
  have hinv : x⁻¹ ∈ R := (R.mem_or_inv_mem x).resolve_left hxR
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hu : IsUnit ((((algebraMap F ℂ).comp R.subtype).codRestrict V.toSubring hV) ⟨x⁻¹, hinv⟩) := by
    refine IsUnit.of_mul_eq_one ⟨(x : ℂ), hx⟩ ?_
    apply Subtype.ext
    change ((x⁻¹ : F) : ℂ) * (x : ℂ) = 1
    rw [IntermediateField.coe_inv, inv_mul_cancel₀ hx0']
  have hu' : IsUnit (⟨x⁻¹, hinv⟩ : R) := hloc.map_nonunit _ hu
  obtain ⟨y, hy⟩ := hu'.exists_right_inv
  have hy' : x⁻¹ * (y : F) = 1 := congrArg Subtype.val hy
  have : x = (y : F) := by
    have h := congrArg (x * ·) hy'
    simp only [← mul_assoc, mul_inv_cancel₀ hx0, one_mul, mul_one] at h
    exact h.symm
  exact hxR (this ▸ y.2)

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreFiniteCard
section
namespace GlobalTheory.FibreEquivalence

noncomputable def fibreEquiv {H : Type} [Group H] (D C : Subgroup H) (h : D ≤ C) (z : H ⧸ C) :
    { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } ≃ C ⧸ D.subgroupOf C :=
  have key : ∀ y : H ⧸ D,
      (Subgroup.quotientEquivProdOfLE h y).1 = Subgroup.quotientMapOfLE h y := by
    intro y
    induction y using QuotientGroup.induction_on
    rfl
  { toFun := fun y => (Subgroup.quotientEquivProdOfLE h y.1).2
    invFun := fun b => ⟨(Subgroup.quotientEquivProdOfLE h).symm (z, b), by
      rw [← key, Equiv.apply_symm_apply]⟩
    left_inv := fun y => by
      apply Subtype.ext
      change (Subgroup.quotientEquivProdOfLE h).symm
        (z, (Subgroup.quotientEquivProdOfLE h y.1).2) = y.1
      rw [Equiv.symm_apply_eq]
      exact Prod.ext (by rw [key]; exact y.2.symm) rfl
    right_inv := fun b => by
      change (Subgroup.quotientEquivProdOfLE h
        ((Subgroup.quotientEquivProdOfLE h).symm (z, b))).2 = b
      rw [Equiv.apply_symm_apply] }

theorem fibre_finite_card : ∀ {H : Type} [inst : Group H] (D C : Subgroup H) (h : D ≤ C), Subgroup.relIndex D C ≠ (0 : ℕ) → ∀ (z : H ⧸ C), Finite { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } ∧ Nat.card { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } = Subgroup.relIndex D C := by
  intro H _ D C h hD z
  have hcard : Nat.card { y : H ⧸ D // Subgroup.quotientMapOfLE h y = z } = Subgroup.relIndex D C := by
    rw [Nat.card_congr (fibreEquiv D C h z)]
    rfl
  exact ⟨Nat.finite_of_card_ne_zero (by rw [hcard]; exact hD), hcard⟩

end GlobalTheory.FibreEquivalence
end

