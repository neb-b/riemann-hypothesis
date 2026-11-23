module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0108
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NegOneSmulCancel
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

section BaseChange

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  (R' : Type) [CommRing R'] [Algebra R R']

@[reducible] def bcF : C ⥤ CommAlgCat.{0} R' where
  obj T := CommAlgCat.of R' (R' ⊗[R] F.obj T)
  map φ := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ))
  map_id T := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_id F T b))
  map_comp φ ψ := CommAlgCat.hom_ext (Algebra.TensorProduct.ext' fun a b ↦
    congrArg (fun y ↦ a ⊗ₜ[R] y) (mp_comp F φ ψ b))

def bcM : BC F (bcF F R') where
  α T := (Algebra.TensorProduct.includeRight : F.obj T →ₐ[R] R' ⊗[R] F.obj T).toRingHom
  naturality _ _ := rfl
  smul T r b := by
    change (1 : R') ⊗ₜ[R] (r • b) = algebraMap R R' r • ((1 : R') ⊗ₜ[R] b)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  bij T := ⟨LinearEquiv.refl _ _, fun _ ↦ rfl⟩

variable {R'} {M : Type} [AddCommGroup M] [Module R M] (j : M →ₗ[R] R')

def ev0 : M ⊗[R] C0 F →ₗ[R] ∀ T : C, R' ⊗[R] F.obj T :=
  LinearMap.pi fun T ↦ TensorProduct.map j (LinearMap.proj T)

def ev1 : M ⊗[R] C1 F →ₗ[R] ∀ (T T' : C) (_ : T ⟶ T'), R' ⊗[R] F.obj T' :=
  LinearMap.pi fun T ↦ LinearMap.pi fun T' ↦ LinearMap.pi fun φ ↦
    TensorProduct.map j ((LinearMap.proj φ) ∘ₗ (LinearMap.proj T') ∘ₗ (LinearMap.proj T))

theorem evaluation_zero_tmul (n : M) (g : C0 F) (T : C) : ev0 F j (n ⊗ₜ g) T = j n ⊗ₜ g T := rfl

theorem realTensorEvalAlgHom_tmul (n : M) (f : C1 F) {T T' : C} (φ : T ⟶ T') :
    ev1 F j (n ⊗ₜ f) T T' φ = j n ⊗ₜ f T T' φ := rfl

theorem evaluation_coboundary_zero_tensor (y : M ⊗[R] C0 F) :
    ev1 F j ((d0 F).lTensor M y) = d0 (bcF F R') (ev0 F j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul n g =>
    funext T T' φ
    show ev1 F j (n ⊗ₜ d0 F g) T T' φ = ev0 F j (n ⊗ₜ g) T' - mp (bcF F R') φ (ev0 F j (n ⊗ₜ g) T)
    rw [realTensorEvalAlgHom_tmul, evaluation_zero_tmul, evaluation_zero_tmul, amitsur_d0_apply]
    show j n ⊗ₜ (g T' - mp F φ (g T)) =
      j n ⊗ₜ g T' - (Algebra.TensorProduct.map (AlgHom.id R' R') (mp F φ)) (j n ⊗ₜ g T)
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.tmul_sub]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_cocycle (e : R' ⊗[R] H1 F ≃ₗ[R'] H1 (bcF F R'))
    (he : ∀ c, e (1 ⊗ₜ c) = (bcM F R').coef.pull1 c) (t : M ⊗[R] Z1 F) :
    ∃ z : Z1 (bcF F R'), z.1 = ev1 F j ((Z1 F).subtype.lTensor M t) ∧
      H1.mk (bcF F R') z = e (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | tmul n c =>
    refine ⟨j n • (bcM F R').coef.pullbackOneCocycle c, ?_, ?_⟩
    · funext T T' φ
      show j n • ((1 : R') ⊗ₜ[R] (c.1 T T' φ)) = ev1 F j (n ⊗ₜ c.1) T T' φ
      rw [realTensorEvalAlgHom_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    · rw [map_smul, ← CoefMap.pullCohomologyOne_class]
      show j n • (bcM F R').coef.pull1 (H1.mk F c) = e (j n ⊗ₜ H1.mk F c)
      rw [← he, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨z1, h1, h1'⟩ := hx
    obtain ⟨z2, h2, h2'⟩ := hy
    refine ⟨z1 + z2, ?_, ?_⟩
    · simp only [Submodule.coe_add, h1, h2, map_add (f := _)]
    · simp only [map_add (f := _), h1', h2']

theorem lTensor_iotaQ_injective_of_retract (h : H1CommutesBaseChange F) (p : R' →ₗ[R] M) (hp : p ∘ₗ j = LinearMap.id) :
    Function.Injective ((iotaQ F).lTensor M) := by
  obtain ⟨e, he⟩ := h R' (bcF F R') (bcM F R')
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective M (H1.mk_surjective F) x
  have hcomp : iotaQ F ∘ₗ H1.mk F = (LinearMap.range (d0 F)).mkQ ∘ₗ (Z1 F).subtype :=
    LinearMap.ext fun f => iotaQ_mk F f
  have hx' : ((LinearMap.range (d0 F)).mkQ).lTensor M ((Z1 F).subtype.lTensor M t) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, ← hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨y, hy⟩ := (lTensor_exact M (LinearMap.exact_map_mkQ_range (d0 F))
    (Submodule.mkQ_surjective _) ((Z1 F).subtype.lTensor M t)).1 hx'
  obtain ⟨z, hz1, hz2⟩ := exists_cocycle F j e he t
  have hz0 : H1.mk (bcF F R') z = 0 := by
    apply iotaQ_injective (bcF F R')
    rw [iotaQ_mk, map_zero, Submodule.Quotient.mk_eq_zero, hz1, ← hy, evaluation_coboundary_zero_tensor]
    exact LinearMap.mem_range_self _ _
  have hx0 : j.rTensor (H1 F) ((H1.mk F).lTensor M t) = 0 := by
    rw [← e.map_eq_zero_iff, ← hz2, hz0]
  calc (H1.mk F).lTensor M t = (p ∘ₗ j).rTensor (H1 F) ((H1.mk F).lTensor M t) := by
        rw [hp, LinearMap.rTensor_id_apply]
    _ = p.rTensor (H1 F) (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := LinearMap.rTensor_comp_apply _ _ _ _
    _ = 0 := by rw [hx0, map_zero]

end BaseChange

theorem iotaQ_lTensor_injective (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (h : H1CommutesBaseChange F) (M : Type) [AddCommGroup M] [Module R M] :
    Function.Injective ((iotaQ F).lTensor M) := by
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id R).fromOpposite fun _ _ => Commute.all _ _)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  exact lTensor_iotaQ_injective_of_retract F (TrivSqZeroExt.inrHom R M) h (TrivSqZeroExt.sndHom R M)
    (LinearMap.ext fun m => by simp)

end GlobalTheory.CompanionTheory.WedgeOf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisGroupTransportIsomorphism
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

section GalConj

variable {F Ω F' Ω' : Type} [Field F] [Field Ω] [Algebra F Ω]
  [Field F'] [Field Ω'] [Algebra F' Ω']

def galConjFun (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) :
    Ω' ≃ₐ[F'] Ω' :=
  AlgEquiv.ofRingEquiv (f := E.symm.trans ((σ : Ω ≃+* Ω).trans E)) (fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 : E.symm (algebraMap F' Ω' (e x)) = algebraMap F Ω x := by
      rw [← hE, RingEquiv.symm_apply_apply]
    simp [h1, hE])

theorem galConjFun_apply (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    galConjFun e E hE σ (E x) = E (σ x) := by
  simp [galConjFun]

def galConjHom (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) :
    (Ω ≃ₐ[F] Ω) →* (Ω' ≃ₐ[F'] Ω') where
  toFun := galConjFun e E hE
  map_one' := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    rw [galConjFun_apply]; rfl
  map_mul' σ τ := by
    ext y
    obtain ⟨x, rfl⟩ := E.surjective y
    show galConjFun e E hE (σ * τ) (E x) = galConjFun e E hE σ (galConjFun e E hE τ (E x))
    rw [galConjFun_apply e E hE τ, galConjFun_apply e E hE σ, galConjFun_apply e E hE (σ * τ),
      AlgEquiv.mul_apply]

theorem galConjHom_apply (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) (σ : Ω ≃ₐ[F] Ω) (x : Ω) :
    galConjHom e E hE σ (E x) = E (σ x) :=
  galConjFun_apply e E hE σ x

theorem continuous_galConjHom [Algebra.IsAlgebraic F Ω]
    (e : F ≃+* F') (E : Ω ≃+* Ω')
    (hE : ∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) :
    Continuous (galConjHom e E hE) := by
  refine continuous_of_continuousAt_one _ ?_
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨K', hK', hKs⟩ := hs
  let b := Module.finBasis F' K'
  let T : Set Ω := Set.range fun i => E.symm (b i : Ω')
  let L : IntermediateField F Ω := IntermediateField.adjoin F T
  have hL : FiniteDimensional F L :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨L, hL, fun σ hσ => hKs ?_⟩
  have hfix : ∀ i, galConjHom e E hE σ (b i : Ω') = (b i : Ω') := by
    intro i
    have hmem : E.symm (b i : Ω') ∈ L :=
      IntermediateField.subset_adjoin F T ⟨i, rfl⟩
    have h1 : σ (E.symm (b i : Ω')) = E.symm (b i : Ω') :=
      (IntermediateField.mem_fixingSubgroup_iff L σ).1 hσ _ hmem
    have h2 := galConjHom_apply e E hE σ (E.symm (b i : Ω'))
    rwa [h1, RingEquiv.apply_symm_apply] at h2
  have hlin : ((galConjHom e E hE σ).toAlgHom.comp K'.val).toLinearMap = K'.val.toLinearMap :=
    b.ext fun i => hfix i
  refine (IntermediateField.mem_fixingSubgroup_iff K' _).2 fun x hx => ?_
  exact congrArg (fun f : K' →ₗ[F'] Ω' => f ⟨x, hx⟩) hlin

end GalConj

theorem exists_galContinuousMulEquiv : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω']
    [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'),
    (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) →
    ∃ Φ : G F Ω ≃ₜ* G F' Ω', ∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F' Ω' := IsAlgClosure.isAlgebraic
  have hE' : ∀ x : F', E.symm (algebraMap F' Ω' x) = algebraMap F Ω (e.symm x) := by
    intro x
    rw [RingEquiv.symm_apply_eq, hE, RingEquiv.apply_symm_apply]
  refine ⟨{ toFun := galConjHom e E hE
            invFun := galConjHom e.symm E.symm hE'
            left_inv := ?_
            right_inv := ?_
            map_mul' := map_mul _
            continuous_toFun := continuous_galConjHom e E hE
            continuous_invFun := continuous_galConjHom e.symm E.symm hE' },
    fun σ x => galConjHom_apply e E hE σ x⟩
  · intro σ
    ext x
    have h := galConjHom_apply e.symm E.symm hE' (galConjHom e E hE σ) (E x)
    rw [galConjHom_apply e E hE σ x, RingEquiv.symm_apply_apply,
      RingEquiv.symm_apply_apply] at h
    exact h
  · intro τ
    ext y
    have h := galConjHom_apply e E hE (galConjHom e.symm E.symm hE' τ) (E.symm y)
    rw [galConjHom_apply e.symm E.symm hE' τ y, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply] at h
    exact h

end GlobalTheory.CompanionTheory.PTIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCoverVanishingInduction
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeZig

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem res_cupList {A : C ⥤ CommAlgCat.{0} R} {U V : ObjectProperty C} (h : V ≤ U) {k : ℕ} (l : Fin k → Ch A U 1) :
    resB A h (cupListC (U.ι ⋙ A) l) = cupListC (V.ι ⋙ A) fun j => resB A h (l j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (CH.mulP _).cupC _ (resB A h (cupListC _ fun i => l (Fin.castSucc i))) (resB A h (l (Fin.last k))) = _
    rw [ih]
    rfl

theorem PP_eq {A : C ⥤ CommAlgCat.{0} R} {N : ℕ} {W : Fin N → ObjectProperty C} (b : ∀ α, Ch A (W α) 1)
    {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch A V 2) (k : ℕ) :
    ∃ e : ℤ, e * e = 1 ∧ ∀ i : Idx (k + 1) N, PP b hWV z k i =
      e • cupListC ((capT W i.1).ι ⋙ A) fun j : Fin k => LL b i j.castSucc j.succ := by
  induction k with
  | zero => exact ⟨1, rfl, fun i => (one_smul ℤ _).symm⟩
  | succ k ih =>
    obtain ⟨e, he, h⟩ := ih
    refine ⟨(-1) ^ k * e, ?_, fun i => ?_⟩
    · rw [mul_mul_mul_comm, he, ← mul_pow]; simp
    · change (-1 : ℤ) ^ k • BB b k k (PP b hWV z k) i = _
      have hLL : ∀ j : Fin k, resB A (cap_le W (Fin.last (k + 1)) i) (LL b (fc (Fin.last (k + 1)) i) j.castSucc j.succ) =
          LL b i j.castSucc.castSucc j.castSucc.succ := by
        intro j
        refine res_LL b i _ _ _ _ _ _ (congrArg i.1 ?_) (congrArg i.1 ?_) <;>
        · have := j.2
          apply Fin.ext
          simp only [CrystallineSemistableComparison.Auxff.sa_val, Fin.val_castSucc, Fin.val_last, Fin.val_succ]
          split_ifs <;> omega
      rw [BB_apply, h, map_zsmul, bm_apply, res_cupList, mul_smul]
      simp only [hLL]
      rfl

theorem PP_mem (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (hF : IsFil Φ Fil) {N : ℕ} {W : Fin N → ObjectProperty C}
    (b : ∀ α, Ch Φ.A (W α) 1) {V : ObjectProperty C} (hWV : ∀ α, W α ≤ V) (z : Ch Φ.A V 2)
    (hb1 : ∀ α, b α ∈ Lm (Fil 1) (W α) 1) (k : ℕ) :
    PP b hWV z k ∈ (dfil (W := W) Fil hF.anti).L (k : ℤ) k k := by
  induction k with
  | zero =>
    intro i _ σ
    rw [hF.top _ (by simp)]
    trivial
  | succ k ih =>
    refine Submodule.smul_of_tower_mem _ _ ?_
    intro i _
    refine Lm_cup (a := Fil k) (b := Fil 1) (fun T x y hx hy => hF.mul k 1 T hx (by simpa using hy)) rfl
      (Lm_res (cap_le W _ i) (ih (fc (Fin.last (k + 1)) i) trivial)) (sub_mem (Lm_res _ (hb1 _)) (Lm_res _ (hb1 _)))

theorem capT_eq {N : ℕ} (W : Fin N → ObjectProperty C) {m : ℕ} (i : Fin m → Fin N) :
    capT W i = capS W (Finset.univ.image i) := by
  funext T
  refine propext ⟨fun h α hα => ?_, fun h a => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))⟩
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
  exact h a

theorem KEx (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (hF : IsFil Φ Fil) {N : ℕ} (W : Fin N → ObjectProperty C)
    (hS : ∀ S : Finset (Fin N), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j))
    (r : ℕ) (p q : ℕ) (hq : q ≠ r) : (dfil (W := W) Fil hF.anti).Ex (r : ℤ) p q := by
  have hH : ∀ (i : Idx (p + 1) N) (j : ℕ), j ≠ r → Subsingleton (HU (gr Fil r) (capT W i.1) j) := by
    intro i j hj
    rw [capT_eq]
    exact hS _ ⟨i.1 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ _ _ (by exact_mod_cast hj)
  cases q with
  | zero =>
    intro x hx hd i _ σ
    exact ex_zero (a := (Fil r).res (capT W i.1).ι) (b := (Fil (r + 1)).res (capT W i.1).ι) (hH i 0 hq) (x i)
      (hx i trivial) (hd i trivial) σ
  | succ q =>
    intro x hx hd
    have h := fun i : Idx (p + 1) N =>
      ex_succ (a := (Fil r).res (capT W i.1).ι) (b := (Fil (r + 1)).res (capT W i.1).ι) (hH i (q + 1) hq) (x i)
        (hx i trivial) (hd i trivial)
    choose v hv hv' using h
    exact ⟨v, fun i _ => hv i, fun i _ => hv' i⟩

theorem alg_fin {M : Type*} [AddCommGroup M] {ι : Type} [Fintype ι] (e s : ℤ) (he : e * e = 1) (Cl Pv E : M) (t : ι → M)
    (sg : ι → ℤ) (h1 : Pv = e • Cl) (h2 : Pv = ∑ k, sg k • t k + s • E) :
    Cl - ∑ k, (e * sg k) • t k = (e * s) • E := by
  have h3 : Cl = e • Pv := by rw [h1, smul_smul, he, one_smul]
  rw [h3, h2, smul_add, Finset.smul_sum]
  simp only [smul_smul]
  abel

theorem KV (A : C ⥤ CommAlgCat.{0} R) (n : ℕ) (W : Fin (n + 2) → ObjectProperty C) (p q : ℕ) (h : n + 1 < p) :
    Subsingleton ((KK A W).X p q) := by
  have e : IsEmpty (Idx (p + 1) (n + 2)) := ⟨fun i => by
    have := Fintype.card_le_of_injective _ i.2.injective
    simp only [Fintype.card_fin] at this
    omega⟩
  exact ⟨fun x y => funext fun i => (e.false i).elim⟩

theorem fin_step {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) (n : ℕ)
    (W : Fin (n + 2) → ObjectProperty C) (Cl : Ch Φ.A (capS W Finset.univ) (n + 1))
    (hCl : Cl ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1))
    (c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1))
    (hc : Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι) Cl c)
    (w : ∀ k : Fin (n + 2), Ch Φ.A (capS W (Finset.univ.erase k)) (n + 1))
    (hw : ∀ k, w k ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1))
    (hdw : ∀ k, CH.d _ (n + 1) (w k) ∈ Lm (Fil ((n : ℤ) + 1 + 1)) _ (n + 2))
    (f : Ch Φ.A (capS W Finset.univ) n) (hf : f ∈ Lm (Fil (n : ℤ)) _ n)
    (hEq : Cl - ∑ k, resB Φ.A (capS_univ_le W (Finset.univ.erase k)) (w k) = CH.d _ n f) :
    ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
      (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
      (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  have hG : ∀ k : Fin (n + 2), CH.d _ (n + 1) (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k)) = 0 := fun k =>
    gC_d (a := (Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      (b := (Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k) (fun s => hdw k s)
  have hY : ∀ k : Fin (n + 2), CH.d _ (n + 1) ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase k))).pullC (n + 1)
      (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
        ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k))) = 0 := fun k => by
    rw [CH.Mor.d_pullC]
    exact (congrArg _ (hG k)).trans (map_zero _)
  refine ⟨fun k => (CH.cx _).cls (gC ((Fil ((n : ℤ) + 1)).res (capS W (Finset.univ.erase k)).ι)
      ((Fil ((n : ℤ) + 1 + 1)).res (capS W (Finset.univ.erase k)).ι) (w k) (hw k)) (hG k), f, hf, ?_, ?_⟩
  · rw [← hEq]
    refine (show _ ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) from sub_mem hCl (Submodule.sum_mem _ fun k _ => ?_))
    exact Lm_res _ (hw k)
  · exact rep_fin hc _ (fun k : Fin (n + 2) => resB Φ.A (capS_univ_le W (Finset.univ.erase k)) (w k)) hY (fun k s => rfl) hEq

theorem cech_top_cup_power : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ (s n : ℕ) (W : Fin (n + 2) → ObjectProperty C), (∀ T, (∃ α, W α T) → (Fil s).S T = ⊥) →
    (∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    ∀ (z : CH.Cn (CH.modF ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A)) 2), CH.d _ 2 z = 0 → (∀ σ, z σ ∈ (Fil 1).S _) →
    ∀ (b : ∀ i, CH.Cn (CH.modF ((W i).ι ⋙ Φ.A)) 1), (∀ i σ, b i σ ∈ (Fil 1).S _) →
    (∀ i, resB Φ.A (fun T h => ⟨i, h⟩ : W i ≤ fun T : C => ∃ α, W α T) z = CH.d _ 1 (b i)) →
    (∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1)) h = 0) →
    ∀ c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
          resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) c →
      ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
        (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
        (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
        Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := by
  intro R _ C _ Φ Fil hF s n W _ _ hS _ z hz hz1 b hb1 hb hcob c hc
  have hWV : ∀ α, W α ≤ (fun T : C => ∃ α, W α T) := fun α T h => ⟨α, h⟩
  have hd := cupPow_d _ z hz (n + 1)
  obtain ⟨u, hu⟩ : cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1) ∈
      LinearMap.range (CH.d _ (2 * n + 1)) := ((CrystallineSemistableComparison.P.cls_surj (CH.cx _) _).2.1 _ hd).1 (hcob hd)
  let v : (KK Φ.A W).X 0 (2 * n + 1) := fun i => resB Φ.A (capV hWV i) u
  have hv1 : (KK Φ.A W).dv 0 (2 * n + 1) v = aa hWV z (n + 1) := by
    funext i
    rw [dv_apply]
    change CH.d _ _ (resB Φ.A _ u) = resB Φ.A _ _
    rw [d_resB, hu]
  have hv2 : (KK Φ.A W).dh 0 (2 * n + 1) v = 0 := by
    funext i
    rw [dh_apply, Fin.sum_univ_two]
    have e : resB Φ.A (cap_le W 0 i) (v (fc 0 i)) = resB Φ.A (cap_le W 1 i) (v (fc 1 i)) := rfl
    rw [e, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_smul, add_neg_cancel]
    rfl
  have hTop : ∀ p q, (dfil (W := W) Fil hF.anti).L 0 p q = ⊤ := fun p q =>
    (Submodule.eq_top_iff'.2 fun x i _ σ => by rw [hF.top 0 le_rfl]; trivial)
  have hPm : PP b hWV z (n + 1) ∈ (dfil (W := W) Fil hF.anti).L ((n : ℤ) + 1) (n + 1) (n + 1) := by
    have h := PP_mem Φ Fil hF b hWV z (fun α σ => hb1 α σ) (n + 1)
    rwa [Nat.cast_succ] at h
  obtain ⟨ω, f, hω, hdω, hf, hP⟩ := zig_stair (BB b) (dfil (W := W) Fil hF.anti) n hTop (fun p q h => KV _ n W p q h)
    (KEx Φ Fil hF W hS) (BB_dh b) (BB_dv b hWV z hb) (aa hWV z) (gg b hWV z) (PP b hWV z)
    (gg_dv b hWV z hz hb) (gg_dh b hWV z) rfl (fun k => rfl) hPm v hv1 hv2
  let tp : Idx (n + 1 + 1) (n + 2) := ⟨id, strictMono_id⟩
  obtain ⟨e, he, hPe⟩ := PP_eq b hWV z (n + 1)
  have hU : capS W Finset.univ ≤ capT W tp.1 := fun T h a => h a (Finset.mem_univ a)
  have hEk : ∀ k : Fin (n + 2), capS W (Finset.univ.erase k) ≤ capT W (fc k tp).1 := fun k T h a =>
    h _ (Finset.mem_erase.2 ⟨Fin.succAbove_ne k a, Finset.mem_univ _⟩)
  have hCl : resB Φ.A hU (PP b hWV z (n + 1) tp) = e • cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
      resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ) := by
    rw [hPe]
    refine (map_zsmul ((rM Φ.A hU).pullC (n + 1)) e _).trans ?_
    have h := res_cupList (A := Φ.A) hU (fun j : Fin (n + 1) => LL b tp j.castSucc j.succ)
    exact congrArg (e • ·) (h.trans (congrArg _ (funext fun j => resB_sub hU _ _)))
  have hP2 : resB Φ.A hU (PP b hWV z (n + 1) tp) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      resB Φ.A (hU.trans (cap_le W k tp)) (ω (fc k tp)) + ((-1 : ℤ) ^ (n + 1)) • CH.d _ n (resB Φ.A hU (f tp)) := by
    have h := congrFun hP tp
    rw [h]
    change (rM Φ.A hU).pullC (n + 1) ((KK Φ.A W).dh n (n + 1) ω tp + (-1 : ℤ) ^ (n + 1) • CH.d _ n (f tp)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dh_apply, map_add (f := _), map_sum, map_zsmul]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) ?_
    · rw [map_zsmul]; rfl
    · rw [d_resB]; rfl
  have hEq := alg_fin e ((-1 : ℤ) ^ (n + 1)) he _ _ _ _ (fun k : Fin (n + 2) => (-1 : ℤ) ^ (k : ℕ)) hCl hP2
  have hd' : CH.d _ n ((e * (-1 : ℤ) ^ (n + 1)) • resB Φ.A hU (f tp)) =
      (e * (-1 : ℤ) ^ (n + 1)) • CH.d _ n (resB Φ.A hU (f tp)) := map_zsmul _ _ _
  have hClm : (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
      resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) ∈
      Lm (Fil ((n : ℤ) + 1)) _ (n + 1) := by
    have h1 : resB Φ.A hU (PP b hWV z (n + 1) tp) ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) := Lm_res _ (hPm tp trivial)
    rw [hCl] at h1
    have h2 := Submodule.smul_of_tower_mem _ e h1
    rwa [smul_smul, he, one_smul] at h2
  have hw : ∀ k : Fin (n + 2), (e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp)) ∈ Lm (Fil ((n : ℤ) + 1)) _ (n + 1) :=
    fun k => Submodule.smul_of_tower_mem _ _ (Lm_res _ (hω (fc k tp) trivial))
  have hdw : ∀ k : Fin (n + 2), CH.d _ (n + 1) ((e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp))) ∈
      Lm (Fil ((n : ℤ) + 1 + 1)) _ (n + 2) := fun k => by
    rw [map_zsmul, d_resB]
    exact Submodule.smul_of_tower_mem _ _ (Lm_res _ (hdω (fc k tp) trivial))
  have hfm : (e * (-1 : ℤ) ^ (n + 1)) • resB Φ.A hU (f tp) ∈ Lm (Fil (n : ℤ)) _ n :=
    Submodule.smul_of_tower_mem _ _ (Lm_res hU (hf tp trivial))
  refine fin_step Φ Fil n W _ hClm c hc _ hw hdw _ hfm ?_
  have e3 : ∀ k : Fin (n + 2), resB Φ.A (capS_univ_le W (Finset.univ.erase k))
      ((e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hEk k) (ω (fc k tp))) =
      (e * (-1 : ℤ) ^ (k : ℕ)) • resB Φ.A (hU.trans (cap_le W k tp)) (ω (fc k tp)) := fun k =>
    map_zsmul ((rM Φ.A (capS_univ_le W (Finset.univ.erase k))).pullC (n + 1)) _ _
  simp only [e3]
  rw [hd']
  exact hEq

end GlobalTheory.CompanionTheory.ConeZig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResLoc
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem resLoc : CrystallineSemistableComparison.E.ResLoc := by
  intro R _ F s U x hx
  exact (GlobalTheory.EtC.resSec R F U).2.2.1 (s : ℤ) ((s + 1 : ℕ) : ℤ) ((s + 1 + 1 : ℕ) : ℤ) (by omega) (by omega) x (by omega) hx

end GlobalTheory.CompanionTheory.EdgeMap
end

