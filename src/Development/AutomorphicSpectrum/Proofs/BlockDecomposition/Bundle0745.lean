module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComparisonDegreeOneBijective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB.Cls

section Abstract

variable {S A₀ A₁ A₂ B₀ B₁ B₂ D₀ D₁ D₂ H : Type} [CommRing S]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup D₀] [AddCommGroup D₁] [AddCommGroup D₂] [AddCommGroup H]
  [Module S A₀] [Module S A₁] [Module S A₂] [Module S B₀] [Module S B₁] [Module S B₂]
  [Module S D₀] [Module S D₁] [Module S D₂] [Module S H]

theorem homology_equiv (a₀ : A₀ →ₗ[S] A₁) (a₁ : A₁ →ₗ[S] A₂) (b₀ : B₀ →ₗ[S] B₁)
    (b₁ : B₁ →ₗ[S] B₂) (e₀ : D₀ →ₗ[S] D₁) (e₁ : D₁ →ₗ[S] D₂) (f₀ : A₀ →ₗ[S] B₀)
    (f₁ : A₁ →ₗ[S] B₁) (f₂ : A₂ →ₗ[S] B₂) (t₀ : B₀ →ₗ[S] D₀) (t₁ : B₁ →ₗ[S] D₁)
    (t₂ : B₂ →ₗ[S] D₂) (Z : Submodule S D₁) (q : Z →ₗ[S] H)
    (hZ : Z = LinearMap.ker e₁) (hq : Function.Surjective q)
    (hq0 : ∀ z : Z, q z = 0 ↔ ∃ g, e₀ g = z.1)
    (hf₁ : ∀ y, f₁ (a₀ y) = b₀ (f₀ y)) (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (ht₁ : ∀ y, t₁ (b₀ y) = e₀ (t₀ y)) (ht₂ : ∀ x, t₂ (b₁ x) = e₁ (t₁ x))
    (ht₀s : Function.Surjective t₀) (ht₁b : Function.Bijective t₁)
    (ht₂i : Function.Injective t₂)
    (hinj : ∀ x, a₁ x = 0 → (∃ y, b₀ y = f₁ x) → ∃ y, a₀ y = x)
    (hsurj : ∀ z, b₁ z = 0 → ∃ x y, a₁ x = 0 ∧ f₁ x - z = b₀ y) :
    ∃ e : Hc a₀ a₁ ≃ₗ[S] H, ∀ (x : A₁) (hx : x ∈ LinearMap.ker a₁),
      ∃ hw : t₁ (f₁ x) ∈ Z, e (Submodule.Quotient.mk ⟨x, hx⟩) = q ⟨_, hw⟩ := by
  have hmem : ∀ x : LinearMap.ker a₁, (t₁ ∘ₗ f₁ ∘ₗ (LinearMap.ker a₁).subtype) x ∈ Z := by
    rintro ⟨x, hx⟩
    rw [hZ, LinearMap.mem_ker]
    have hx' : a₁ x = 0 := hx
    change e₁ (t₁ (f₁ x)) = 0
    rw [← ht₂, ← hf₂, hx', map_zero, map_zero]
  let Φ : LinearMap.ker a₁ →ₗ[S] H :=
    q ∘ₗ (t₁ ∘ₗ f₁ ∘ₗ (LinearMap.ker a₁).subtype).codRestrict Z hmem
  have hΦ : ∀ x : LinearMap.ker a₁, Φ x = q ⟨t₁ (f₁ x.1), hmem x⟩ := fun x ↦ rfl
  have hs : Function.Surjective Φ := by
    intro c
    obtain ⟨w, rfl⟩ := hq c
    obtain ⟨w₀, hw₀⟩ := ht₁b.2 w.1
    have hker : ∀ d, d ∈ Z → e₁ d = 0 := fun d hd ↦ by
      rw [hZ] at hd
      exact hd
    have hw : e₁ w.1 = 0 := hker _ w.2
    have hd : b₁ w₀ = 0 := ht₂i (by rw [ht₂, hw₀, hw, map_zero])
    obtain ⟨x, y, hx, hxy⟩ := hsurj w₀ hd
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hΦ, ← sub_eq_zero, ← map_sub, hq0]
    refine ⟨t₀ y, ?_⟩
    change e₀ (t₀ y) = t₁ (f₁ x) - w.1
    rw [← ht₁, ← hxy, map_sub, hw₀]
  have hk : (LinearMap.range a₀).comap (LinearMap.ker a₁).subtype = LinearMap.ker Φ := by
    ext ⟨x, hx⟩
    have hx' : a₁ x = 0 := hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range, LinearMap.mem_ker]
    rw [hΦ, hq0]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨t₀ (f₀ y), by simp only [← ht₁, hf₁]⟩
    · rintro ⟨g, hg⟩
      obtain ⟨g₀, rfl⟩ := ht₀s g
      refine hinj x hx' ⟨g₀, ht₁b.1 ?_⟩
      rw [ht₁]
      exact hg
  refine ⟨(Submodule.quotEquivOfEq _ _ hk).trans (Φ.quotKerEquivOfSurjective hs), fun x hx ↦ ?_⟩
  exact ⟨hmem ⟨x, hx⟩, rfl⟩

end Abstract

variable {R S C : Type} [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} S}

theorem comparison_degree_one_coboundary (m : BC F F') (x : S ⊗[R] C0 F) :
    th1 m ((d0 F).baseChange S x) = d0 F' (th0 m x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s g =>
    rw [LinearMap.baseChange_tmul, th1, th0, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' φ
    change m.α T' (g T' - mp F φ (g T)) = m.α T' (g T') - mp F' φ (m.α T (g T))
    rw [map_sub, m.naturality]

theorem comparison_degree_two_coboundary (m : BC F F') (x : S ⊗[R] C1 F) :
    th2 m ((d1 F).baseChange S x) = d1 F' (th1 m x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s g =>
    rw [LinearMap.baseChange_tmul, th2, th1, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' T'' φ ψ
    change m.α T'' (mp F ψ (g T T' φ) - g T T'' (φ ≫ ψ) + g T' T'' ψ) =
      mp F' ψ (m.α T' (g T T' φ)) - m.α T'' (g T T'' (φ ≫ ψ)) + m.α T'' (g T' T'' ψ)
    rw [map_add (f := _), map_sub, m.naturality]

theorem model_comparison_degree_zero_bijective (R S C P₀ P₁ P₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) [AddCommGroup P₀] [AddCommGroup P₁]
    [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁)
    (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F)
    (m : BC F F') : IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) →
      Function.Bijective (th1 m) → Function.Bijective (th2 m) →
      ∃ e : Hc (a₀.baseChange S) (a₁.baseChange S) ≃ₗ[S] H1 F',
        ∀ (x : S ⊗[R] P₁) (hx : x ∈ LinearMap.ker (a₁.baseChange S)),
          ∃ hw : th1 m (ψ₁.baseChange S x) ∈ Z1 F',
            e (Submodule.Quotient.mk ⟨x, hx⟩) = H1.mk F' ⟨_, hw⟩ := by
  rintro ⟨-, hc0, hc1, hq⟩ b0 b1 b2
  obtain ⟨-, hq2⟩ := hq (ModuleCat.of R S)
  refine homology_equiv (a₀.baseChange S) (a₁.baseChange S) ((d0 F).baseChange S)
    ((d1 F).baseChange S) (d0 F') (d1 F') (ψ₀.baseChange S) (ψ₁.baseChange S) (ψ₂.baseChange S)
    (th0 m) (th1 m) (th2 m) (Z1 F') (H1.mk F') (commAlgFunctorCocyclesOne_eq_ker F') (H1.mk_surjective F')
    (fun z ↦ H1.mk_eq_zero) ?_ ?_ (comparison_degree_one_coboundary m) (comparison_degree_two_coboundary m) b0.2 b1 b2.1 hq2.1 hq2.2
  · intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc0, LinearMap.baseChange_comp,
      LinearMap.comp_apply]
  · intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hc1, LinearMap.baseChange_comp,
      LinearMap.comp_apply]

end GlobalTheory.CompanionTheory.PerfVB.Cls
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelComplexUnitElement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem lid_lTensor_unit {R A B : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A]
    [Module R B] (f : A →ₗ[R] B) (u : R ⊗[R] A) :
    TensorProduct.lid R B (f.lTensor R u) = f (TensorProduct.lid R A u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul r a => simp

theorem d0_one {R C : Type} [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    d0 F (1 : C0 F) = 0 := by
  funext T T' φ
  simp [d0]

theorem unit_of_model : ∀ (R C P₀ P₁ P₂ : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂]
    (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F)
    (ψ₂ : P₂ →ₗ[R] C2 F), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → ∃ e : P₀, a₀ e = 0 ∧ ψ₀ e = 1 := by
  intro R C P₀ P₁ P₂ _ _ F _ _ _ _ _ _ a₀ a₁ ψ₀ ψ₁ ψ₂ h
  obtain ⟨-, -, -, hM⟩ := h
  obtain ⟨x, y, h1, h2⟩ := (hM (ModuleCat.of R R)).1.2 ((1 : R) ⊗ₜ[R] (1 : C0 F))
    (by simp [d0_one F])
  have h1' : a₀.lTensor R x = 0 := h1
  have h2' : ψ₀.lTensor R x - (1 : R) ⊗ₜ[R] (1 : C0 F) = 0 := by simpa using h2
  refine ⟨TensorProduct.lid R P₀ x, ?_, ?_⟩
  · rw [← lid_lTensor_unit, h1', map_zero]
  · rw [← lid_lTensor_unit, sub_eq_zero.mp h2']
    simp

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModelSteinOfComparison
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem comparison_degree_one_tensor_coboundary {R k C : Type} [CommRing R] [CommRing k] [Algebra R k] [Category.{0} C]
    {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} k} (m : BC F F') (y : k ⊗[R] C0 F) :
    th1 m ((d0 F).lTensor k y) = d0 F' (th0 m y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s f =>
    rw [LinearMap.lTensor_tmul, th1, th0, liftSemi_tmul, liftSemi_tmul, map_smul]
    congr 1
    funext T T' φ
    change m.α T' (d0 F f T T' φ) = d0 F' (c0 m f) T T' φ
    rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, m.naturality]
    rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem const_on_fibre : ∀ (R k C P₀ P₁ P₂ : Type) [CommRing R] [Field k] [Algebra R k] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} k) [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F) (m : BC F F') (e : P₀), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → Function.Bijective (th0 m) → Stein F' → a₀ e = 0 → ψ₀ e = 1 → ∀ x : k ⊗[R] P₀, a₀.lTensor k x = 0 → ∃ c : k, x = c • ((1 : k) ⊗ₜ[R] e) := by
  intro R k C P₀ P₁ P₂ _ _ _ _ F F' _ _ _ _ _ _ a₀ a₁ ψ₀ ψ₁ ψ₂ m e hM hb hS ha he x hx
  obtain ⟨-, h2, -, hQ⟩ := hM
  have hx1 : (d0 F).lTensor k (ψ₀.lTensor k x) = ψ₁.lTensor k (a₀.lTensor k x) := by
    have h := congrArg (LinearMap.lTensor k) h2
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp] at h
    exact (LinearMap.congr_fun h x).symm
  have hv : d0 F' (th0 m (ψ₀.lTensor k x)) = 0 := by
    rw [← comparison_degree_one_tensor_coboundary, hx1, hx, map_zero, map_zero]
  obtain ⟨c, hc⟩ := (hS.1 _).1 hv
  have hone : c0 m (1 : C0 F) = 1 := funext fun T ↦ map_one (m.α T)
  have hce : th0 m (ψ₀.lTensor k (c • ((1 : k) ⊗ₜ[R] e))) = th0 m (ψ₀.lTensor k x) := by
    rw [← hc, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, LinearMap.lTensor_tmul, he, th0,
      liftSemi_tmul, hone, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
  have hψ : ψ₀.lTensor k (x - c • ((1 : k) ⊗ₜ[R] e)) = 0 := by
    rw [map_sub, hb.1 hce, sub_self]
  have ha' : a₀.lTensor k (x - c • ((1 : k) ⊗ₜ[R] e)) = 0 := by
    rw [map_sub, hx, TensorProduct.smul_tmul', LinearMap.lTensor_tmul, ha, TensorProduct.tmul_zero,
      sub_zero]
  obtain ⟨y, hy⟩ := (hQ (ModuleCat.of R k)).1.1 _ ha' ⟨0, by rw [map_zero]; exact hψ.symm⟩
  refine ⟨c, sub_eq_zero.1 ?_⟩
  rw [← hy]
  rfl

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallLiftBaseChangeLocal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem rTensor_eq_zero_iff_mem_smul {R A A' P : Type} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [AddCommGroup P] [Module R P] (π : A →ₐ[R] A')
    (hπ : Function.Surjective π) (w : A ⊗[R] P) :
    π.toLinearMap.rTensor P w = 0 ↔
      w ∈ (RingHom.ker π) • (⊤ : Submodule A (A ⊗[R] P)) := by
  constructor
  · intro hw
    have hex : Function.Exact ((RingHom.ker π).restrictScalars R).subtype π.toLinearMap := by
      intro a
      constructor
      · intro h
        exact ⟨⟨a, (RingHom.mem_ker (f := π)).mpr h⟩, rfl⟩
      · rintro ⟨k, rfl⟩
        exact (RingHom.mem_ker (f := π)).mp k.2
    obtain ⟨v, rfl⟩ := ((rTensor_exact P hex hπ) w).mp hw
    clear hw
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul k p =>
      rw [LinearMap.rTensor_tmul, Submodule.coe_subtype]
      have e : (k : A) ⊗ₜ[R] p = (k : A) • ((1 : A) ⊗ₜ[R] p) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e]
      exact Submodule.smul_mem_smul k.2 Submodule.mem_top
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · intro hw
    refine Submodule.smul_induction_on hw (fun k hk x _hx => ?_) ?_
    · clear _hx
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a p =>
        rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, smul_eq_mul,
          map_mul, (RingHom.mem_ker (f := π)).mp hk, MulZeroClass.zero_mul, TensorProduct.zero_tmul]
      | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, add_zero]
    · intro x y hx hy
      rw [map_add (f := _), hx, hy, add_zero]

theorem lTensor_rTensor_apply {R A A' P P' : Type} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    (π : A →ₐ[R] A') (f : P →ₗ[R] P') (w : A ⊗[R] P) :
    f.lTensor A' (π.toLinearMap.rTensor P w) = π.toLinearMap.rTensor P' (f.lTensor A w) := by
  induction w with
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul a p => simp

private theorem lift_of_smallLift_lemma {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A) (t : A) :
    RingHom.ker ((Ideal.Quotient.mkₐ R (Ideal.span {Ideal.Quotient.mk J t})).comp (Ideal.Quotient.mkₐ R J)) =
      J ⊔ Ideal.span {t} := by
  ext x
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, ← Set.image_singleton, ← Ideal.map_span,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]

theorem lift_of_smallLift : ∀ (R P₀ P₁ P₂ A : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [CommRing A] [IsLocalRing A] [Algebra R A] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂), a₁ ∘ₗ a₀ = 0 → SmallLift a₀ a₁ → Lift (a₁.baseChange A) := by
  intro R P₀ P₁ P₂ A _ _ _ _ _ _ _ _ _ _ a₀ a₁ h01 hS
  intro J t hJ hJt z hz
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : IsLocalRing (A ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  set t' : A ⧸ J := Ideal.Quotient.mk J t with ht'
  set ρ : A →ₐ[R] (A ⧸ J) ⧸ Ideal.span {t'} :=
    (Ideal.Quotient.mkₐ R (Ideal.span {t'})).comp (Ideal.Quotient.mkₐ R J) with hρ
  have hρs : Function.Surjective ρ :=
    (Ideal.Quotient.mkₐ_surjective R _).comp (Ideal.Quotient.mkₐ_surjective R J)
  have hker : RingHom.ker ρ = J ⊔ Ideal.span {t} := lift_of_smallLift_lemma J t
  have hJs : Function.Surjective (Ideal.Quotient.mkₐ R J) := Ideal.Quotient.mkₐ_surjective R J
  have hkerJ : RingHom.ker (Ideal.Quotient.mkₐ R J) = J := Ideal.Quotient.mkₐ_ker R J
  have ht : ∀ x : A ⧸ J, ¬ IsUnit x → x * t' = 0 := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : x ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hx (hu.map _)
    rw [ht', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hJt x hx'
  set z' := ρ.toLinearMap.rTensor P₁ z with hz'
  have hz2 : (a₁.lTensor A) z ∈ (J ⊔ Ideal.span {t}) • (⊤ : Submodule A (A ⊗[R] P₂)) := by
    rwa [LinearMap.baseChange_eq_ltensor] at hz
  have hz0 : a₁.lTensor _ z' = 0 := by
    rw [hz', lTensor_rTensor_apply, rTensor_eq_zero_iff_mem_smul ρ hρs, hker]
    exact hz2
  obtain ⟨xb, y, hx0, hxy⟩ := hS (A ⧸ J) t' ht z' hz0
  obtain ⟨x₁, rfl⟩ := LinearMap.rTensor_surjective P₁ (g := (Ideal.Quotient.mkₐ R J).toLinearMap) hJs xb
  obtain ⟨y₁, rfl⟩ := LinearMap.rTensor_surjective P₀ (g := ρ.toLinearMap) hρs y
  have hcomp : ρ.toLinearMap.rTensor P₁ x₁ = (Ideal.Quotient.mkₐ R (Ideal.span {t'})).toLinearMap.rTensor P₁
      ((Ideal.Quotient.mkₐ R J).toLinearMap.rTensor P₁ x₁) := by
    rw [hρ, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
  refine ⟨x₁ - a₀.lTensor A y₁, ?_, ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor, map_sub]
    have h0 : a₁.lTensor A (a₀.lTensor A y₁) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h01, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rw [h0, sub_zero, ← hkerJ, ← rTensor_eq_zero_iff_mem_smul _ hJs, ← lTensor_rTensor_apply]
    exact hx0
  · rw [← hker, ← rTensor_eq_zero_iff_mem_smul ρ hρs, map_sub, map_sub, ← lTensor_rTensor_apply, hcomp, ← hz',
      sub_right_comm, hxy, sub_self]

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitComplexHomotopyData
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_contraction_onto_homology (R P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup P₀]
    [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂]
    (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (t : P₁ →ₗ[R] P₀) (s : P₂ →ₗ[R] P₁) :
    a₁ ∘ₗ a₀ = 0 → a₀ ∘ₗ t ∘ₗ a₀ = a₀ → a₁ ∘ₗ s ∘ₗ a₁ = a₁ →
    ∃ (j : Hc a₀ a₁ →ₗ[R] P₁) (π : P₁ →ₗ[R] Hc a₀ a₁) (h : P₁ →ₗ[R] P₀) (h' : P₂ →ₗ[R] P₁),
      π ∘ₗ j = LinearMap.id ∧ a₁ ∘ₗ j = 0 ∧ π ∘ₗ a₀ = 0 ∧
        j ∘ₗ π + a₀ ∘ₗ h + h' ∘ₗ a₁ = LinearMap.id := by
  intro h10 ht hs
  have h10' : ∀ y, a₁ (a₀ y) = 0 := fun y => LinearMap.congr_fun h10 y
  have ht' : ∀ y, a₀ (t (a₀ y)) = a₀ y := fun y => LinearMap.congr_fun ht y
  have hs' : ∀ x, a₁ (s (a₁ x)) = a₁ x := fun x => LinearMap.congr_fun hs x
  have hk : ∀ x, x - s (a₁ x) ∈ LinearMap.ker a₁ := fun x => by
    rw [LinearMap.mem_ker, map_sub, hs', sub_self]
  have hp : Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀) ≤
      LinearMap.ker ((LinearMap.id - a₀ ∘ₗ t) ∘ₗ (LinearMap.ker a₁).subtype) := by
    rintro ⟨z, hz⟩ hzN
    obtain ⟨y, rfl⟩ : ∃ y, a₀ y = z := LinearMap.mem_range.1 (Submodule.mem_comap.1 hzN)
    rw [LinearMap.mem_ker]
    change a₀ y - a₀ (t (a₀ y)) = 0
    rw [ht', sub_self]
  refine ⟨Submodule.liftQ _ ((LinearMap.id - a₀ ∘ₗ t) ∘ₗ (LinearMap.ker a₁).subtype) hp,
    (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)).mkQ ∘ₗ
      LinearMap.codRestrict (LinearMap.ker a₁) (LinearMap.id - s ∘ₗ a₁) hk,
    t - t ∘ₗ s ∘ₗ a₁, s, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)) q
    have hz' : a₁ z = 0 := LinearMap.mem_ker.1 hz
    have key : (⟨z - a₀ (t z) - s (a₁ (z - a₀ (t z))), hk _⟩ : LinearMap.ker a₁) - ⟨z, hz⟩ ∈
        Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀) := by
      refine Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨-t z, ?_⟩)
      change a₀ (-t z) = z - a₀ (t z) - s (a₁ (z - a₀ (t z))) - z
      rw [map_sub a₁, hz', h10', sub_self, map_zero, sub_zero, map_neg]
      abel
    exact (Submodule.Quotient.eq _).2 key
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)) q
    have hz' : a₁ z = 0 := LinearMap.mem_ker.1 hz
    change a₁ (z - a₀ (t z)) = 0
    rw [map_sub, hz', h10', sub_zero]
  · refine LinearMap.ext fun y => ?_
    change Submodule.Quotient.mk (p := Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀))
      (⟨a₀ y - s (a₁ (a₀ y)), hk _⟩ : LinearMap.ker a₁) = 0
    refine (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨y, ?_⟩))
    change a₀ y = a₀ y - s (a₁ (a₀ y))
    rw [h10', map_zero, sub_zero]
  · refine LinearMap.ext fun x => ?_
    change x - s (a₁ x) - a₀ (t (x - s (a₁ x))) + a₀ (t x - t (s (a₁ x))) + s (a₁ x) = x
    simp only [map_sub]
    abel

end GlobalTheory.CompanionTheory.PerfVB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialPullbackGivesUnitCocycle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.FewEq

open GlobalTheory.SmallExtLift

theorem exists_local_of_gen {R : Type} [CommRing R] {X Y : Scheme.{0}} (s : X ⟶ Sp R) (J : Ideal R)
    {π : Y ⟶ X} {f' : Y ⟶ Sp (R ⧸ J)}
    (H : IsPullback π f' s (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (M : LB X) (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a))
    (hV : ∀ a, IsAffineOpen (V a)) (hVV : ∀ a b, IsAffineOpen (V a ⊓ V b))
    (t : LB.Gen (M.pull π)) (ht : t.IsGen) :
    ∃ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
      ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈
        ext s J (V a ⊓ V b) := by
  choose y hy using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    (rs Y (pull_le M π (j a) (hj a)) (t.s fun _ => j a).val)
  choose z hz using fun a => app_surj Ideal.Quotient.mk_surjective H (hV a)
    (rs Y (pull_le M π (j a) (hj a)) (t.s fun _ => j a)⁻¹.val)
  refine ⟨y, z, fun a => ?_, fun a b => ?_⟩
  · have h := mem_of_app_eq_zero Ideal.Quotient.mk_surjective H (hV a) (y a * z a - 1) (by
      rw [map_sub, map_mul, map_one, hy, hz, ← map_mul, Units.mul_inv, map_one, sub_self])
    rwa [Ideal.mk_ker] at h
  · have h := mem_of_app_eq_zero Ideal.Quotient.mk_surjective H (hVV a b)
      (rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b)) (gr_ext fun w hw => by
        have e : ∀ c (h : (𝟙 Y ≫ π) w ∈ V c), gr (𝟙 Y ≫ π) w (V c) h (y c) =
            gr (𝟙 Y) w _ (pull_le M π (j c) le_rfl (hj c h)) (t.s fun _ => j c).val := fun c h =>
          (gr_app (𝟙 Y) π w (V c) h (y c)).symm.trans
            ((congrArg _ (hy c)).trans (gr_res (𝟙 Y) w _ h _))
        refine (gr_app _ _ _ _ _ _).trans ?_
        simp only [tr]
        rw [map_zero, map_sub, map_mul, gr_res, gr_res, gr_res, e, e, sub_eq_zero]
        exact gr_gen ht (𝟙 Y) w (hj a hw.1) (hj b hw.2))
    rwa [Ideal.mk_ker] at h

theorem exists_local_of_triv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Ideal R) (M : LB X), M.IsLB →
    ∀ (A : Type) (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)),
      (∀ a, IsAffineOpen (V a)) → (∀ a b, IsAffineOpen (V a ⊓ V b)) →
      GlobalTheory.AbLaw.Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) →
      ∃ y z : ∀ a, Γ(X, V a), (∀ a, y a * z a - 1 ∈ ext s J (V a)) ∧
        ∀ a b, rs X inf_le_left (y a) - tr M V j hj a b * rs X inf_le_right (y b) ∈ ext s J (V a ⊓ V b) := by
  intro R _ X s J M _ A V j hj hV hVV ⟨t, ht⟩
  exact exists_local_of_gen s J (IsPullback.of_hasPullback s (spMap (Ideal.Quotient.mk J))) M A V j
    hj hV hVV t ht

end GlobalTheory.CompanionTheory.FewEq
end
end

