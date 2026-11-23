module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0132
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0734

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAndFinrankLe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds

theorem finite_and_finrank_le {k V : Type} [Field k] [AddCommGroup V] [Module k V] (g : ℕ)
    (h : ∀ x : Fin (g + 1) → V, ¬ LinearIndependent k x) :
    Module.Finite k V ∧ Module.finrank k V ≤ g := by
  classical
  let b := Module.Basis.ofVectorSpace k V
  have hemb : ∀ e : Fin (g + 1) ↪ Module.Basis.ofVectorSpaceIndex k V, False :=
    fun e => h _ (b.linearIndependent.comp e e.injective)
  haveI : Finite (Module.Basis.ofVectorSpaceIndex k V) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    exact hemb (Fin.valEmbedding.trans (Infinite.natEmbedding _))
  haveI hfin : Module.Finite k V := Module.Finite.of_basis b
  refine ⟨hfin, ?_⟩
  rw [Module.finrank_eq_nat_card_basis b]
  by_contra hlt
  rw [not_le] at hlt
  exact hemb ((Fin.castLEEmb (Nat.succ_le_of_lt hlt)).trans (Finite.equivFin _).symm.toEmbedding)

theorem h1Le : DescentSt → LowSt → SteinSt → VanSt → HopfSt → HopfLeSt → PositivityTheory.ObstructionTrivialLocus.H1StructureDimLe := by
  intro hD hL hS hV hH hHL k _ A _ g hA hsm
  haveI : AlgebraicGeometry.IsProper A.hom := ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme.proper (self := hA)
  haveI : CompactSpace A.left := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨P, _, _, ⟨S⟩⟩ := GlobalTheory.CompanionTheory.Hodge.WedgeField.exists_finite_sys A.hom
  have hfield : IsField k := Field.toIsField k
  have hq : MainStatements.Hodge.AllQIso (MainStatements.Hodge.resSys A.hom S) := hD k A.left A.hom inferInstance P S
  obtain ⟨hb1, -, hst⟩ := hL k _ _ _ _ (MainStatements.Hodge.resSys A.hom S) hq
  have hstein : MainStatements.Hodge.Stein (MainStatements.Hodge.OSys A.hom S) := hst.mp (hS k A g hA hsm)
  have hexact := hV k A g hA hsm hfield P S
  have hhopf : MainStatements.Hodge.Hopf (MainStatements.Hodge.OSys A.hom S) True := by
    have h := hH k A g hA hsm P S
    rwa [eq_true hfield] at h
  have hno := hHL k P (MainStatements.Hodge.OSys A.hom S) g hfield hstein hexact hhopf
  refine finite_and_finrank_le g (fun x hx => ?_)
  exact hno (⇑(MainStatements.Hodge.resSys A.hom S).pull1 ∘ x)
    (hx.map' (MainStatements.Hodge.resSys A.hom S).pull1 (LinearMap.ker_eq_bot.mpr hb1.1))

end GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitelyManySectionsPointsClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.ClosedPts

theorem isClosed_singleton_of_finite_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (Z : Scheme.{0}) (s : Z ⟶ Sp k) [LocallyOfFiniteType s], Set.Finite {σ : Sp k ⟶ Z | σ ≫ s = 𝟙 _} → ∀ z : Z, IsClosed ({z} : Set Z) := by
  intro k _ _ Z s _ hfin z
  haveI : JacobsonSpace (Sp k) :=
    (PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace (R := k)).mp inferInstance
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace s
  let pt : Sp k := IsLocalRing.closedPoint (CommRingCat.of k)
  have hsec : ∀ x : Z, IsClosed ({x} : Set Z) →
      x ∈ (fun σ : Sp k ⟶ Z => σ pt) '' {σ : Sp k ⟶ Z | σ ≫ s = 𝟙 _} := by
    intro x hx
    haveI := (isClosed_singleton_iff_locallyOfFiniteType (x := x)).mp hx
    obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of k ⟶ Z.residueField x,
        Spec.map g = Z.fromSpecResidueField x ≫ s :=
      ⟨Spec.preimage (Z.fromSpecResidueField x ≫ s), Spec.map_preimage _⟩
    have hlft : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    have hft : g.hom.FiniteType := HasRingHomProperty.Spec_iff.mp hlft
    letI : Algebra k (Z.residueField x) := g.hom.toAlgebra
    haveI : Algebra.FiniteType k (Z.residueField x) := hft
    haveI : Module.Finite k (Z.residueField x) := finite_of_finite_type_of_isJacobsonRing k _
    have hbij : Function.Bijective (algebraMap k (Z.residueField x)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e := RingEquiv.ofBijective (algebraMap k (Z.residueField x)) hbij
    let φ : Z.residueField x ⟶ CommRingCat.of k := CommRingCat.ofHom e.symm.toRingHom
    have hgφ : g ≫ φ = 𝟙 _ := by
      ext a
      exact e.symm_apply_apply a
    refine ⟨Spec.map φ ≫ Z.fromSpecResidueField x, ?_, ?_⟩
    · have h1 : (Spec.map φ ≫ Z.fromSpecResidueField x) ≫ s = Spec.map (g ≫ φ) := by
        rw [Category.assoc, ← hg]
        exact (Spec.map_comp _ _).symm
      rw [hgφ, Spec.map_id] at h1
      exact h1
    · simp [Scheme.fromSpecResidueField_apply]
  have hcp : (closedPoints Z).Finite :=
    (hfin.image (fun σ : Sp k ⟶ Z => σ pt)).subset (fun x hx => hsec x hx)
  have hT : (closure ({z} : Set Z) ∩ closedPoints Z).Finite :=
    hcp.subset Set.inter_subset_right
  have hTc : IsClosed (closure ({z} : Set Z) ∩ closedPoints Z) := by
    rw [← Set.biUnion_of_singleton (closure ({z} : Set Z) ∩ closedPoints Z)]
    exact hT.isClosed_biUnion (fun t ht => ht.2)
  have heq : closure (closure ({z} : Set Z) ∩ closedPoints Z) = closure ({z} : Set Z) :=
    JacobsonSpace.closure_inter_closedPoints isClosed_closure
  have hz : z ∈ closure ({z} : Set Z) ∩ closedPoints Z := by
    rw [← hTc.closure_eq, heq]
    exact subset_closure (Set.mem_singleton z)
  exact hz.2

end GlobalTheory.CompanionTheory.ClosedPts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeFirstCohomology
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FlatBase

section Alg

variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']

def Bas {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (f : M → M') : Prop :=
  ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ b, e (1 ⊗ₜ b) = f b

variable {R R'}

theorem Bas.pi {J : Type} [Finite J] {M M' : J → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)] (f : ∀ i, M i → M' i) (h : ∀ i, Bas R R' (f i)) :
    Bas R R' (fun (x : ∀ i, M i) i ↦ f i (x i)) := by
  classical
  haveI := Fintype.ofFinite J
  choose e he using h
  refine ⟨(TensorProduct.piRight R R' R' M).trans (LinearEquiv.piCongrRight e), fun b ↦ ?_⟩
  funext i
  simp [he]

theorem flat_coh [Module.Flat R R'] {A₀ A₁ A₂ B₀ B₁ B₂ : Type} [AddCommGroup A₀] [AddCommGroup A₁]
    [AddCommGroup A₂] [Module R A₀] [Module R A₁] [Module R A₂] [AddCommGroup B₀] [AddCommGroup B₁]
    [AddCommGroup B₂] [Module R' B₀] [Module R' B₁] [Module R' B₂]
    (Z : Submodule R A₁) (Z' : Submodule R' B₁) (d₀ : A₀ →ₗ[R] Z) (d₁ : A₁ →ₗ[R] A₂)
    (d₀' : B₀ →ₗ[R'] Z') (d₁' : B₁ →ₗ[R'] B₂)
    (hZ : ∀ x, x ∈ Z ↔ d₁ x = 0) (hZ' : ∀ x, x ∈ Z' ↔ d₁' x = 0)
    (a₀ : A₀ → B₀) (a₁ : A₁ → B₁) (a₂ : A₂ → B₂)
    (h₀ : Bas R R' a₀) (h₁ : Bas R R' a₁) (h₂ : Bas R R' a₂)
    (c₀ : ∀ x, (d₀' (a₀ x)).1 = a₁ (d₀ x).1) (c₁ : ∀ x, d₁' (a₁ x) = a₂ (d₁ x))
    (p : (Z ⧸ LinearMap.range d₀) →ₛₗ[algebraMap R R'] (Z' ⧸ LinearMap.range d₀'))
    (hp : ∀ (z : Z) (z' : Z'), z'.1 = a₁ z.1 →
      p (Submodule.Quotient.mk z) = Submodule.Quotient.mk z') :
    ∃ e : R' ⊗[R] (Z ⧸ LinearMap.range d₀) ≃ₗ[R'] (Z' ⧸ LinearMap.range d₀'),
      ∀ c, e (1 ⊗ₜ c) = p c := by
  obtain ⟨e₀, he₀⟩ := h₀
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  letI : Module R (Z' ⧸ LinearMap.range d₀') := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (Z' ⧸ LinearMap.range d₀') :=
    ⟨fun r s x ↦ by
      change (r • s) • x = algebraMap R R' r • s • x
      rw [Algebra.smul_def, mul_smul]⟩
  let pl : (Z ⧸ LinearMap.range d₀) →ₗ[R] (Z' ⧸ LinearMap.range d₀') :=
    { toFun := p, map_add' := p.map_add, map_smul' := fun r x ↦ p.map_smulₛₗ r x }
  let L : R' ⊗[R] (Z ⧸ LinearMap.range d₀) →ₗ[R'] (Z' ⧸ LinearMap.range d₀') := pl.liftBaseChange R'
  have hL : ∀ c, L (1 ⊗ₜ c) = p c := fun c ↦ by
    simp only [L, LinearMap.liftBaseChange_tmul, one_smul]; rfl
  have ta : ∀ (r : R') (x : A₁), e₁ (r ⊗ₜ x) = r • a₁ x := fun r x ↦ by
    rw [← he₁, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have ta₀ : ∀ (r : R') (x : A₀), e₀ (r ⊗ₜ x) = r • a₀ x := fun r x ↦ by
    rw [← he₀, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have ta₂ : ∀ (r : R') (x : A₂), e₂ (r ⊗ₜ x) = r • a₂ x := fun r x ↦ by
    rw [← he₂, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have a₂0 : a₂ 0 = 0 := by rw [← he₂, TensorProduct.tmul_zero, map_zero]

  have comm₁ : ∀ t, e₂ (d₁.baseChange R' t) = d₁' (e₁ t) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [ta, ta₂, c₁]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have comm₀ : ∀ t, (d₀' (e₀ t)).1 = e₁ (Z.subtype.baseChange R' (d₀.baseChange R' t)) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [ta, ta₀, c₀]
    | add x y hx hy => simp only [map_add (f := _), Submodule.coe_add, hx, hy]
  have mem : ∀ t, e₁ (Z.subtype.baseChange R' t) ∈ Z' := fun t ↦ by
    rw [hZ', ← comm₁]
    have : ∀ t, d₁.baseChange R' (Z.subtype.baseChange R' t) = 0 := fun t ↦ by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul r x => simp [(hZ _).1 x.2]
      | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    rw [this, map_zero]
  let g : R' ⊗[R] Z →ₗ[R'] Z' :=
    LinearMap.codRestrict Z' (e₁.toLinearMap ∘ₗ Z.subtype.baseChange R') mem
  have hg : ∀ t, (g t).1 = e₁ (Z.subtype.baseChange R' t) := fun _ ↦ rfl
  have key : ∀ t, L ((LinearMap.range d₀).mkQ.baseChange R' t) = Submodule.Quotient.mk (g t) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have hx : a₁ x.1 ∈ Z' := by
        rw [hZ', c₁, (hZ _).1 x.2, a₂0]
      rw [LinearMap.baseChange_tmul]
      simp only [L, LinearMap.liftBaseChange_tmul]
      have e1 : pl ((LinearMap.range d₀).mkQ x) = Submodule.Quotient.mk ⟨a₁ x.1, hx⟩ := hp x _ rfl
      rw [e1, ← Submodule.Quotient.mk_smul]
      congr 1
      apply Subtype.ext
      simp [hg, ta]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]; rfl
  have hLs : Function.Surjective L := fun c' ↦ by
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ c'
    have hex : Function.Exact Z.subtype d₁ := fun x ↦ by
      rw [← hZ]; simp
    have hex' := Module.Flat.lTensor_exact R' hex
    have h0 : d₁.lTensor R' (e₁.symm z'.1) = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]
      apply e₂.injective
      rw [comm₁, e₁.apply_symm_apply, map_zero]
      exact (hZ' _).1 z'.2
    obtain ⟨t, ht⟩ := (hex' _).1 h0
    rw [← LinearMap.baseChange_eq_ltensor] at ht
    refine ⟨(LinearMap.range d₀).mkQ.baseChange R' t, ?_⟩
    rw [key]
    congr 1
    apply Subtype.ext
    rw [hg, ht, e₁.apply_symm_apply]
  have hLi : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨t₀, rfl⟩ : ∃ t₀, (LinearMap.range d₀).mkQ.baseChange R' t₀ = t := by
      have := LinearMap.lTensor_surjective R' (g := (LinearMap.range d₀).mkQ)
        (Submodule.mkQ_surjective _)
      rw [← LinearMap.baseChange_eq_ltensor] at this
      exact this t
    rw [key, Submodule.Quotient.mk_eq_zero] at ht
    obtain ⟨y', hy'⟩ := ht
    have e1 : Z.subtype.baseChange R' (d₀.baseChange R' (e₀.symm y')) = Z.subtype.baseChange R' t₀ := by
      apply e₁.injective
      rw [← comm₀, e₀.apply_symm_apply, hy', hg]
    have inj : Function.Injective (Z.subtype.baseChange R') := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Z.injective_subtype
    rw [← inj e1]
    have : ∀ y, (LinearMap.range d₀).mkQ.baseChange R' (d₀.baseChange R' y) = 0 := fun y ↦ by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r x =>
        have : (LinearMap.range d₀).mkQ (d₀ x) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
        simp [this]
      | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    exact this _
  exact ⟨LinearEquiv.ofBijective L ⟨hLi, hLs⟩, hL⟩

end Alg

section Sys

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'}

theorem flat_base_change_first_cohomology [Module.Flat R R'] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (m : BC F F') :
    ∃ e : R' ⊗[R] H1 F ≃ₗ[R'] H1 F', ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c := by
  have b : ∀ T, Bas R R' (m.α T) := m.bij
  have b₀ : Bas R R' (fun (x : C0 F) T ↦ m.α T (x T)) := Bas.pi _ b
  have b₁ : Bas R R' (fun (x : C1 F) T T' φ ↦ m.α T' (x T T' φ)) :=
    Bas.pi (M := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F.obj T')
      (M' := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F'.obj T') _ fun T ↦
    Bas.pi (M := fun T' ↦ ∀ _ : T ⟶ T', F.obj T') (M' := fun T' ↦ ∀ _ : T ⟶ T', F'.obj T') _ fun T' ↦
    Bas.pi (M := fun _ : T ⟶ T' ↦ F.obj T') (M' := fun _ : T ⟶ T' ↦ F'.obj T') _ fun _ ↦ b T'
  have b₂ : Bas R R' (fun (x : C2 F) T T' T'' φ ψ ↦ m.α T'' (x T T' T'' φ ψ)) :=
    Bas.pi (M := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'')
      (M' := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'') _ fun T ↦
    Bas.pi (M := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'')
      (M' := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'') _ fun T' ↦
    Bas.pi (M := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'')
      (M' := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'') _ fun T'' ↦
    Bas.pi (M := fun _ : T ⟶ T' ↦ ∀ _ : T' ⟶ T'', F.obj T'')
      (M' := fun _ : T ⟶ T' ↦ ∀ _ : T' ⟶ T'', F'.obj T'') _ fun _ ↦
    Bas.pi (M := fun _ : T' ⟶ T'' ↦ F.obj T'') (M' := fun _ : T' ⟶ T'' ↦ F'.obj T'') _ fun _ ↦ b T''
  refine flat_coh (Z1 F) (Z1 F') ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) (d1 F)
    ((d0 F').codRestrict (Z1 F') (commAlgFunctorCoboundaryZero_mem_cocyclesOne F')) (d1 F')
    (fun x ↦ by rw [commAlgFunctorCocyclesOne_eq_ker]; rfl) (fun x ↦ by rw [commAlgFunctorCocyclesOne_eq_ker]; rfl) _ _ _ b₀ b₁ b₂ ?_ ?_
    m.coef.pull1 ?_
  · intro x
    funext T T' φ
    simp only [LinearMap.codRestrict_apply, amitsur_d0_apply, map_sub, m.naturality]
  · intro x
    funext T T' T'' φ ψ
    simp only [d1_apply, map_sub, map_add (f := _), m.naturality]
  · intro z z' h
    have : m.coef.pullbackOneCocycle z = z' := Subtype.ext h.symm
    rw [← this]
    rfl

end Sys

theorem flatBC : DescentSt → LowSt → SysBCSt → FlatBCSt := by
  intro hD hL hS R R' _ _ _ _ X X' s s' φ h hsep hqc
  haveI := hsep
  haveI := hqc
  haveI : CompactSpace X := by
    rw [← isCompact_univ_iff]
    simpa using QuasiCompact.isCompact_preimage (f := s) Set.univ isOpen_univ isCompact_univ
  obtain ⟨P, iP, fP, ⟨S⟩⟩ := GlobalTheory.CompanionTheory.Hodge.WedgeField.exists_finite_sys s
  obtain ⟨S', m, hm⟩ := hS R R' X X' s s' φ h hsep P S
  have hsep' : IsSeparated s' := MorphismProperty.of_isPullback (P := @IsSeparated) h hsep
  obtain ⟨b, -, -⟩ := hL R _ _ _ _ _ (hD R X s hsep P S)
  obtain ⟨b', -, -⟩ := hL R' _ _ _ _ _ (hD R' X' s' hsep' P S')
  let E : HO1 s ≃ₗ[R] H1 (OSys s S) := LinearEquiv.ofBijective (resSys s S).pull1 b
  let E' : HO1 s' ≃ₗ[R'] H1 (OSys s' S') := LinearEquiv.ofBijective (resSys s' S').pull1 b'
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  obtain ⟨e, he⟩ := flat_base_change_first_cohomology m
  refine ⟨(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') E).trans
    (e.trans E'.symm), fun c ↦ hm c _ ?_⟩
  have : E' ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') E).trans
      (e.trans E'.symm) (1 ⊗ₜ c)) = e (1 ⊗ₜ E c) := by
    simp
  exact ((he _).symm.trans this.symm)

end GlobalTheory.CompanionTheory.Hodge.FlatBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricallyIntegralGlobalFunctionsConstant
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem triv_of_isEmpty {Y : Scheme.{0}} [IsEmpty Y] (L : LB Y) : Triv L := by
  have hs : ∀ U : Y.Opens, Subsingleton Γ(Y, U) := fun U => by
    have hU : U = ⊥ := by
      ext y
      exact (IsEmpty.false y).elim
    subst hU
    infer_instance
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have := hs (L.U i ⊓ L.U j)
  exact Subsingleton.elim _ _

theorem exists_ideal_near : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB →
    Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → Surjective f →
    (∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)),
      IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom) →
    ∀ p : PrimeSpectrum R, ∃ (r : R) (I : Ideal R), r ∉ p.asIdeal ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
        (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) →
        (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  intro R _ X f M hM hP hQ hprop hgi hsurj hbij p
  have hW := GlobalTheory.TrivLocus.isClosed_trivLocus R X f M hM hP hQ hprop hgi
  by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X)
      (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)}
  · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, hpb, ht⟩ := hp
    obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R X f M hM hP inferInstance hsurj K g₀ X₀ π₀ f₀ hpb
      (hbij K g₀ X₀ π₀ f₀ hpb) ht
    refine ⟨r, I, fun hrp => hr ?_, H⟩
    rw [← hk] at hrp
    exact hrp
  · obtain ⟨_, ⟨r, rfl⟩, hpr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ _ from hp) hW.isOpen_compl
    refine ⟨r, ⊤, hpr, fun R' _ g X' π f' h hu => ?_⟩
    rcases subsingleton_or_nontrivial R' with hR' | hR'
    · have hE : IsEmpty (Spec (CommRingCat.of R')) := inferInstanceAs (IsEmpty (PrimeSpectrum R'))
      have hX' : IsEmpty X' := ⟨fun x => hE.false (f' x)⟩
      exact ⟨fun _ x _ => Subsingleton.elim _ _, fun _ => triv_of_isEmpty _⟩
    · refine ⟨fun ht => ?_, fun hle => ?_⟩
      · exfalso
        obtain ⟨m, hm⟩ := Ideal.exists_maximal R'
        let _ : Field (R' ⧸ m) := Ideal.Quotient.field m
        let q : R' →+* R' ⧸ m := Ideal.Quotient.mk m
        have hpb : IsPullback (pullback.fst f' (Spec.map (CommRingCat.ofHom q)) ≫ π)
            (pullback.snd f' (Spec.map (CommRingCat.ofHom q))) f
            (Spec.map (CommRingCat.ofHom (q.comp g))) := by
          have e : Spec.map (CommRingCat.ofHom (q.comp g)) =
              Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom g) := by
            rw [← Spec.map_comp, CommRingCat.ofHom_comp]
          rw [e]
          exact (IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom q))).paste_horiz h
        have hprime : (RingHom.ker (q.comp g)).IsPrime := RingHom.ker_isPrime _
        refine hsub (show (⟨RingHom.ker (q.comp g), hprime⟩ : PrimeSpectrum R) ∈ _ from ?_)
          ⟨R' ⧸ m, inferInstance, q.comp g, _, _, _, rfl, hpb, GlobalTheory.Biadditive.triv_pull_comp ht _⟩
        intro hr
        exact (hu.map q).ne_zero hr
      · have h1 : g 1 = 0 := hle (Submodule.mem_top (x := (1 : R)))
        rw [map_one] at h1
        exact absurd h1 one_ne_zero

end GlobalTheory.CompanionTheory.TrivLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfStOfSpreads
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfModels

theorem flat_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Flat s] (U : X.affineOpens) :
    Module.Flat R (Sec s U.1) := by
  have hfl : RingHom.Flat (s.appLE ⊤ U.1 le_top).hom := s.flat_appLE (isAffineOpen_top _) U.2 le_top
  have hi : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
  have h : RingHom.Flat (secMap s U.1).hom := RingHom.Flat.comp hi hfl
  exact (RingHom.flat_algebraMap_iff (R := R) (S := Sec s U.1)).1 h

theorem exists_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsSeparated s] [QuasiCompact s] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  obtain ⟨J, hf, hl, U, -, hm, hc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed R X s inferInstance inferInstance
  exact ⟨J, hl, hf, ⟨⟨U, hm, hc⟩⟩⟩

theorem perf_noeth (hF : FinCohSt) (hN : PerfNoethSt) (R : Type) [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{0}) (s : X ⟶ Sp R) [Smooth s] [IsProper s] :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys X P), Perf (OSys s S) := by
  obtain ⟨P, _, _, ⟨S⟩⟩ := exists_sys s
  obtain ⟨h₀, h₁⟩ := hF R X s inferInstance P S
  exact ⟨P, inferInstance, inferInstance, S,
    hN R P (OSys s S) inferInstance (fun T ↦ flat_sec s (S.u T.unop)) h₀ h₁⟩

theorem perf_base (hB : SysBCSt) (hP : PerfBaseSt) {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R)
    {Y X : Scheme.{0}} (f : Y ⟶ Sp R₀) (s : X ⟶ Sp R) (π : X ⟶ Y) [IsSeparated f]
    (h : IsPullback π s f (spMap φ))
    (hY : ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys Y P), Perf (OSys f S)) :
    ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P) (S : Sys X P), Perf (OSys s S) := by
  obtain ⟨P, _, _, S, hS⟩ := hY
  letI := φ.toAlgebra
  obtain ⟨S', m, -⟩ := hB R₀ R Y X f s π h inferInstance P S
  exact ⟨P, inferInstance, inferInstance, S', hP R₀ P (OSys f S) hS R (OSys s S') m⟩

theorem perfSt_of_spreads : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) →
    GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → DescentSt → LowSt → SysBCSt → FinCohSt → PerfNoethSt →
    PerfBaseSt → PerfSt := by
  intro hS hSm hPr _ _ hBC hF hN hP R _ X s hsm hpr
  obtain ⟨R₀, _, φ, Y₀, f₀, π, hm⟩ := hS R X s inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := hSm R R₀ φ X Y₀ s f₀ π hm hsm
  have m₁ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := hPr R R₁ φ₁ X _ s _ _ m₁ hpr
  have m₂ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₂ ft₂ m₁
  have sm₁' : Smooth (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (Limits.pullback.snd (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  haveI : IsNoetherianRing R₂ := Algebra.FiniteType.isNoetherianRing ℤ R₂
  exact perf_base hBC hP φ₂ _ s _ m₂.2.2.2.2 (perf_noeth hF hN R₂ _ _)

end GlobalTheory.CompanionTheory.PerfModels
end
end

