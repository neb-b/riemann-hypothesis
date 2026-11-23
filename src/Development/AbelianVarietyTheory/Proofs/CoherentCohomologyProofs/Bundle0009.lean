module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijOnKerAndExactOfQuasiIsoBaseChange
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem bijOn_ker_and_exact_of_quasiIso {R : Type} [CommRing R]
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C) (h : QuasiIso φ) :
    Set.BijOn (φ.f 0).hom (LinearMap.ker (K.d 0 1).hom) (LinearMap.ker (C.d 0 1).hom) ∧
      (Function.Exact (C.d 0 1).hom (C.d 1 2).hom → Function.Exact (K.d 0 1).hom (K.d 1 2).hom) := by
  have h0 := (quasiIsoAt_zero_iff φ).1 inferInstance
  have h1 := (quasiIsoAt_succ_iff φ 0).1 inferInstance
  refine ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun hC x => ⟨fun hx => ?_, ?_⟩⟩
  · have hx' : (K.d 0 1).hom x = 0 := hx
    change (C.d 0 1).hom ((φ.f 0).hom x) = 0
    rw [cochain_comm_apply, hx', map_zero]
  · have hx' : (K.d 0 1).hom x = 0 := hx
    have hy' : (K.d 0 1).hom y = 0 := hy
    exact sub_eq_zero.1 (h0.2 (x - y) (by rw [map_sub, hx', hy', sub_zero])
      (by rw [map_sub, hxy, sub_self]))
  · obtain ⟨x, hx, hx'⟩ := h0.1 y hy
    exact ⟨x, hx, hx'⟩
  · obtain ⟨z, hz⟩ := (hC ((φ.f 1).hom x)).1 (by rw [cochain_comm_apply, hx, map_zero])
    exact h1.2 x z hx hz
  · rintro ⟨w, rfl⟩
    exact cochain_d_d_apply K 0 1 2 w

theorem bijOn_ker_and_exact_of_quasiIso_baseChange (R R' : Type) [CommRing R] [CommRing R']
    [inst : Algebra R R'] (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C)
    (h : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    Set.BijOn ((φ.f 0).hom.baseChange R') (LinearMap.ker ((K.d 0 1).hom.baseChange R'))
        (LinearMap.ker ((C.d 0 1).hom.baseChange R')) ∧
      (Function.Exact ((C.d 0 1).hom.baseChange R') ((C.d 1 2).hom.baseChange R') →
        Function.Exact ((K.d 0 1).hom.baseChange R') ((K.d 1 2).hom.baseChange R')) := by
  have key := bijOn_ker_and_exact_of_quasiIso _ h
  clear h
  generalize hf : algebraMap R R' = f at key
  have e : inst = f.toAlgebra := Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)
  subst e
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexExactAtOfMonomialBasis
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

variable {ι : Type} (R : Type) [CommRing R]

def Cube.above (w : Finset ι) : Cube.{0} ι R :=
  Cube.mk (fun s => ModuleCat.of R (PLift (w ⊆ s) →₀ R))
    (fun h => Finsupp.lmapDomain R R fun x => ⟨x.down.trans h⟩)
    (fun _ _ => Finsupp.mapDomain_id)
    (fun _ _ _ => Finsupp.mapDomain_comp.symm)

theorem cubeComplex_above_exactAt [LinearOrder ι] [Fintype ι] (w : Finset ι) {p : ℕ}
    (hp : p ≠ Fintype.card ι) : (cubeComplex (Cube.above R w)).ExactAt p := by
  by_cases hw : w = Finset.univ
  · subst hw
    have : Subsingleton (Cube.Term (Cube.above R (Finset.univ : Finset ι)) p) := by
      refine ⟨fun x y => funext fun s => ?_⟩
      refine Finsupp.ext fun a => absurd ?_ hp
      rw [← s.2, Finset.univ_subset_iff.1 a.down, Finset.card_univ]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Cube.Term _ p)))
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ w := by
      by_contra! h
      exact hw (Finset.eq_univ_iff_forall.2 h)
    refine cubeComplex_exactAt_of_bijective _ i (fun s _ => ?_) p
    refine ⟨Finsupp.mapDomain_injective fun _ _ _ => Subsingleton.elim _ _,
      Finsupp.mapDomain_surjective fun x => ⟨⟨?_⟩, Subsingleton.elim _ _⟩⟩
    exact (Finset.subset_insert_iff_of_notMem hi).1 x.down

variable {R}

def monomialCoord {κ : Type} (T : κ → Finset ι) {s : Finset ι} {M : Type} [AddCommGroup M]
    [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M) :
    M ≃ₗ[R] ⨁ a, (PLift (T a ⊆ s) →₀ R) :=
  b.repr ≪≫ₗ Finsupp.domLCongr (Equiv.sigmaPLiftEquivSubtype fun a => T a ⊆ s).symm ≪≫ₗ
    sigmaFinsuppLequivDFinsupp R

theorem monomialCoord_basis {κ : Type} [DecidableEq κ] (T : κ → Finset ι) {s : Finset ι} {M : Type}
    [AddCommGroup M] [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M)
    (a : {a : κ // T a ⊆ s}) :
    monomialCoord T b (b a) =
      DirectSum.lof R κ (fun a => PLift (T a ⊆ s) →₀ R) a.1 (Finsupp.single ⟨a.2⟩ 1) := by
  simp only [monomialCoord, LinearEquiv.trans_apply, Module.Basis.repr_self, Finsupp.domLCongr_single]
  exact sigmaFinsuppEquivDFinsupp_single _ _

theorem cubeComplex_exactAt_of_monomialBasis (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩)
    (p : ℕ) (hp : p ≠ Fintype.card ι) : (cubeComplex A).ExactAt p := by
  classical
  let e : A ≅ Cube.directSum fun a => Cube.above R (T a) :=
    Cube.isoMk (fun s => monomialCoord T (b s)) fun {s t} h x => by
      have : (monomialCoord T (b t)).toLinearMap ∘ₗ Cube.res A h =
          (DirectSum.lmap fun a => Finsupp.lmapDomain R R
            fun x : PLift (T a ⊆ s) => (⟨x.down.trans h⟩ : PLift (T a ⊆ t))) ∘ₗ
            (monomialCoord T (b s)).toLinearMap := by
        refine (b s).ext fun a => ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hb, monomialCoord_basis,
          DirectSum.lmap_lof, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      exact congr($this x)
  exact (exactAt_iff_of_quasiIsoAt ((cubeFunctor ι R).mapIso e).hom p).2
    ((cubeComplex_directSum_exactAt_iff _ p).2 fun a => cubeComplex_above_exactAt R (T a) hp)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexOfNoetherianModel
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem Cube.nonempty_extendScalars_iso_baseChange {ι : Type} {R₀ R : Type} [CommRing R₀]
    [CommRing R] [inst : Algebra R₀ R] (C : Cube.{0} ι R₀) :
    Nonempty (C ⋙ ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R) ≅ Cube.baseChange R C) := by
  obtain ⟨f, rfl⟩ : ∃ f : R₀ →+* R, inst = f.toAlgebra := ⟨_, toAlgebra_algebraMap.symm⟩
  exact ⟨NatIso.ofComponents (fun s => Iso.refl _) fun h => by
    rw [Iso.refl_hom, Iso.refl_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm⟩

theorem finite_projective_extendScalars_obj {R₀ R : Type} [CommRing R₀] [CommRing R]
    (f : R₀ →+* R) (M : ModuleCat.{0} R₀) [Module.Finite R₀ M] [Module.Projective R₀ M] :
    Module.Finite R ((ModuleCat.extendScalars.{0, 0, 0} f).obj M) ∧
      Module.Projective R ((ModuleCat.extendScalars.{0, 0, 0} f).obj M) := by
  letI := f.toAlgebra
  exact ⟨inferInstanceAs (Module.Finite R (R ⊗[R₀] M)),
    inferInstanceAs (Module.Projective R (R ⊗[R₀] M))⟩

theorem quasiIso_extendScalars_extendScalars {R₀ R R' : Type} [CommRing R₀] [CommRing R]
    [CommRing R'] (f : R₀ →+* R) (g : R →+* R') {K L : CochainComplex (ModuleCat.{0} R₀) ℕ}
    (φ : K ⟶ L)
    (h : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (g.comp f)).mapHomologicalComplex _).map φ)) :
    QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).map
      (((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).map φ)) := by
  let e := NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{0} f g)
    (ComplexShape.up ℕ)
  have h' : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} f ⋙
      ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).map φ) := by
    rw [← NatIso.naturality_1 e φ]
    infer_instance
  exact h'

theorem exists_finite_projective_complex_of_noetherian_model :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R] (C₀ : Cube.{0} ι R₀) (A : Cube.{0} ι R) (θ : Cube.baseChange R C₀ ⟶ A), (∀ s : Finset ι, s.Nonempty → Module.Flat R₀ (C₀.obj s)) → (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) → (∀ s : Finset ι, s.Nonempty → Function.Bijective (θ.app s).hom) → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechComplex A), (∀ p, Fintype.card ι ≤ p + 1 → IsZero (K.X (p + 1))) ∧ (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  intro ι _ _ R₀ R _ _ _ _ C₀ A θ hflat hfin hθ
  obtain ⟨K₀, φ₀, h0, h1, -, h2, -, -, h3⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} (cechComplex C₀) (Fintype.card ι - 1)
      (fun p hp => isZero_cechComplex_X C₀ (by omega))
      (fun p => Cube.flat_term C₀ (p + 1) fun s hs => hflat s (Finset.card_pos.1 (by omega))) hfin
  obtain ⟨e⟩ := Cube.nonempty_extendScalars_iso_baseChange (R := R) C₀
  let F := (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let ψ : F.obj (cechComplex C₀) ≅ cechComplex A :=
    cechExtendScalarsIso (algebraMap R₀ R) C₀ ≪≫ (cechFunctor ι R).mapIso e ≪≫
      @asIso _ _ _ _ (cechComplexMap θ) (isIso_cechComplexMap θ hθ)
  refine ⟨F.obj K₀, F.map φ₀ ≫ ψ.hom, fun p hp => ?_, fun p => ?_, fun R' _ _ => ?_⟩
  · exact (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R)).map_isZero (h0 _ (by omega))
  · have := h1 p
    have := h2 p
    exact finite_projective_extendScalars_obj (algebraMap R₀ R) (K₀.X p)
  · letI := ((algebraMap R R').comp (algebraMap R₀ R)).toAlgebra
    have := quasiIso_extendScalars_extendScalars (algebraMap R₀ R) (algebraMap R R') φ₀ (h3 R')
    rw [Functor.map_comp]
    infer_instance

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct in
theorem _root_.GlobalTheory.exists_homogeneous_family_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ], (∀ i : ι, ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M)) → ∃ (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ ℳ (d l)) ∧ ∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (Set.range g) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ hT
  choose T hT using hT
  choose S hS using fun m : M => _root_.GlobalTheory.exists_sum_grProj ℳ m
  classical
  let G : Finset (ℤ × M) := (Finset.univ.biUnion T).biUnion fun t =>
    (S t).image fun j => (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t)
  refine ⟨G.card, fun l => (G.equivFin.symm l).1.1, fun l => (G.equivFin.symm l).1.2,
    fun l => ?_, fun i y => ?_⟩
  · have hmem := (G.equivFin.symm l).2
    obtain ⟨t, -, hj⟩ := Finset.mem_biUnion.1 hmem
    obtain ⟨j, -, hjeq⟩ := Finset.mem_image.1 hj
    show (G.equivFin.symm l : ℤ × M).2 ∈ ℳ (G.equivFin.symm l : ℤ × M).1
    rw [← hjeq]
    exact _root_.GlobalTheory.GradedHilbert.proj_mem ℳ j t
  · obtain ⟨k, hk⟩ := hT i y
    refine ⟨k, Submodule.span_le.2 ?_ hk⟩
    intro t ht
    rw [← hS t]
    refine Submodule.sum_mem _ fun j hj => Submodule.subset_span ?_
    have hG : (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t) ∈ G :=
      Finset.mem_biUnion.2 ⟨t, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩,
        Finset.mem_image.2 ⟨j, hj, rfl⟩⟩
    exact ⟨G.equivFin ⟨_, hG⟩, by simp⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMatricesOfProjectiveComplex
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem projMatrix_abstract {S : Type} [CommRing S] {P₀ P₁ P₂ F₀ F₁ G₁ G₂ : Type}
    [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂]
    [AddCommGroup F₀] [Module S F₀] [AddCommGroup F₁] [Module S F₁]
    [AddCommGroup G₁] [Module S G₁] [AddCommGroup G₂] [Module S G₂]
    (d₀ : P₀ →ₗ[S] P₁) (d₁ : P₁ →ₗ[S] P₂) (p₀ : F₀ →ₗ[S] P₀) (s₀ : P₀ →ₗ[S] F₀)
    (p₁ : F₁ →ₗ[S] P₁) (s₁ : P₁ →ₗ[S] F₁) (D₀ : F₀ →ₗ[S] G₁) (D₁ : G₁ →ₗ[S] G₂)
    (q₁ : G₁ →ₗ[S] F₁) (q₀ : G₁ →ₗ[S] F₀) (i₁ : F₁ →ₗ[S] G₁) (i₀ : F₀ →ₗ[S] G₁)
    (r₂ : G₂ →ₗ[S] P₂) (r₁ : G₂ →ₗ[S] F₁) (r₀ : G₂ →ₗ[S] P₀)
    (h₀ : p₀ ∘ₗ s₀ = LinearMap.id) (h₁ : p₁ ∘ₗ s₁ = LinearMap.id)
    (hq₁ : q₁ ∘ₗ D₀ = s₁ ∘ₗ d₀ ∘ₗ p₀) (hq₀ : q₀ ∘ₗ D₀ = LinearMap.id - s₀ ∘ₗ p₀)
    (hi : i₁ ∘ₗ q₁ + i₀ ∘ₗ q₀ = LinearMap.id)
    (hr₂ : r₂ ∘ₗ D₁ = d₁ ∘ₗ p₁ ∘ₗ q₁) (hr₁ : r₁ ∘ₗ D₁ = q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁)
    (hr₀ : r₀ ∘ₗ D₁ = p₀ ∘ₗ q₀) :
    Set.BijOn p₀ {v | D₀ v = 0} (LinearMap.ker d₀) ∧
      (Function.Exact d₀ d₁ → ∀ w, D₁ w = 0 → ∃ v, D₀ v = w) := by
  have h₀ : ∀ x, p₀ (s₀ x) = x := fun x => LinearMap.congr_fun h₀ x
  have h₁ : ∀ x, p₁ (s₁ x) = x := fun x => LinearMap.congr_fun h₁ x
  have hq₁ : ∀ x, q₁ (D₀ x) = s₁ (d₀ (p₀ x)) := fun x => LinearMap.congr_fun hq₁ x
  have hq₀ : ∀ x, q₀ (D₀ x) = x - s₀ (p₀ x) := fun x => LinearMap.congr_fun hq₀ x
  have hi : ∀ x, i₁ (q₁ x) + i₀ (q₀ x) = x := fun x => LinearMap.congr_fun hi x
  have hr₂ : ∀ x, r₂ (D₁ x) = d₁ (p₁ (q₁ x)) := fun x => LinearMap.congr_fun hr₂ x
  have hr₁ : ∀ x, r₁ (D₁ x) = q₁ x - s₁ (p₁ (q₁ x)) := fun x => LinearMap.congr_fun hr₁ x
  have hr₀ : ∀ x, r₀ (D₁ x) = p₀ (q₀ x) := fun x => LinearMap.congr_fun hr₀ x
  have key : ∀ v, D₀ v = 0 → s₀ (p₀ v) = v := fun v hv => by
    have := hq₀ v
    rw [hv, map_zero] at this
    exact (sub_eq_zero.mp this.symm).symm
  refine ⟨⟨fun v hv => ?_, fun v hv v' hv' h => ?_, fun x hx => ⟨s₀ x, ?_, h₀ x⟩⟩, ?_⟩
  · have hv : D₀ v = 0 := hv
    have := congrArg p₁ (hq₁ v)
    rw [hv, map_zero, map_zero, h₁] at this
    exact this.symm
  · rw [← key v hv, ← key v' hv', h]
  · have hx : d₀ x = 0 := hx
    show D₀ (s₀ x) = 0
    rw [← hi (D₀ (s₀ x)), hq₁, hq₀, h₀, hx]
    simp
  · intro hex w hw
    have e₂ := hr₂ w
    have e₁ := hr₁ w
    have e₀ := hr₀ w
    rw [hw, map_zero] at e₂ e₁ e₀
    obtain ⟨x, hx⟩ := (hex _).mp e₂.symm
    refine ⟨s₀ x + q₀ w, ?_⟩
    have hp : p₀ (s₀ x + q₀ w) = x := by rw [map_add (f := _), h₀, ← e₀, add_zero]
    rw [← hi (D₀ _), hq₁, hq₀, hp, hx, ← sub_eq_zero.mp e₁.symm, add_sub_cancel_left, hi]

theorem projMatrix_mulVec {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) (x : R' ⊗[R] (Fin a → R)) :
    ((LinearMap.toMatrix' f).map (algebraMap R R')).mulVec
        (TensorProduct.piScalarRight R R' R' (Fin a) x) =
      TensorProduct.piScalarRight R R' R' (Fin b) (f.baseChange R' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Matrix.mulVec_add, hx, hy]
  | tmul r y =>
    ext i
    have hy : f y = (LinearMap.toMatrix' f).mulVec y := by
      rw [LinearMap.toMatrix'_mulVec]
    rw [LinearMap.baseChange_tmul, hy]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, Algebra.smul_def, map_mul,
      map_sum, Finset.sum_mul, mul_assoc]

theorem projMatrix_sum {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    {a : ℕ} {P : Type} [AddCommGroup P] [Module R P] (p : (Fin a → R) →ₗ[R] P)
    (x : R' ⊗[R] (Fin a → R)) :
    ∑ k, TensorProduct.piScalarRight R R' R' (Fin a) x k ⊗ₜ[R] p (Pi.single k 1) =
      p.baseChange R' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul r y =>
    have hy : p y = ∑ k, y k • p (Pi.single k 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_smul, ← map_sum]
      congr 1
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [LinearMap.baseChange_tmul, hy]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      TensorProduct.tmul_sum, TensorProduct.smul_tmul]

theorem exists_matrices_of_projective_complex :
    ∀ (R : Type) [CommRing R] (P₀ P₁ P₂ : Type) [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₀] [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (d₀ : P₀ →ₗ[R] P₁) (d₁ : P₁ →ₗ[R] P₂), d₁ ∘ₗ d₀ = 0 → ∃ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R) (u : Fin a → P₀), D₁ * D₀ = 0 ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], Set.BijOn (fun v : Fin a → R' => ∑ k, v k ⊗ₜ[R] u k) {v | (D₀.map (algebraMap R R')).mulVec v = 0} (LinearMap.ker (d₀.baseChange R')) ∧ (Function.Exact (d₀.baseChange R') (d₁.baseChange R') → ∀ w : Fin b → R', (D₁.map (algebraMap R R')).mulVec w = 0 → ∃ v, (D₀.map (algebraMap R R')).mulVec v = w) := by
  intro R _ P₀ P₁ P₂ _ _ _ _ _ _ _ _ _ _ _ _ d₀ d₁ hd
  obtain ⟨n₀, p₀, s₀, -, -, h₀⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₀
  obtain ⟨n₁, p₁, s₁, -, -, h₁⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₁
  obtain ⟨n₂, p₂, s₂, -, -, h₂⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₂
  have hE : ∀ n m : ℕ, Nonempty ((Fin (n + m) → R) ≃ₗ[R] (Fin n → R) × (Fin m → R)) :=
    fun n m => ⟨(LinearEquiv.funCongrLeft R R finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ R R)⟩
  obtain ⟨E⟩ := hE n₁ n₀
  obtain ⟨E'⟩ := hE n₂ (n₁ + n₀)
  have h₀' : ∀ x, p₀ (s₀ x) = x := fun x => LinearMap.congr_fun h₀ x
  have h₁' : ∀ x, p₁ (s₁ x) = x := fun x => LinearMap.congr_fun h₁ x
  have h₂' : ∀ x, p₂ (s₂ x) = x := fun x => LinearMap.congr_fun h₂ x
  have hd' : ∀ x, d₁ (d₀ x) = 0 := fun x => LinearMap.congr_fun hd x
  let q₁ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin n₁ → R) := LinearMap.fst R _ _ ∘ₗ E.toLinearMap
  let q₀ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin n₀ → R) := LinearMap.snd R _ _ ∘ₗ E.toLinearMap
  let i₁ : (Fin n₁ → R) →ₗ[R] (Fin (n₁ + n₀) → R) := E.symm.toLinearMap ∘ₗ LinearMap.inl R _ _
  let i₀ : (Fin n₀ → R) →ₗ[R] (Fin (n₁ + n₀) → R) := E.symm.toLinearMap ∘ₗ LinearMap.inr R _ _
  let f₀ : (Fin n₀ → R) →ₗ[R] (Fin (n₁ + n₀) → R) :=
    E.symm.toLinearMap ∘ₗ LinearMap.prod (s₁ ∘ₗ d₀ ∘ₗ p₀) (LinearMap.id - s₀ ∘ₗ p₀)
  let f₁ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin (n₂ + (n₁ + n₀)) → R) :=
    E'.symm.toLinearMap ∘ₗ LinearMap.prod (s₂ ∘ₗ d₁ ∘ₗ p₁ ∘ₗ q₁)
      (E.symm.toLinearMap ∘ₗ LinearMap.prod (q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁) (s₀ ∘ₗ p₀ ∘ₗ q₀))
  let r₂ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] P₂ := p₂ ∘ₗ LinearMap.fst R _ _ ∘ₗ E'.toLinearMap
  let r₁ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] (Fin n₁ → R) :=
    q₁ ∘ₗ LinearMap.snd R _ _ ∘ₗ E'.toLinearMap
  let r₀ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] P₀ :=
    p₀ ∘ₗ q₀ ∘ₗ LinearMap.snd R _ _ ∘ₗ E'.toLinearMap
  have hq₁ : q₁ ∘ₗ f₀ = s₁ ∘ₗ d₀ ∘ₗ p₀ := LinearMap.ext fun x => by simp [q₁, f₀]
  have hq₀ : q₀ ∘ₗ f₀ = LinearMap.id - s₀ ∘ₗ p₀ := LinearMap.ext fun x => by simp [q₀, f₀]
  have hi : i₁ ∘ₗ q₁ + i₀ ∘ₗ q₀ = LinearMap.id := LinearMap.ext fun x => by
    simp [q₀, q₁, i₀, i₁, ← map_add (f := _)]
  have hr₂ : r₂ ∘ₗ f₁ = d₁ ∘ₗ p₁ ∘ₗ q₁ := LinearMap.ext fun x => by simp [r₂, f₁, h₂']
  have hr₁ : r₁ ∘ₗ f₁ = q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁ := LinearMap.ext fun x => by simp [r₁, f₁, q₁]
  have hr₀ : r₀ ∘ₗ f₁ = p₀ ∘ₗ q₀ := LinearMap.ext fun x => by simp [r₀, f₁, q₀, h₀']
  have hf : f₁ ∘ₗ f₀ = 0 := LinearMap.ext fun x => by
    have e₁ : q₁ (f₀ x) = s₁ (d₀ (p₀ x)) := LinearMap.congr_fun hq₁ x
    have e₀ : q₀ (f₀ x) = x - s₀ (p₀ x) := LinearMap.congr_fun hq₀ x
    simp [f₁, e₁, e₀, h₀', h₁', hd']
  refine ⟨n₀, n₁ + n₀, n₂ + (n₁ + n₀), LinearMap.toMatrix' f₀, LinearMap.toMatrix' f₁,
    fun k => p₀ (Pi.single k 1), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hf, map_zero]
  intro R' _ _
  obtain ⟨hB, hX⟩ := projMatrix_abstract (d₀.baseChange R') (d₁.baseChange R')
    (p₀.baseChange R') (s₀.baseChange R') (p₁.baseChange R') (s₁.baseChange R')
    (f₀.baseChange R') (f₁.baseChange R') (q₁.baseChange R') (q₀.baseChange R')
    (i₁.baseChange R') (i₀.baseChange R') (r₂.baseChange R') (r₁.baseChange R')
    (r₀.baseChange R')
    (by rw [← LinearMap.baseChange_comp, h₀, LinearMap.baseChange_id])
    (by rw [← LinearMap.baseChange_comp, h₁, LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, hq₁])
    (by simp only [← LinearMap.baseChange_comp, hq₀, LinearMap.baseChange_sub,
      LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, ← LinearMap.baseChange_add, hi,
      LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, hr₂])
    (by simp only [← LinearMap.baseChange_comp, hr₁, LinearMap.baseChange_sub])
    (by simp only [← LinearMap.baseChange_comp, hr₀])
  constructor
  · let e := TensorProduct.piScalarRight R R' R' (Fin n₀)
    have hmem : ∀ x, (((LinearMap.toMatrix' f₀).map (algebraMap R R')).mulVec (e x) = 0) ↔
        f₀.baseChange R' x = 0 := fun x => by
      rw [projMatrix_mulVec, LinearEquiv.map_eq_zero_iff]
    refine ⟨fun v hv => ?_, fun v hv v' hv' h => ?_, fun y hy => ?_⟩
    · obtain ⟨x, rfl⟩ := e.surjective v
      have := hB.mapsTo ((hmem x).mp hv)
      rwa [← projMatrix_sum] at this
    · obtain ⟨x, rfl⟩ := e.surjective v
      obtain ⟨x', rfl⟩ := e.surjective v'
      congr 1
      refine hB.injOn ((hmem x).mp hv) ((hmem x').mp hv') ?_
      rw [← projMatrix_sum, ← projMatrix_sum]
      exact h
    · obtain ⟨x, hx, rfl⟩ := hB.surjOn hy
      exact ⟨e x, (hmem x).mpr hx, projMatrix_sum R' p₀ x⟩
  · intro hex w hw
    obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight R R' R' (Fin (n₁ + n₀))).surjective w
    rw [projMatrix_mulVec, LinearEquiv.map_eq_zero_iff] at hw
    obtain ⟨v, rfl⟩ := hX hex x hw
    exact ⟨_, projMatrix_mulVec R' f₀ v⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsWitnessesOfFormallySmoothQuotient
section
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_sum_mul_of_mem_span_range_sq {S : Type} [CommRing S] {r : ℕ} (g : Fin r → S)
    (x : S) (hx : x ∈ Ideal.span (Set.range g) * Ideal.span (Set.range g)) :
    ∃ b : Fin r → Fin r → S, x = ∑ k, ∑ l, b k l * (g k * g l) := by

  have hx' : x ∈ Ideal.span (Set.range fun p : Fin r × Fin r => g p.1 * g p.2) := by
    open Pointwise in
    have hset : Set.range g * Set.range g =
        Set.range fun p : Fin r × Fin r => g p.1 * g p.2 := by
      ext y
      simp [Set.mem_mul]
    open Pointwise in
    rwa [Ideal.span_mul_span', hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hx'
  refine ⟨fun k l => c (k, l), ?_⟩
  rw [← hc, Fintype.sum_prod_type]
  simp only [smul_eq_mul]

theorem exists_witnesses_of_formallySmooth_quotient :
    ∀ (ι : Type) [Fintype ι] (R : Type) [CommRing R] (r : ℕ) (g : Fin r → MvPolynomial ι R), Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) → ∃ (a : ι → Fin r → MvPolynomial ι R) (b : Fin r → Fin r → Fin r → MvPolynomial ι R), ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l) := by
  intro ι _ R _ r g hs
  set I : Ideal (MvPolynomial ι R) := Ideal.span (Set.range g) with hI
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I

  obtain ⟨σ, hσ⟩ := (Algebra.FormallySmooth.iff_split_surjection _ hsurj).1 hs
  have hK : RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom = I := by
    ext x
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem

  have hlift : ∀ i : ι, ∃ y : MvPolynomial ι R,
      Ideal.Quotient.mk _ y = σ (Ideal.Quotient.mkₐ R I (X i)) :=
    fun i => Ideal.Quotient.mk_surjective _
  choose y hy using hlift

  have hdiff : ∀ i, y i - X i ∈ I := by
    intro i
    have h1 := congrArg (Ideal.Quotient.mkₐ R I).kerSquareLift (hy i)
    rw [AlgHom.kerSquareLift_mk, ← AlgHom.comp_apply, hσ, AlgHom.id_apply] at h1
    exact Ideal.Quotient.eq.1 h1
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 (hdiff i)
  have hy' : ∀ i, X i + ∑ k, a i k * g k = y i := by
    intro i
    have := ha i
    simp only [smul_eq_mul] at this
    rw [this]
    ring

  have hcomp : (Ideal.Quotient.mkₐ R _).comp
      (aeval fun i => X i + ∑ k, a i k * g k : MvPolynomial ι R →ₐ[R] MvPolynomial ι R) =
      σ.comp (Ideal.Quotient.mkₐ R I) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X, hy', AlgHom.comp_apply, ← hy i]
    rfl

  have hmem : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) ∈ I * I := by
    intro j
    have hgj : Ideal.Quotient.mkₐ R I (g j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
    have h2 := AlgHom.congr_fun hcomp (g j)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hgj, map_zero, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, hK, pow_two] at h2
    exact h2
  choose b hb using fun j => exists_sum_mul_of_mem_span_range_sq g _ (hmem j)
  exact ⟨a, b, hb⟩

end GlobalTheory
end

