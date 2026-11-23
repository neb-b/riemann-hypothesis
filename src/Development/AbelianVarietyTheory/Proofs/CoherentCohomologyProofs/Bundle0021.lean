module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AcyclicSliceSecCubeOfIsAffineOpen
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type} [LinearOrder ν] [LinearOrder κ]

def sliceEmptySecCubeIso (M : LB Y) (E : ν → Y.Opens) (e : κ ↪o ν) {s₀ : Finset ν} (h₀ : s₀ = ∅) :
    Cube.slice e s₀ (secCube f M E) ≅ secCube f M fun k => E (e k) :=
  have h (t : Finset κ) : ⨅ i ∈ s₀ ∪ t.map e.toEmbedding, E i = ⨅ k ∈ t, E (e k) := by
    subst h₀
    rw [Finset.empty_union]
    refine le_antisymm (le_iInf₂ fun k hk => biInf_le _ (Finset.mem_map_of_mem _ hk))
      (le_iInf₂ fun i hi => ?_)
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hi
    exact biInf_le (fun k => E (e k)) hk
  Cube.isoMk (fun t => LinearEquiv.ofBijective (SecOnR.restrict f M (h t).ge)
      (SecOnR.restrict_bijective f (h t).ge (h t).le))
    fun {s t} _ x => (SecOnR.restrict_restrict f _ (h t).ge x).trans
      (SecOnR.restrict_restrict f (h s).ge _ x).symm

theorem acyclic_slice_secCube_of_isSeparated [Fintype κ] (hM : M.IsLB) [IsSeparated f]
    (E : ν → Y.Opens) (hE : ∀ i, IsAffineOpen (E i)) (e : κ ↪o ν) (hc : ⨆ k, E (e k) = ⊤)
    {s₀ : Finset ν} (h₀ : s₀.Nonempty) :
    (cubeComplex (Cube.slice e s₀ (secCube f M E))).Acyclic := by
  have : IsSeparated (terminal.from Y) := by
    rw [← terminal.comp_from f]
    infer_instance
  refine acyclic_slice_secCube_of_isAffineOpen R Y f M ν κ E e s₀ hM (hc ▸ le_top) fun t => ?_
  exact IsAffineOpen.biInf _ (Finset.finite_toSet _)
    (h₀.mono Finset.subset_union_left) fun i _ => hE i

theorem cechLB_homology_equiv_of_affine_covers :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ' : Type) [LinearOrder κ'] [Fintype κ'] (D' : κ' → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, IsAffineOpen (D' i)) → ⨆ i, D' i = ⊤ → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cechLB f M D').homology n) := by
  intro R _ Y f M κ _ _ D κ' _ _ D' hM hf hD hc hD' hc' n
  let E : κ ⊕ₗ κ' → Y.Opens := fun u => Sum.elim D D' (ofLex u)
  have hE (u : κ ⊕ₗ κ') : IsAffineOpen (E u) := by
    rcases u with i | i
    exacts [hD i, hD' i]
  let e₁ := trunc₂HomologyIsoFst (secCube f M E) (fun s hs =>
    acyclic_slice_secCube_of_isSeparated f hM E hE (Cube.inrEmb κ κ') hc' hs.map) n
  let e₂ := trunc₂HomologyIsoSnd (secCube f M E) (fun t ht => by
    rw [Cube.sliceFst_eq_slice]
    exact acyclic_slice_secCube_of_isSeparated f hM E hE (Cube.inlEmb κ κ') hc ht.map) n
  let i₁ : Cube.sliceFst (secCube f M E) ∅ ≅ secCube f M D :=
    eqToIso (Cube.sliceFst_eq_slice _ _) ≪≫
      sliceEmptySecCubeIso f M E (Cube.inlEmb κ κ') (Finset.map_empty _)
  let i₂ : Cube.sliceSnd (secCube f M E) ∅ ≅ secCube f M D' :=
    sliceEmptySecCubeIso f M E (Cube.inrEmb κ κ') (Finset.map_empty _)
  exact ⟨((HomologicalComplex.homologyMapIso ((cechFunctor κ R).mapIso i₁) n).symm ≪≫ e₁.symm ≪≫
    e₂ ≪≫ HomologicalComplex.homologyMapIso ((cechFunctor κ' R).mapIso i₂) n).toLinearEquiv⟩

end GlobalTheory.AbLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw

section

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type}

theorem isAffineOpen_biInf_of_le (E : ν → Y.Opens)
    (hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V)) (u : Finset ν) {V : Y.Opens}
    (hV : IsAffineOpen V) (h : ⨅ i ∈ u, E i ≤ V) : IsAffineOpen (⨅ i ∈ u, E i) := by
  classical
  rw [← inf_eq_left.2 h]
  clear h
  induction u using Finset.induction_on with
  | empty => simpa using hV
  | insert a s _ ih =>
    rw [Finset.iInf_insert, inf_assoc]
    exact hE a _ ih

theorem acyclic_comap_secCube [LinearOrder ν] [LinearOrder κ] [Fintype κ] (hM : M.IsLB)
    (E : ν → Y.Opens) (hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V)) (e : κ ↪o ν)
    (hc : ⨆ k, E (e k) = ⊤) (s₀ : Finset ν) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : ⨅ i ∈ s₀, E i ≤ V) (g : Finset κ → Finset ν) (hg : Monotone g)
    (hgs : ∀ t, g t = s₀ ∪ t.map e.toEmbedding) :
    (cubeComplex (Cube.comap g hg (secCube f M E))).Acyclic := by
  rw [Cube.comap_congr hg (Cube.monotone_union_map e s₀) hgs]
  exact acyclic_slice_secCube_of_isAffineOpen R Y f M ν κ E e s₀ hM (hc ▸ le_top) fun t =>
    isAffineOpen_biInf_of_le E hE _ hV
      ((iInf_le_iInf_of_subset E Finset.subset_union_left).trans h)


variable (M) in
def comapSecCubeIso (E : ν → Y.Opens) (D : κ → Y.Opens) (g : Finset κ → Finset ν) (hg : Monotone g)
    (h : ∀ t, ⨅ i ∈ g t, E i = ⨅ k ∈ t, D k) :
    Cube.comap g hg (secCube f M E) ≅ secCube f M D :=
  Cube.isoMk (fun t => LinearEquiv.ofBijective (SecOnR.restrict f M (h t).ge)
      (SecOnR.restrict_bijective f (h t).ge (h t).le))
    fun hst x => (SecOnR.restrict_restrict f (iInf_le_iInf_of_subset E (hg hst)) (h _).ge x).trans
      (SecOnR.restrict_restrict f (h _).ge (iInf_le_iInf_of_subset D hst) x).symm

theorem biInf_sumVertex [LinearOrder ν] [LinearOrder κ] (E : ν ⊕ₗ κ → Y.Opens) (s : Finset ν)
    (t : Finset κ) : ⨅ i ∈ Cube.sumVertex s t, E i =
      (⨅ i ∈ s, E (toLex (Sum.inl i))) ⊓ ⨅ k ∈ t, E (toLex (Sum.inr k)) := by
  apply le_antisymm
  · exact le_inf (le_iInf₂ fun i hi => iInf₂_le _ (Cube.inl_mem_sumVertex.2 hi))
      (le_iInf₂ fun i hi => iInf₂_le _ (Cube.inr_mem_sumVertex.2 hi))
  · refine le_iInf₂ fun i hi => ?_
    obtain ⟨i | i, rfl⟩ := toLex.surjective i
    · exact inf_le_left.trans (iInf₂_le _ (Cube.inl_mem_sumVertex.1 hi))
    · exact inf_le_right.trans (iInf₂_le _ (Cube.inr_mem_sumVertex.1 hi))

end

theorem cechLB_homology_equiv_trunc₂ :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ⨆ i, U i = ⊤ → ⨆ j, W j = ⊤ → (∀ i V, IsAffineOpen V → IsAffineOpen (U i ⊓ V)) → (∀ j V, IsAffineOpen V → IsAffineOpen (W j ⊓ V)) → (∀ i j, IsAffineOpen (U i ⊓ W j)) → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cubeComplex (Cube.trunc₂ (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)))).homology (n + 2)) := by
  intro R _ Y f M κ _ _ D κ₁ _ _ U κ₂ _ _ W hM hf hD cD cU cW hU hW hUW n
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let E : (κ₁ ⊕ₗ κ₂) ⊕ₗ κ → Y.Opens := fun u =>
    Sum.elim (fun v : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex v)) D (ofLex u)
  have hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V) := by
    rintro ((i | j) | k) V hV
    · exact hU i V hV
    · exact hW j V hV
    · exact (hD k).inf hV
  let A := secCube f M E
  let e₁ := trunc₃HomologyIsoDropLast A (fun s t ⟨i, hi⟩ ⟨j, hj⟩ =>
    acyclic_comap_secCube f hM E hE (Cube.inrEmb _ _) cD
      ((Cube.sumVertex s t).map (Cube.inlEmb _ _).toEmbedding) (hUW i j)
      (le_inf
        (iInf₂_le (toLex (Sum.inl (toLex (Sum.inl i))))
          (Finset.mem_map_of_mem _ (Cube.inl_mem_sumVertex.2 hi)))
        (iInf₂_le (toLex (Sum.inl (toLex (Sum.inr j))))
          (Finset.mem_map_of_mem _ (Cube.inr_mem_sumVertex.2 hj))))
      _ (fun _ _ h => Cube.sumVertex_mono (subset_refl _) h) fun _ => rfl) (n + 2)
  let e₂ := trunc₃HomologyIsoDropFirst A (fun t w _ ⟨k, hk⟩ =>
    acyclic_comap_secCube f hM E hE (Cube.firstEmb _ _ _) cU
      ((Cube.sumVertex t w).map (Cube.lastTwoEmb _ _ _).toEmbedding) (hD k)
      (iInf₂_le (toLex (Sum.inr k)) (Finset.mem_map_of_mem _ (Cube.inr_mem_sumVertex.2 hk)))
      (fun s => Cube.sumVertex (Cube.sumVertex s t) w)
      (fun _ _ h => Cube.sumVertex_mono (Cube.sumVertex_mono h (subset_refl _)) (subset_refl _))
      fun s => (Cube.map_lastTwoEmb_union _ _ _ s t w).symm) (n + 2)
  let e₃ := trunc₂HomologyIsoSnd (Cube.lowerFace (Cube.lastTwoEmb κ₁ κ₂ κ) A) (fun w ⟨k, hk⟩ =>
    acyclic_comap_secCube f hM E hE ((Cube.inlEmb κ₂ κ).trans (Cube.lastTwoEmb κ₁ κ₂ κ)) cW
      (w.map (Cube.inrEmb _ _).toEmbedding) (hD k)
      (iInf₂_le (toLex (Sum.inr k)) (Finset.mem_map_of_mem _ hk))
      (fun t => (Cube.sumVertex t w).map (Cube.lastTwoEmb κ₁ κ₂ κ).toEmbedding)
      (fun _ _ h => Finset.map_subset_map.2 (Cube.sumVertex_mono h (subset_refl _)))
      fun t => by
        rw [Cube.sumVertex, Finset.map_union, Finset.map_map, Finset.map_map, Finset.union_comm]
        rfl) n
  let e₄ : Cube.sliceFst A ∅ ≅ secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u) :=
    comapSecCubeIso f M E _ _ (fun _ _ h => Cube.sumVertex_mono h (subset_refl _)) fun t => by
      rw [biInf_sumVertex]
      simp [E]
  let e₅ : Cube.sliceSnd A (Cube.sumVertex ∅ ∅) ≅ secCube f M D :=
    comapSecCubeIso f M E _ _ (fun _ _ h => Cube.sumVertex_mono (subset_refl _) h) fun t => by
      rw [biInf_sumVertex]
      simp [E, Cube.sumVertex]
  exact ⟨((cechHomologyMapIso
    (eqToIso (Cube.sliceSnd_lowerFace_lastTwoEmb A ∅) ≪≫ e₅) n).symm ≪≫ e₃.symm ≪≫ e₂.symm ≪≫ e₁ ≪≫
      cubeHomologyMapIso (Cube.trunc₂Iso e₄.hom fun _ _ _ _ =>
        ConcreteCategory.bijective_of_isIso (e₄.hom.app _)) (n + 2)).toLinearEquiv⟩

end GlobalTheory.AbLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors
section
namespace GlobalTheory.KFiniteVectors

open Formalism.MainNotions.S

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFiniteVectors (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {v | IsKFin ε σ v}
  zero_mem' := by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
    intro g _ x hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]
  add_mem' := by
    rintro a b ⟨S, hS, ha, hSK⟩ ⟨T, hT, hb, hTK⟩
    refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup ha hb, ?_⟩
    intro g hg x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hSK g hg y hy) (hTK g hg z hz)
  smul_mem' := by
    rintro c a ⟨S, hS, ha, hSK⟩
    exact ⟨S, hS, S.smul_mem c ha, hSK⟩

theorem mem_kFiniteVectors (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) :
    v ∈ kFiniteVectors ε σ ↔ IsKFin ε σ v := by
  exact Iff.rfl

end GlobalTheory.KFiniteVectors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw.PerfOfModel

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {Y Y' : Scheme.{0}}
  {f : Y ⟶ Spec (CommRingCat.of R)} {f' : Y' ⟶ Spec (CommRingCat.of R')} {π : Y' ⟶ Y}
  (M : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens)

def termMap (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (p : ℕ) :
    R' ⊗[R] (cechLB f M D).X p →ₗ[R'] (cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).X p :=
  secTermBaseChange M D w (p + 1)

theorem d_termMap (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (p : ℕ)
    (x : R' ⊗[R] (cechLB f M D).X p) :
    ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d p (p + 1)).hom (termMap M D w p x) =
      termMap M D w (p + 1) (((cechLB f M D).d p (p + 1)).hom.baseChange R' x) := by
  rw [cechLB_d, cechLB_d]
  exact d_secTermBaseChange M D w (p + 1) x

variable {M D}

theorem termMap_bijective [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (p : ℕ) :
    Function.Bijective (termMap M D H.w p) :=
  secTermBaseChange_bijective hM H (p + 1) fun s hs => hD s (Finset.card_pos.1 (by omega))

theorem termMap_bijOn [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    Set.BijOn (termMap M D H.w 0) (LinearMap.ker (((cechLB f M D).d 0 1).hom.baseChange R'))
      (LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom) := by
  have key (x : R' ⊗[R] (cechLB f M D).X 0) :
      termMap M D H.w 0 x ∈ LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom ↔
        x ∈ LinearMap.ker (((cechLB f M D).d 0 1).hom.baseChange R') := by
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    exact (d_termMap M D H.w 0 x).congr_left.trans
      (map_eq_zero_iff _ (termMap_bijective hM H hD 1).1)
  refine ⟨fun x hx => (key x).2 hx, (termMap_bijective hM H hD 0).1.injOn, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := (termMap_bijective hM H hD 0).2 y
  exact ⟨x, (key x).1 hy, rfl⟩

theorem exact_baseChange [Finite κ] (hM : M.IsLB)
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (h : Function.Exact ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom
      ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 1 2).hom) :
    Function.Exact (((cechLB f M D).d 0 1).hom.baseChange R')
      (((cechLB f M D).d 1 2).hom.baseChange R') := by
  intro x
  have e₁ := d_termMap M D H.w 1 x
  refine (map_eq_zero_iff _ (termMap_bijective hM H hD 2).1).symm.trans
    (e₁.congr_left.symm.trans ((h _).trans ⟨?_, ?_⟩))
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := (termMap_bijective hM H hD 0).2 y
    exact ⟨z, (termMap_bijective hM H hD 1).1 ((d_termMap M D H.w 0 z).symm.trans hy)⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, d_termMap M D H.w 0 z⟩

theorem iSup_preimage (π : Y' ⟶ Y) (hc : ⨆ i, D i = ⊤) : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hc]
  rfl

theorem coord_termMap_sum (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    {a : ℕ} (v : Fin a → R') (x : Fin a → (cechLB f M D).X 0)
    (s : {s : Finset κ // s.card = 0 + 1}) (j : M.ι)
    (h : π ⁻¹ᵁ ((⨅ i ∈ s.1, D i) ⊓ M.U j) ≤ (⨅ i ∈ s.1, π ⁻¹ᵁ D i) ⊓ (M.pull π).U fun _ => j) :
    rs Y' h (SecOnR.coord (f := f') (termMap M D w 0 (∑ k, v k ⊗ₜ[R] x k) s) fun _ => j) =
      ∑ k, cst f' (π ⁻¹ᵁ ((⨅ i ∈ s.1, D i) ⊓ M.U j)) (v k) *
        (π.app _).hom (SecOnR.coord (f := f) (x k s) j) := by
  let F : (cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).X 0 →+
      Γ(Y', π ⁻¹ᵁ ((⨅ i ∈ s.1, D i) ⊓ M.U j)) :=
    AddMonoidHom.mk' (fun y => rs Y' h (SecOnR.coord (f := f') (y s) fun _ => j))
      fun y z => map_add (rs Y' h) _ _
  change F (termMap M D w 0 _) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  change rs Y' h (SecOnR.coord (f := f') (v k • SecOnR.pull M w _ _ (preimage_biInf D π s.1).ge (x k s)) fun _ => j) = _
  refine (congrArg (rs Y' h) (SecOnR.coord_base_smul _ _ _)).trans
    ((map_mul (rs Y' h) _ _).trans (congrArg₂ (· * ·) (rs_cst f' h _) ?_))
  refine (congrArg (rs Y' h) (SecOn.coord_pullLE π (preimage_biInf D π s.1).ge (x k s) _)).trans ?_
  rw [Scheme.Hom.app_eq_appLE]
  exact GlobalTheory.LB.resG_appLE π _ _ _

end GlobalTheory.AbLaw.PerfOfModel

namespace GlobalTheory.AbLaw

open PerfOfModel

theorem perf_of_projective_model :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechLB f M D), M.IsLB → ⨆ i, D i = ⊤ → (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ((∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) → Nonempty (Perf f M) := by
  intro R _ Y f M κ _ _ D K φ hM hc hD ⟨hK, hq⟩
  haveI := fun p => (hK p).1
  haveI := fun p => (hK p).2
  obtain ⟨a, b, c, D₀, D₁, u, hcomp, hmat⟩ := exists_matrices_of_projective_complex R (K.X 0)
    (K.X 1) (K.X 2) (K.d 0 1).hom (K.d 1 2).hom
    (LinearMap.ext fun x => cochain_d_d_apply K 0 1 2 x)
  refine ⟨{
    a := a, b := b, c := c, D₀ := D₀, D₁ := D₁, comp := hcomp
    I := κ × M.ι
    W := fun p => (⨅ i ∈ ({p.1} : Finset κ), D i) ⊓ M.U p.2
    ch := fun p => p.2
    le := fun _ => inf_le_right
    cover := ?_
    u := fun k p => SecOnR.coord (f := f) ((φ.f 0).hom (u k) ⟨{p.1}, Finset.card_singleton _⟩) p.2
    sec := ?_
    exact := ?_ }⟩
  · simp only [Finset.iInf_singleton]
    rw [iSup_prod]
    refine top_unique fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ y))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨j, hi, hj⟩⟩
  · intro R' _ g Y' π f' H
    letI := g.toAlgebra
    have B := ((termMap_bijOn hM H hD).comp
      (bijOn_ker_and_exact_of_quasiIso_baseChange R R' K _ φ (hq R')).1).comp (hmat R').1
    let S := CechOne.secKerEquiv (M.pull π) f' (iSup_preimage π hc)
    refine ⟨(B.equiv _).trans S.symm.toEquiv, fun v p => ?_⟩
    have hv : (S (S.symm (B.equiv _ v))).1 =
        termMap M D H.w 0 (∑ k, v.1 k ⊗ₜ[R] (φ.f 0).hom (u k)) := by
      rw [S.apply_symm_apply]
      change termMap M D H.w 0 ((φ.f 0).hom.baseChange R' (∑ k, v.1 k ⊗ₜ[R] u k)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum ((φ.f 0).hom.baseChange R')]
      rfl
    have hle : π ⁻¹ᵁ ((⨅ i ∈ ({p.1} : Finset κ), D i) ⊓ M.U p.2) ≤
        (⨅ i ∈ ({p.1} : Finset κ), π ⁻¹ᵁ D i) ⊓ (M.pull π).U fun _ => p.2 :=
      le_inf ((π.preimage_mono inf_le_left).trans (preimage_biInf D π _).le)
        (le_pull M π inf_le_right)
    refine Eq.trans ?_ (coord_termMap_sum H.w v.1 (fun k => (φ.f 0).hom (u k))
      ⟨{p.1}, Finset.card_singleton _⟩ p.2 hle)
    rw [← hv, CechOne.secKerEquiv_val]
    exact (rs_rs inf_le_right hle _).symm
  · intro R' _ g Y' π f' H h1
    letI := g.toAlgebra
    refine (hmat R').2 ((bijOn_ker_and_exact_of_quasiIso_baseChange R R' K _ φ (hq R')).2
      (exact_baseChange hM H hD ?_))
    rw [cechLB_d f' _ _ 0, cechLB_d f' _ _ 1]
    exact GlobalTheory.Cohom.exact_cech_one_of_h1Zero R' Y' f' _ κ _ (LB.isLB_pull hM π)
      (iSup_preimage π hc) h1

end GlobalTheory.AbLaw
end
end

