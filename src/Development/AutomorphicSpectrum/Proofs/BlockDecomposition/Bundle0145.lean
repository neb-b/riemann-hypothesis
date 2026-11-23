module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0133
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0134
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0136
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLoweringDerivationFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0137

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicallyIndependentCoordsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraically_independent_coords : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), IsIntegral X → 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → (AlgebraicIndependent K fun k => Ideal.Quotient.mk (homIdeal i) (y k)) → (V : Set X).Nonempty → letI := (strV q V).toAlgebra; AlgebraicIndependent K (tV i y hy V hV) := by
  first | exact @GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV | exact GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV | (intros; apply GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxEvaluationPullbackLeftRightStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_evaluation_pullback_left_right : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1) (_ : dn F 1 x = 0), pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 ∧ pulln (boxE F T₀ ε) 1 (pulln (boxR F) 1 x) = x := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR | exact GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR | (intros; apply GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechStructureSheafComparisonStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_structure_sheaf_comparison : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of R)) (P : Type) [SemilatticeInf P]
    (S : MainStatements.Hodge.Sys X P) {κ : Type} [LinearOrder κ] (e : κ → P) (n : ℕ),
    letI := GlobalTheory.algebraΓOfHom s
    Nonempty (((cechOf e).obj (toMod (MainStatements.Hodge.OSys s S))).homology n ≃ₗ[R]
      GlobalTheory.cechH R (GlobalTheory.structureModule X) ⊤ (fun i ↦ (S.u (e i)).1) n) :=
  @cech_OSys_homology_equiv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassZeroCocycleTensorCoboundary
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.Axis

theorem rTensor_cocycle_eq_coboundary_of_class_eq_zero :
    ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (N : Type) [AddCommGroup N] [Module R N] (t : Z1 F ⊗[R] N), (H1.mk F).rTensor N t = 0 →
    ∃ g : ∀ T : C, F.obj T ⊗[R] N, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T) := by
  intro R _ C _ F N _ _ t ht
  have hex : Function.Exact ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) (H1.mk F) :=
    LinearMap.exact_map_mkQ_range _
  obtain ⟨u, rfl⟩ := (rTensor_exact N hex (H1.mk_surjective F) t).1 ht
  refine ⟨fun T => (LinearMap.proj T : C0 F →ₗ[R] F.obj T).rTensor N u, fun T T' φ => ?_⟩
  have key : evZ F φ ∘ₗ (d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F) =
      (LinearMap.proj T' : C0 F →ₗ[R] F.obj T') -
        (mp F φ).toLinearMap ∘ₗ (LinearMap.proj T : C0 F →ₗ[R] F.obj T) := by
    ext g
    rfl
  rw [← LinearMap.rTensor_comp_apply, key, LinearMap.rTensor_sub, LinearMap.sub_apply,
    LinearMap.rTensor_comp_apply]

end GlobalTheory.CompanionTheory.Axis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainCohomologyNerveHomologyEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_cohomology_nerve_homology_equiv : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveCx.obj (toMod F)).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveCx.obj (toMod F)).homology (n + 1)) :=
  @GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleOnProductFromSecondFactor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem mp_box_tmul {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {a a' b b' : C}
    (φ : a ⟶ a') (ψ : b ⟶ b') (u : F.obj a) (v : F.obj b) :
    mp (box F) (show ((a, b) : C × C) ⟶ (a', b') from (φ, ψ)) (u ⊗ₜ[R] v) = mp F φ u ⊗ₜ[R] mp F ψ v :=
  rfl

theorem exists_pull_of_vanish_fst (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hU : USt F) (f : Z1 (box F))
    (hf : ∀ (a a' b : C) (φ : a ⟶ a'), f.1 (a, b) (a', b) (φ, 𝟙 b) = 0) :
    ∃ y : Z1 F, (boxR F).pullbackOneCocycle y = f := by

  have hk : ∀ {b b' : C} (ψ : b ⟶ b') {a a' : C} (φ : a ⟶ a'),
      f.1 (a', b) (a', b') (𝟙 a', ψ) =
        mp (box F) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b'))
          (f.1 (a, b) (a, b') (𝟙 a, ψ)) := by
    intro b b' ψ a a' φ
    have e1 := Z1.comp f (T := (a, b)) (T' := (a', b)) (T'' := (a', b'))
      (φ, 𝟙 b) (𝟙 a', ψ)
    have e2 := Z1.comp f (T := (a, b)) (T' := (a, b')) (T'' := (a', b'))
      (𝟙 a, ψ) (φ, 𝟙 b')
    have e : (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) ≫
        (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', ψ)) =
        (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) ≫
        (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b')) := by
      simp
    rw [e, e2, hf a a' b' φ, add_zero, hf a a' b φ, map_zero, zero_add] at e1
    exact e1.symm
  have hcomm : ∀ {a a' b' : C} (φ : a ⟶ a') (x : F.obj a ⊗[R] F.obj b'),
      TensorProduct.comm R (F.obj a') (F.obj b')
          (mp (box F) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b')) x) =
        (mp F φ).toLinearMap.lTensor (F.obj b') (TensorProduct.comm R (F.obj a) (F.obj b') x) := by
    intro a a' b' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => rw [mp_box_tmul, mp_id]; simp
    | add u v hu hv => simp only [map_add (f := _), hu, hv]

  have hex : ∀ {b b' : C} (ψ : b ⟶ b'), ∃! m : F.obj b', ∀ a : C,
      f.1 (a, b) (a, b') (𝟙 a, ψ) = (1 : F.obj a) ⊗ₜ[R] m := by
    intro b b' ψ
    obtain ⟨m, hm, hu⟩ := hU (F.obj b')
      (fun a ↦ TensorProduct.comm R (F.obj a) (F.obj b') (f.1 (a, b) (a, b') (𝟙 a, ψ)))
      (fun a a' φ ↦ by rw [hk ψ φ, hcomm])
    have hiff : ∀ (a : C) (m' : F.obj b'),
        TensorProduct.comm R (F.obj a) (F.obj b') (f.1 (a, b) (a, b') (𝟙 a, ψ)) = m' ⊗ₜ[R] (1 : F.obj a) ↔
          f.1 (a, b) (a, b') (𝟙 a, ψ) = (1 : F.obj a) ⊗ₜ[R] m' := by
      intro a m'
      exact (TensorProduct.comm R (F.obj a) (F.obj b')).injective.eq_iff' (TensorProduct.comm_tmul R _ _ _ _)
    exact ⟨m, fun a ↦ (hiff a m).1 (hm a), fun m' h ↦ hu m' fun a ↦ (hiff a m').2 (h a)⟩
  choose y hy huniq using @hex
  refine ⟨⟨fun b b' ψ ↦ y ψ, fun b b' b'' ψ χ ↦ ?_⟩, ?_⟩
  · refine (huniq (ψ ≫ χ) _ fun a ↦ ?_).symm
    have e := Z1.comp f (T := (a, b)) (T' := (a, b')) (T'' := (a, b''))
      (𝟙 a, ψ) (𝟙 a, χ)
    have e' : (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) ≫
        (show ((a, b') : C × C) ⟶ (a, b'') from (𝟙 a, χ)) = (𝟙 a, ψ ≫ χ) := by
      simp
    rw [e', hy ψ a, hy χ a] at e
    refine e.trans ?_
    rw [mp_box_tmul, mp_id, TensorProduct.tmul_add]
  · refine Subtype.ext ?_
    funext T T' φ
    obtain ⟨a, b⟩ := T
    obtain ⟨a', b'⟩ := T'
    obtain ⟨φ₁, φ₂⟩ := φ
    have e := Z1.comp f (T := (a, b)) (T' := (a', b)) (T'' := (a', b'))
      (φ₁, 𝟙 b) (𝟙 a', φ₂)
    have e' : (show ((a, b) : C × C) ⟶ (a', b) from (φ₁, 𝟙 b)) ≫
        (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', φ₂)) = (φ₁, φ₂) := by
      simp
    rw [e', hf a a' b φ₁, map_zero, zero_add, hy φ₂ a'] at e
    exact e.symm

end GlobalTheory.CompanionTheory.Axis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleTensorCoboundaryClassZero
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Axis.KFlat

section Pi

variable {R : Type} [CommRing R] {J : Type} [Finite J] {M : J → Type} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] {N : Type} [AddCommGroup N] [Module R N]

theorem piLeft_apply_eq [Fintype J] [DecidableEq J] (u : (∀ i, M i) ⊗[R] N) (i : J) :
    TensorProduct.piLeft R N M u i = (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

theorem pi_rTensor_eq_zero (w : (∀ i, M i) ⊗[R] N)
    (h : ∀ i, (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N w = 0) : w = 0 := by
  classical
  have := Fintype.ofFinite J
  apply (TensorProduct.piLeft R N M).injective
  funext i
  rw [piLeft_apply_eq, h, map_zero]
  rfl

theorem pi_rTensor_exists (g : ∀ i, M i ⊗[R] N) :
    ∃ u : (∀ i, M i) ⊗[R] N, ∀ i, (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N u = g i := by
  classical
  have := Fintype.ofFinite J
  refine ⟨(TensorProduct.piLeft R N M).symm g, fun i ↦ ?_⟩
  rw [← piLeft_apply_eq, LinearEquiv.apply_symm_apply]

end Pi

theorem class_eq_zero_of_coboundary (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (N : Type) [AddCommGroup N] [Module R N] [Module.Flat R N] (t : Z1 F ⊗[R] N)
    (g : ∀ T : C, F.obj T ⊗[R] N)
    (h : ∀ (T T' : C) (φ : T ⟶ T'), (evZ F φ).rTensor N t = g T' - (mp F φ).toLinearMap.rTensor N (g T)) :
    (H1.mk F).rTensor N t = 0 := by
  classical
  haveI : ∀ T T' : C, Finite (T ⟶ T') := fun T T' ↦ by
    haveI : Subsingleton (T ⟶ T') := inferInstance
    exact Finite.of_subsingleton
  let κ : Z1 F →ₗ[R] ∀ x : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj x.2.1 :=
    LinearMap.pi fun x ↦ evZ F x.2.2
  have hκ : Function.Injective κ := fun a b hab ↦ Subtype.ext (by
    funext T T' φ
    exact congrFun hab ⟨T, T', φ⟩)
  let δ : C0 F →ₗ[R] Z1 F := (d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)
  obtain ⟨u, hu⟩ := pi_rTensor_exists (R := R) (M := fun T : C ↦ F.obj T) (N := N) g
  have hδ : ∀ {T T' : C} (φ : T ⟶ T'), evZ F φ ∘ₗ δ =
      (LinearMap.proj T' : C0 F →ₗ[R] F.obj T') -
        (mp F φ).toLinearMap ∘ₗ (LinearMap.proj T : C0 F →ₗ[R] F.obj T) := fun φ ↦ by
    refine LinearMap.ext fun c ↦ ?_
    rfl
  have key : t = δ.rTensor N u := by
    apply Module.Flat.rTensor_preserves_injective_linearMap κ hκ
    rw [← sub_eq_zero, ← map_sub]
    apply pi_rTensor_eq_zero
    rintro ⟨T, T', φ⟩
    rw [← LinearMap.rTensor_comp_apply]
    have e : (LinearMap.proj (⟨T, T', φ⟩ : Σ T : C, Σ T' : C, (T ⟶ T')) :
        (∀ x : (Σ T : C, Σ T' : C, (T ⟶ T')), F.obj x.2.1) →ₗ[R] F.obj T') ∘ₗ κ = evZ F φ := rfl
    rw [e, map_sub, h, ← LinearMap.rTensor_comp_apply, hδ, LinearMap.rTensor_sub, LinearMap.sub_apply,
      LinearMap.rTensor_comp_apply, hu, hu, sub_self]
  have hz : H1.mk F ∘ₗ δ = 0 := by
    refine LinearMap.ext fun c ↦ ?_
    exact (H1.mk_eq_zero (F := F) (f := δ c)).2 ⟨c, rfl⟩
  rw [key, ← LinearMap.rTensor_comp_apply, hz, LinearMap.rTensor_zero, LinearMap.zero_apply]

end GlobalTheory.CompanionTheory.Axis.KFlat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinducedCechAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coinduced_cech_acyclic : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Surjective e → ∀ (M : P → ModuleCat.{0} R) (n : ℕ),
    IsZero (((cechOf e).obj (coind M)).homology (n + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology | exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.isZero_homology <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjectiveStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_forms_map_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ), Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdeal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeUnit

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem pt_of_hom {T T' : Thick (smFun X q)} (φ : T ⟶ T') :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T = pt T' := by
  have := φ.pt
  unfold pt
  rw [← this]
  rfl

theorem spec_comp {C : Type 1} [Category.{0} C] (g : C ⥤ Thick (smFun X q)) {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) := by
  have hφ : (g.map (a ≫ b)).φ = (g.map b).φ.comp (g.map a).φ := by rw [g.map_comp]; rfl
  rw [← Spec.map_comp]
  congr 1
  ext x
  show Ideal.Quotient.mk _ ((g.map (a ≫ b)).φ x) = Ideal.Quotient.mk _ ((g.map b).φ ((g.map a).φ x))
  rw [hφ]
  rfl

theorem u_points (D : E.LineData X) {V : Scheme.{0}} {a a' b : V ⟶ D.Y} (ha : a = a')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b ≫ D.f) : D.u a b h = D.u a' b h' := by
  subst ha
  rfl

theorem gamma_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom y) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom y) :=
  congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem r_sub_mem {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D)
    {c₀ c₁ c₂ : C} (a : c₀ ⟶ c₁) (b : c₁ ⟶ c₂) (c : c₀ ⟶ c₂) (hc : c = a ≫ b) :
    ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) * Λ.w b * (Λ.w c)⁻¹ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈
      (g.obj c₂).J := by
  subst hc
  have ea := pt_of_hom (g.map a)
  have eb := pt_of_hom (g.map b)
  have ec := pt_of_hom (g.map (a ≫ b))
  have h1 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₁ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ea]
  have h2 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, eb]
  have h3 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ (g.map (a ≫ b)).hle)) ≫ Λ.p c₀) ≫ D.f =
      Λ.p c₂ ≫ D.f := by rw [Category.assoc, Λ.hp, Λ.hp, ec]
  have wa := Λ.hw a h1
  have wb := Λ.hw b h2
  have wc := Λ.hw (a ≫ b) h3
  have nat := D.nat (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle))) _ _ h1
  have h12 : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₁).J (g.map a).φ (g.map a).hle)) ≫ Λ.p c₀) ≫ D.f =
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ Λ.p c₁) ≫ D.f := by
    simpa only [Category.assoc] using
      congrArg (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle)) ≫ ·) h1
  have coc := D.coc _ _ _ h12 h2
  have uc := u_points D (show Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c₂).J (g.map (a ≫ b)).φ
      (g.map (a ≫ b)).hle)) ≫ Λ.p c₀ = _ by rw [spec_comp, Category.assoc]) h3 (h12.trans h2)
  have A : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) =
      (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c₂).B ⧸ (g.obj c₂).J))).hom.hom
        (D.u _ _ h12).1 := by
    show Ideal.quotientMap (g.obj c₂).J (g.map b).φ (g.map b).hle (Ideal.Quotient.mk (g.obj c₁).J (Λ.w a)) = _
    rw [wa, nat, ← gamma_nat]
    rfl
  have B : Ideal.Quotient.mk (g.obj c₂).J ((Units.map (g.map b).φ.toMonoidHom (Λ.w a) : (g.obj c₂).Bˣ) : (g.obj c₂).B) *
      Ideal.Quotient.mk (g.obj c₂).J (Λ.w b) = Ideal.Quotient.mk (g.obj c₂).J (Λ.w (a ≫ b)) := by
    rw [A, wb, wc, ← map_mul, ← Units.val_mul, coc, uc]
  rw [← Ideal.Quotient.eq, map_one, Units.val_mul, Units.val_mul, map_mul, map_mul, B, ← map_mul, Units.mul_inv, map_one]

theorem r_sub_one : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (σ : ComposableArrows C 2), ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1) ∈ (g.obj (σ.obj (Fin.last 2))).J := by
  intro K _ _ X q C _ g D Λ σ
  exact r_sub_mem Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (by
    rw [← Functor.map_comp]
    rfl)

end GlobalTheory.CompanionTheory.ConeUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLoweringDerivationFormulaStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_lowering_derivation_formula : ∀ {R : Type} [CommRing R] (H : ℕ → Type) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] (g : ℕ) (_ : Module.Basis (Fin g) R (H 1)) (one : H 0) (L : ∀ n, H 1 →ₗ[R] H n →ₗ[R] H (n + 1)) (D : ∀ n, Module.Dual R (H 1) → H (n + 1) →ₗ[R] H n) (τ : ∀ n, H n →ₗ[R] H n), (∀ r : R, r • one = 0 → r = 0) → (∀ x, L 0 x one = x) → (∀ l x, D 0 l x = l x • one) → (∀ n l x z, D (n + 1) l (L (n + 1) x z) = l x • τ (n + 1) z - L n x (D n l z)) → (∀ n x z, τ (n + 2) (L (n + 1) x z) = L (n + 1) x (τ (n + 1) z)) → (∀ x, τ 1 x = x) → (∀ y, τ 2 y = y) → Subsingleton (H (g + 2)) → ∃ e : ⋀[R]^2 (H 1) ≃ₗ[R] H 2, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = L 1 a b := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.Wedge.exteriorSquare_equiv | exact GlobalTheory.CompanionTheory.HopfC.Wedge.exteriorSquare_equiv | (intros; apply GlobalTheory.CompanionTheory.HopfC.Wedge.exteriorSquare_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossProductKernelQuotientVanishingStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cross_product_kernel_quotient_vanishing : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R) (t : H1 F ⊗[R] H1 F), TensorProduct.lift (crossB F) t = 0 → TensorProduct.map (iotaQ F) (iotaQ F) t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.Shuffle.map_iotaQ_eq_zero | exact GlobalTheory.CompanionTheory.WedgeOf.Shuffle.map_iotaQ_eq_zero | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.Shuffle.map_iotaQ_eq_zero <;> assumption)
end

