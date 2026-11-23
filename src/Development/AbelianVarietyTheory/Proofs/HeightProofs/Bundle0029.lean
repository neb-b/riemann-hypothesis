module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFrames
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicMatrixLattice

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem exists_coords : ∃ (n : ℕ) (e : R ⊗[F] E ≃ₜ (Fin n → R)) (b : E ≃ₗ[F] (Fin n → F)),
    (∀ x y, e (x + y) = e x + e y) ∧ ∀ x i, e (inclR R x) i = algebraMap F R (b x i) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  refine ⟨Module.finrank F E, { e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap },
    (Module.finBasis F E).equivFun, fun x y => e.map_add x y, fun x i => ?_⟩
  change (Algebra.TensorProduct.basis R (Module.finBasis F E)).repr ((1 : R) ⊗ₜ[F] x) i = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem discrete_tensor (h : ∃ U ∈ nhds (0 : R), ∀ x : F, algebraMap F R x ∈ U → x = 0) :
    ∃ U ∈ nhds (0 : R ⊗[F] E), ∀ x : E, inclR R x ∈ U → x = 0 := by
  obtain ⟨U, hU, hx⟩ := h
  obtain ⟨n, e, b, hadd, hb⟩ := exists_coords (F := F) (E := E) R
  have h0 : e 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => U), ?_, fun x hxU => ?_⟩
  · refine e.continuous.continuousAt.preimage_mem_nhds ?_
    rw [h0]
    exact set_pi_mem_nhds Set.finite_univ fun _ _ => hU
  · refine b.injective ?_
    rw [map_zero]
    funext i
    refine hx _ ?_
    rw [← hb]
    exact hxU i (Set.mem_univ i)

theorem cocompact_tensor
    (h : ∃ K : Set R, IsCompact K ∧ ∀ a : R, ∃ x : F, a - algebraMap F R x ∈ K) :
    ∃ K : Set (R ⊗[F] E), IsCompact K ∧ ∀ a : R ⊗[F] E, ∃ x : E, inclR R x + a ∈ K := by
  obtain ⟨K, hK, hx⟩ := h
  obtain ⟨n, e, b, hadd, hb⟩ := exists_coords (F := F) (E := E) R
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => K), e.isCompact_preimage.2 (isCompact_univ_pi fun _ => hK),
    fun a => ?_⟩
  choose c hc using hx
  refine ⟨b.symm fun i => - c (e a i), fun i _ => ?_⟩
  rw [hadd, Pi.add_apply, hb, b.apply_symm_apply, map_neg, neg_add_eq_sub]
  exact hc _

end Tensor

theorem lattice : ∀ (D : D7) (V W : HSp D), IsTopologicalAddGroup (WA V W) ∧ LocallyCompactSpace (WA V W) ∧ SecondCountableTopology (WA V W) ∧ T2Space (WA V W) ∧ DiscreteTopology (ratL V W) ∧ ∃ K : Set (WA V W), IsCompact K ∧ ∀ x : WA V W, ∃ γ ∈ ratL V W, γ + x ∈ K := by
  intro D V W
  have : LocallyCompactSpace (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele _
  have : SecondCountableTopology (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E)
    (AF D.host.F)
  have : LocallyCompactSpace (AE D) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AE D) := e.secondCountableTopology
  have : T2Space (AE D) := e.isEmbedding.t2Space
  have hg : IsTopologicalAddGroup (WA V W) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin V.rank → Fin W.rank → AE D))
  refine ⟨hg, inferInstanceAs (LocallyCompactSpace (Fin V.rank → Fin W.rank → AE D)),
    inferInstanceAs (SecondCountableTopology (Fin V.rank → Fin W.rank → AE D)),
    inferInstanceAs (T2Space (Fin V.rank → Fin W.rank → AE D)), ?_, ?_⟩
  · obtain ⟨U, hU, hx⟩ := discrete_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero D.host.F)
    have hN : (Set.univ.pi fun _ : Fin V.rank => Set.univ.pi fun _ : Fin W.rank => U) ∈
        nhds (0 : WA V W) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratL V W => (x : WA V W)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, hx⟩ := cocompact_tensor (F := D.host.F) (E := D.host.E) (AF D.host.F)
      (GlobalTheory.AdeleCocompact.exists_compact_adele D.host.F)
    choose c hc using hx
    refine ⟨Set.univ.pi fun _ : Fin V.rank => Set.univ.pi fun _ : Fin W.rank => K,
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

end GlobalTheory.AdelicMatrixLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def BddDen (V : HSp D) (d : ℕ) (g : GA D V) : Prop :=
  ∀ i j, d • finMat D.sp.cm.sig V.gram g i j ∈ intAE D ∧ d • finMat D.sp.cm.sig V.gram g⁻¹ i j ∈ intAE D

def DenomBound (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∃ (C : ℝ) (M : ℕ), ∀ g : GA D V, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ M ∧
    ∀ i : Fin V.rank, (Pi.single i (d : D.host.E) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.latG V g

def RealPoints (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  (∀ τ, (gramAt D V τ)ᴴ = gramAt D V τ ∧ IsUnit (gramAt D V τ).det) ∧
  (∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ) ∧
  (∀ g ∈ GinfC V, ∀ g' ∈ GinfC V,
    (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = infMat D.sp.cm.sig V.gram (θ τ) g') → g = g') ∧
  (∀ g g' τ, infMat D.sp.cm.sig V.gram (θ τ) (g * g') =
    infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g') ∧
  (∀ k ∈ GfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = 1) ∧
  (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧
  (∀ g : GA D V, ∃ k ∈ GfC V, ∃ a ∈ GinfC V, g = k * a) ∧
  ∀ (g : GA D V), ∀ a ∈ GinfC V, finMat D.sp.cm.sig V.gram (g * a) = finMat D.sp.cm.sig V.gram g

end GlobalTheory.SmoothForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTanAtOfGenericFibre
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntFramesCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames GlobalTheory.Reg

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Linear

variable {S : Type} [Field S] {x : Sp S ⟶ Xo.X} {m : ℕ} {u v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}

end Linear

section Basis

variable {S : Type} [Field S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} {τ : E →+* ℂ}
  {u v : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}

theorem exists_eigenBasisAt (hx0 : x ≫ Xo.s = sOf c S) (τ : E →+* ℂ) : ∃ u, IsEigenBasisAt Xo c x τ u := by
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  let B : Module.Basis (Fin (Dw.mult τ)) S (gfpEig (c := c) hx τ) :=
    Module.finBasisOfFinrankEq S _ (gfp_finrank hx0 hx τ)
  have hd : LinearIndependent S ((gfpEig (c := c) hx τ).subtype ∘ B) :=
    B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _)
  have hW : ∀ i, ((gfpEig (c := c) hx τ).subtype ∘ B) i ∈ gfpEig (c := c) hx τ := fun i => (B i).2
  exact ⟨fun i => gfpVec x xc (((gfpEig (c := c) hx τ).subtype ∘ B) i), fun i => gfp_tan hx _,
    fun i => (gfp_eig_iff hx τ _).2 (hW i), fun w hw he => gfp_basis hx0 hx τ _ hd hW w hw he⟩

end Basis

section Generic

end Generic

variable (Xo c)

end GlobalTheory.IntFramesCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTangentOfIsLieImage
section
noncomputable section

namespace GlobalTheory.ArcLieCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

section General

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem prod_Oφ_zero {T : Over (Sp R)} (b : T ⟶ D.P.A) {Z : Scheme.{0}} (π : Z ⟶ T.left) (σ : Z ⟶ Sp R)
    (hb : π ≫ b.left = σ ≫ eSec D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (Z ⟶ D.P.A.left) → U) :
    ∏ k, h (π ≫ D.Oφ b χ k) ^ Oinvε k = 1 := by
  have hσ : σ = π ≫ T.hom := by
    have e : eSec D.P.A ≫ D.P.A.hom = 𝟙 (Sp R) := Over.w η[D.P.A]
    rw [← Over.w b, ← Category.assoc, hb, Category.assoc]
    exact ((congrArg (σ ≫ ·) e).trans (Category.comp_id _)).symm
  let FinalForm : Over (Sp R) := Over.mk (π ≫ T.hom)
  let π' : FinalForm ⟶ T := Over.homMk π rfl
  have h1 : π' ≫ b = 1 := Over.OverMorphism.ext (hb.trans (by
    rw [hσ]
    show _ = (toUnit FinalForm ≫ η[D.P.A]).left
    simp [eSec, FinalForm]))
  have e : ∀ k, π ≫ D.Oφ b χ k = D.Oφ (1 : FinalForm ⟶ D.P.A) χ k := fun k =>
    (WeightPf.Oφ_comp π' b χ k).trans (by rw [h1])
  simp only [e]
  rw [Fin.prod_univ_four]
  show h ((1 : FinalForm ⟶ D.P.A) * (toUnit FinalForm ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit FinalForm ≫ D.c χ).left ^ (1 : ℤ) *
    h (1 : FinalForm ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : FinalForm ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  simp

theorem exists_isZero (T : Over (Sp R)) : ∃ g : GtPt D T, g.IsZero := by
  have hF : ∀ χ, FormEq (PEmpty.elim : PEmpty → (T.left ⟶ D.P.A.left)) PEmpty.elim
      (DegPre.gtφT D T 1 χ) DegPre.gtε := fun χ U _ h => by
    have := prod_Oφ_zero (D := D) (1 : T ⟶ D.P.A) (𝟙 _) T.hom (by
      show 𝟙 _ ≫ (toUnit T ≫ η[D.P.A]).left = _
      simp [eSec]) χ h
    simp only [Category.id_comp] at this
    rw [TorusCoord.gtφT_eq]
    exact (Fintype.prod_empty _).trans this.symm
  choose s h using fun χ => exists_gen D.P.isLB (hF χ) (LB.oneGen D.P.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  have hs := fun χ => (h χ).1
  have vs := fun χ => (h χ).2
  have v1 : ∀ χ y J, Good D.P.L y J → val (s χ) (𝟙 _) y J = 1 := fun χ y J hJ =>
    (vs χ _ _ y J hJ).trans (val_one _)
  refine ⟨⟨1, s, hs, corr_of_val D.P.isLB fun y J hJ => vs 0 _ _ y J hJ,
    fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl,
    fun χ => corr_of_val D.P.isLB fun y J hJ => vs χ _ _ y J hJ⟩
  have c := val_cub D.cub (𝟙 T) hJ (DegPre.cT D T χ) (DegPre.cT D T χ') 1
  simp only [Category.id_comp] at c
  have face (x x' : T ⟶ D.P.A) : cubV D.cub y J 1 x x' = 1 := by
    have e := val_corr hJ (D.cub.face 0) (lift x x').left
    rw [val_one] at e
    refine (Eq.trans ?_ (val_cub D.cub (lift x x') hJ (pzero D.P.A _) (x2 D.P.A 0) (x2 D.P.A 1)).symm).trans e
    congr 1 <;> simp [x2, pzero, Hom.one_def]
  have swap01 (x x' w : T ⟶ D.P.A) : cubV D.cub y J x x' w = cubV D.cub y J x' x w := by
    have e := (val_corr hJ D.cub.cubeSymmetric_swap_first (lift x (lift x' w)).left).trans (val_cub D.cub (lift x (lift x' w)) hJ _ _ _)
    refine Eq.trans e ?_
    congr 1 <;> simp [x3]
  have swap12 (x x' w : T ⟶ D.P.A) : cubV D.cub y J x x' w = cubV D.cub y J x w x' := by
    have e := (val_corr hJ D.cub.cubeSymmetric_swap_last (lift x (lift x' w)).left).trans (val_cub D.cub (lift x (lift x' w)) hJ _ _ _)
    refine Eq.trans e ?_
    congr 1 <;> simp [x3]
  have c' := c.trans ((swap12 _ _ _).trans ((swap01 _ _ _).trans (face _ _)))
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v1 _ y J hJ) c')).trans
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v1 _ y J hJ) (v1 _ y J hJ))).symm


variable {I : Ideal R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)


omit [IsDomain R] in
theorem epsRed_hom : epsRed R ≫ (epsR R).hom = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
    RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
  rw [h3]
  exact Spec.map_id _

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section ThetaShiftProofs

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁}
  {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

end ThetaShiftProofs


end GlobalTheory.ArcLieCompare
end
end

