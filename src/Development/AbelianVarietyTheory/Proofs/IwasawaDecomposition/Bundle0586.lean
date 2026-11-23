module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointThree

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcLieBasisExponentialCoordsHasSumStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_lieBasis_exponentialCoords_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U) (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ) (hn : M.n = g) (v' : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) → IsLieBasis v → (Matrix.of z).det ≠ 0 → (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ (Fin.cast hn.symm i)) → (∀ i, IsLieComb (A i) v (v' i)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → ∀ i, (∀ k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)) ∧ ∀ j, Wv (Fin.cast hg.symm i) j = ∑ k, (∑' m : ℕ, PowerSeries.coeff m (A i k) * eTwoPi w ^ m) * z k j := by
  first | exact @GlobalTheory.ArcLieCoord.lie_coords_hasSum | exact GlobalTheory.ArcLieCoord.lie_coords_hasSum | (intros; apply GlobalTheory.ArcLieCoord.lie_coords_hasSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiFromTau

theorem exists_isTauCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X),
    ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x := by
  intro R _ _ _ D a b
  have pick : ∀ (z : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A), ∃ i, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsIntChart D z i := by
    intro z
    have hc : z.left (closedPoint R) ∈ ⨆ i, D.P.L.U i := by
      rw [D.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨i, ((closedPoint_mem_iff (R := R) (z.left ⁻¹ᵁ D.P.L.U i)).1 hi).ge⟩
  obtain ⟨i1, h1⟩ := pick (D.c (a + b))
  obtain ⟨i2, h2⟩ := pick (D.c a)
  obtain ⟨i3, h3⟩ := pick (D.c b)
  obtain ⟨i4, h4⟩ := pick η[D.P.A]
  let j : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → D.P.L.ι := Sum.elim (Sum.elim (Sum.elim (fun _ => i1) (fun _ => i2)) (fun _ => i3)) (fun _ => i4)
  refine ⟨_, j, ?_, h1, h2, h3, h4, rfl⟩
  intro y _
  refine Set.mem_iInter.2 ?_
  rintro (((⟨⟩ | ⟨⟩) | ⟨⟩) | ⟨⟩)
  · exact h1 (Set.mem_univ (jK R y))
  · exact h2 (Set.mem_univ (jK R y))
  · exact h3 (Set.mem_univ (jK R y))
  · exact h4 (Set.mem_univ ((toUnit (TK R)).left y))

theorem associated_of_tau : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (g : R →+* W) (hg : Function.Injective g)
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
    (∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W)) →
    ∀ (y : P.D.toPre.X) (r : R) (r' : W), PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (ρ y) r' → Associated (g r) r' := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ g hg t' P' ρ hρ y r r' hr hr'
  letI := H.starRing
  obtain ⟨x, hx⟩ := exists_isTauCoord R P.D.toPre y (H.w0 • y)
  obtain ⟨x', hx'⟩ := exists_isTauCoord W P'.D.toPre (ρ y) (H.w0 • ρ y)
  have hx'' : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ y) (ρ (H.w0 • y)) x' := by rwa [ρ.map_smul]
  obtain ⟨u, hu⟩ := hρ y (H.w0 • y) x x' hx hx''
  obtain ⟨u1, hu1⟩ := _root_.GlobalTheory.PsiTauCoordRel.main R P.D.toPre (𝓞 E) P.oD H.w0 P.w0 y r x hr hx
  obtain ⟨u2, hu2⟩ := _root_.GlobalTheory.PsiTauCoordRel.main W P'.D.toPre (𝓞 E) P'.oD H.w0 P'.w0 (ρ y) r' x' hr' hx'
  set φ := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) with hφ
  have hφa : ∀ s : R, φ (algebraMap R (FractionRing R) s) = algebraMap W (FractionRing W) (g s) := fun s =>
    IsFractionRing.lift_algebraMap _ s
  have e1 := congrArg φ hu1
  rw [map_mul, hφa, hφa, hu] at e1
  let v : Wˣ := Units.map g.toMonoidHom u1 * u * u2⁻¹
  have key : g r = r' * (v : W) := by
    apply IsFractionRing.injective W (FractionRing W)
    have h2 : (x' : FractionRing W) = algebraMap W (FractionRing W) ((u2⁻¹ : Wˣ) : W) * algebraMap W (FractionRing W) r' := by
      rw [hu2, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    rw [e1, h2]
    simp only [v, Units.val_mul, map_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  exact Associated.symm ⟨v, key.symm⟩

end GlobalTheory.PsiFromTau
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedPsdRationalRadicalConeSubsetIntCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem psdCone_subset_psdCone_int (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] : psdCone (bar := bar) (X := X) ⊆ psdCone (bar := (id : ℤ → ℤ)) (X := X) := by
  rintro B ⟨X₁, _, _, hP, r, B₁, hr, h1, h2, h3⟩
  haveI : Module.Projective ℤ X₁ := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hP
    exact Module.Projective.of_split (s.restrictScalars ℤ) ((Finsupp.linearCombination O id).restrictScalars ℤ)
      (by ext x; exact congrArg (· x) hs)
  refine ⟨X₁, inferInstance, inferInstance, inferInstance, r.toAddMonoidHom.toIntLinearMap, B₁, hr,
    ⟨h1.1, fun a y z => ?_⟩, h2, h3⟩
  show B₁ (a • y) z = B₁ y (a • z)
  rw [map_zsmul, map_zsmul, LinearMap.smul_apply]

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFrames
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions
  Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.GoodMetric GlobalTheory.LieBase

namespace GlobalTheory.ShFam.CarriesAt

theorem diag_mul_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem isUnit_diag_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hd : IsUnit A.det) (i : Fin n) : IsUnit (A i i) := by
  rw [Matrix.det_of_upperTriangular hA] at hd
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => A j j) (Finset.mem_univ i)) hd

theorem tri_of_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C k _ φ x g p hC y ψ φ₁ f t hp hf
  obtain ⟨y₁, ψ₁, φ₂, f₁, t₁, t₁', hp₁, hf₁, hg₁⟩ := hC

  have hsp : p (IsLocalRing.closedPoint k) ⤳ y := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
      rw [hp]
      exact ⟨spMap ψ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hsp₁ : p (IsLocalRing.closedPoint k) ⤳ y₁ := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y₁) := by
      rw [hp₁]
      exact ⟨spMap ψ₁ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp.symm
  have hψ₁ : ψ₁ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y₁)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom ≫ C.Y.X.fromSpecStalk y₁ = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp₁.symm
  set ψp := (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom with hψpdef
  set ρ := (C.Y.X.presheaf.stalkSpecializes hsp).hom with hρdef
  set ρ₁ := (C.Y.X.presheaf.stalkSpecializes hsp₁).hom with hρ₁def
  set alg := algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint k))) C.Y.X.functionField with halgdef
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have halg : algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField = alg.comp ρ := algebraMap_eq_comp_specializes hsp
  have halg₁ : algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField = alg.comp ρ₁ :=
    algebraMap_eq_comp_specializes hsp₁
  have hxp : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hxp₁ : spMap ρ₁ ≫ stalkPt C.Y y₁ = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
  have hpp : spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) = p := spMap_stalkClosedPointTo p

  have c1 : alg.comp (ρ.comp φ₁) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg, hf.2.1]
  have c2 : alg.comp (ρ₁.comp φ₂) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg₁, hf₁.2.1]
  have hρφ : ρ₁.comp φ₂ = ρ.comp φ₁ := RingHom.ext fun a => hinj
    ((RingHom.congr_fun c2 a).trans (RingHom.congr_fun c1 a).symm)
  have hgen : genericPt C.Y ≫ C.π ≫ genι Z = spMap alg ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hf.1, halg, ← hxp]
    simp [spMap, Spec.map_comp]
  have hx0 : x = p ≫ C.π ≫ genι Z := by rw [hg₁.1, hp₁, Category.assoc]
  have hxk : x = spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hx0, ← Category.assoc (spMap ψp), hpp]
  have hxψ : x = spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z := by
    rw [hx0, hp, Category.assoc]
  have hφk : φ = ψ.comp φ₁ := by
    rw [hg₁.2.1, hψ₁, hψ, RingHom.comp_assoc, RingHom.comp_assoc, hρφ]

  obtain ⟨f', hf'⟩ := f.exists_isMap ρ (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) rfl
    (by rw [← hxp, Category.assoc])
  obtain ⟨f₁', hf₁'⟩ := f₁.exists_isMap ρ₁ (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) hρφ.symm
    (by rw [← hxp₁, Category.assoc])
  obtain ⟨fF, hfF⟩ := f'.exists_isMap alg c1.symm hgen
  obtain ⟨f₁F, hf₁F⟩ := f₁'.exists_isMap alg c1.symm hgen
  obtain ⟨fk, hfk⟩ := f.exists_isMap ψ hφk hxψ
  obtain ⟨f₁k, hf₁k⟩ := f₁.exists_isMap ψ₁ hg₁.2.1 hg₁.1
  have iF : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) fF := fun τ i => by
    rw [hfF τ i, hf' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap alg)), ← spMap_dualMap_comp, ← halg]
  have i₁F : f₁.IsMap (algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField) f₁F := fun τ i => by
    rw [hf₁F τ i, hf₁' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap alg)), ← spMap_dualMap_comp, ← halg₁]
  have ik : f'.IsMap ψp fk := fun τ i => by
    rw [hfk τ i, hf' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap ψp)), ← spMap_dualMap_comp, ← hψ]
  have i₁k : f₁'.IsMap ψp f₁k := fun τ i => by
    rw [hf₁k τ i, hf₁' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap ψp)), ← spMap_dualMap_comp, ← hψ₁]

  have key : ∀ τ, (fk.co g τ).BlockTriangular id ∧ ∀ i, IsUnit (fk.co g τ i i) := by
    intro τ
    have hU := EigFrame.Tri.co (τ := τ) hf iF
    have hU₁ := EigFrame.Tri.co (τ := τ) hf₁ i₁F
    have hU₁t : (f₁F.co C.f0 τ).BlockTriangular id := fun a i h => hU₁.1 a i h
    have hU₁d : IsUnit (f₁F.co C.f0 τ).det := f₁F.isUnit_det_co C.f0 τ
    have hW : fF.co f₁F τ = fF.co C.f0 τ * (f₁F.co C.f0 τ)⁻¹ := by
      rw [← fF.co_mul f₁F C.f0 τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU₁d, Matrix.mul_one]
    have hWt : (fF.co f₁F τ).BlockTriangular id := by
      haveI := Matrix.invertibleOfIsUnitDet _ hU₁d
      rw [hW]
      exact Matrix.BlockTriangular.mul (fun a i h => hU.1 a i h) (Matrix.blockTriangular_inv_of_blockTriangular hU₁t)
    have hM : fF.co f₁F τ = (f'.co f₁' τ).map alg := EigFrame.IsMap.co τ hfF hf₁F hgen
    have hMt : (f'.co f₁' τ).BlockTriangular id := fun a i h => hinj (by
      have := hWt h
      rw [hM, Matrix.map_apply] at this
      rw [this, map_zero])
    have hMu : ∀ i, IsUnit (f'.co f₁' τ i i) := isUnit_diag_of_blockTriangular hMt (f'.isUnit_det_co f₁' τ)
    have hN := EigFrame.Tri.co (τ := τ) hg₁ hf₁k
    have hNt : (f₁k.co g τ).BlockTriangular id := fun a i h => hN.1 a i h
    have hMk : fk.co f₁k τ = (f'.co f₁' τ).map ψp := EigFrame.IsMap.co τ ik i₁k hxk
    have hMkt : (fk.co f₁k τ).BlockTriangular id := fun a i h => by
      rw [hMk, Matrix.map_apply, hMt h, map_zero]
    have hQ : fk.co g τ = fk.co f₁k τ * f₁k.co g τ := (fk.co_mul f₁k g τ).symm
    refine ⟨hQ ▸ hMkt.mul hNt, fun i => ?_⟩
    rw [hQ, diag_mul_of_blockTriangular hMkt hNt, hMk, Matrix.map_apply, hN.2 i]
    exact ((hMu i).map ψp).mul (Units.isUnit _)
  refine ⟨fun τ i => ((key τ).2 i).unit, hxψ, hφk, fun τ i => ⟨fun a => fk.co g τ a i, ((key τ).2 i).unit_spec.symm,
    fun a ha => (key τ).1 ha, ?_⟩⟩
  rw [← funext (hfk τ)]
  exact fk.co_spec g τ i

end GlobalTheory.ShFam.CarriesAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorOnRayOfLinIndepSubcell
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace CellRay

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m' : ℕ}

theorem inCell {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCell bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he

end CellRay

end GlobalTheory.PolFan


open GlobalTheory.PolFan.CellRay in
theorem GlobalTheory.PolFan.cell_gen_on_ray : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m n : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X)
    (c : Fin n → ℝ), IsCell bar φ δ → IsCell bar φ γ → LinearIndependent ℤ δ → (∀ j, 0 ≤ c j) →
    ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) → ∀ i, ∃ (j : Fin n) (a b : ℕ), 0 < a ∧ 0 < b ∧ a • δ i = b • γ j := by
  intro O _ bar φ X _ _ _ m n δ γ c hδ hγ hli hc hrel i
  classical

  obtain ⟨k, d, hk, hkd⟩ := inCell hγ hδ.mem hδ.nonneg (a := fun _ => (1 : ℝ)) (b := c) (fun _ => zero_le_one) hc
    ((linearOn_iff φ δ).1 hδ.linear (fun _ => 1) fun _ => zero_le_one) (by simpa using hrel) i one_ne_zero

  have hB : ∀ j, ∃ (kj : ℕ) (e : Fin m → ℕ), 0 < kj ∧ (d j ≠ 0 → kj • γ j = ∑ l, e l • δ l) := by
    intro j
    by_cases hd : d j = 0
    · exact ⟨1, 0, one_pos, fun h => absurd hd h⟩
    obtain ⟨kj, e, hkj, he⟩ := inCell (a := fun j => (d j : ℝ)) (b := Pi.single i (k : ℝ)) hδ hγ.mem hγ.nonneg
      (fun j => Nat.cast_nonneg _) (fun l => by by_cases h : l = i <;> simp [h])
      ((linearOn_iff φ γ).1 hγ.linear _ fun j => Nat.cast_nonneg _) (by
        refine LinearMap.ext₂ fun a b => ?_
        have := LinearMap.congr_fun₂ hkd a b
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, nsmul_eq_mul] at this ⊢
        simp only [Pi.single_apply, ite_smul, zero_smul, LinearMap.smul_apply, toReal_apply, smul_eq_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
        exact_mod_cast this.symm) j (by exact_mod_cast hd)
    exact ⟨kj, e, hkj, fun _ => he⟩
  choose kk e hkk he using hB
  set K := ∏ j, kk j with hKdef
  let Kj : Fin n → ℕ := fun j => ∏ j' ∈ Finset.univ.erase j, kk j'
  have hK : ∀ j, kk j * Kj j = K := fun j => Finset.mul_prod_erase Finset.univ kk (Finset.mem_univ j)
  have hKpos : 0 < K := Finset.prod_pos fun j _ => hkk j
  have hKj : ∀ j, Kj j ≠ 0 := fun j h => by
    have := hK j
    rw [h, mul_zero] at this
    omega
  have hterm : ∀ j, (K * d j) • γ j = ∑ l, (d j * Kj j * e j l) • δ l := by
    intro j
    by_cases hd : d j = 0
    · simp [hd]
    rw [← hK j, show kk j * Kj j * d j = (d j * Kj j) * kk j by ring, ← smul_smul, he j hd, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
  have key : (K * k) • δ i = ∑ l, (∑ j, d j * Kj j * e j l) • δ l := by
    rw [← smul_smul, hkd, Finset.smul_sum]
    simp only [smul_smul, hterm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => (Finset.sum_smul).symm
  have hFG := Fintype.linearIndependent_iffₛ.1 hli (fun l => ((∑ j, d j * Kj j * e j l : ℕ) : ℤ))
    (fun l => if l = i then ((K * k : ℕ) : ℤ) else 0) (by
      simp only [Nat.cast_smul_eq_nsmul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact key.symm)
  have hoff : ∀ l, l ≠ i → ∀ j, d j * Kj j * e j l = 0 := by
    intro l hl j
    have := hFG l
    simp only [if_neg hl, Nat.cast_eq_zero] at this
    exact (Finset.sum_eq_zero_iff.1 this) j (Finset.mem_univ _)
  have hon : ∑ j, d j * Kj j * e j i ≠ 0 := by
    have := hFG i
    rw [if_pos rfl, Nat.cast_inj] at this
    rw [this]
    exact (Nat.mul_pos hKpos hk).ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hon
  have hdj : d j ≠ 0 := fun h => hj (by rw [h]; ring)
  have hej : e j i ≠ 0 := fun h => hj (by rw [h]; ring)
  have hel : ∀ l, l ≠ i → e j l = 0 := fun l hl => by
    have := hoff l hl j
    rcases Nat.mul_eq_zero.1 this with h | h
    · rcases Nat.mul_eq_zero.1 h with h' | h'
      · exact absurd h' hdj
      · exact absurd h' (hKj j)
    · exact h
  have hγj : kk j • γ j = e j i • δ i := by
    rw [he j hdj, Finset.sum_eq_single i (fun l _ hl => by rw [hel l hl, zero_smul]) (by simp)]
  exact ⟨j, e j i, kk j, Nat.pos_of_ne_zero hej, hkk j, hγj.symm⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureInverseRealSymmetricGram
section
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.RealGram

open GlobalTheory.HermFrame Filter

theorem curv_inv_of_real : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, GlobalTheory.HermFrame.mddbar H z ξ η = 0) → ∀ ξ η, GlobalTheory.HermFrame.curv (fun x => (H x)⁻¹) z ξ η = -((GlobalTheory.HermFrame.conn H z η)ᵀᴴ * GlobalTheory.HermFrame.conn H z ξ)ᵀ := by
  intro E _ _ _ _ g H z h2 hu hs hh hdd ξ η
  have hsz : (H z)ᵀ = H z := hs.self_of_nhds.eq
  have hhz : (H z)ᴴ = H z := hh.self_of_nhds.eq
  have he : (fun x => (H x)⁻¹) =ᶠ[𝓝 z] fun x => dualGram (H x) :=
    hs.mono fun x hx => by
      show (H x)⁻¹ = (H x)⁻¹ᵀ
      rw [transpose_nonsing_inv, hx.eq]
  have hbar : (mdbar H z η)ᵀ = mdbar H z η := by
    rw [← mdbar_transpose]; exact mdbar_congr (hs.mono fun x hx => hx.eq) η
  have hdel : (mdel H z η)ᴴ = mdbar H z η := conjTranspose_mdel hh η
  have key : (conn H z η)ᵀᴴ = (H z)ᵀ⁻¹ * (mdbar H z η)ᵀ := by
    rw [conn, transpose_mul, transpose_transpose, conjTranspose_mul, hdel, transpose_nonsing_inv,
      transpose_transpose, hsz, hbar, conjTranspose_nonsing_inv, hhz]
  rw [curv_congr he, curv_dual h2 hu, curv_eq h2 hu, hdd, transpose_zero, Matrix.mul_zero,
    sub_zero, key, conn, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.RealGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormIntegrableComplexPointsOfChernWeil
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodMetric

theorem hasChernIntegral_top_of_chernWeil : GlobalTheory.Published.ChernWeilNumbers → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E ⊤ H → ∀ R : MvPolynomial (ι × ℕ) ℝ, ∃ t : ℝ, HasChernIntegral E ⊤ H R t := by
  intro h F _ σ X ι _ m E H hH R
  obtain ⟨Y, E', φ, f, gr, -, hR, hg⟩ := Model.exists_flagSpace X E
  exact ⟨_, h F σ X Y ι m E E' φ f gr hR hg H hH R⟩

end GlobalTheory.GoodMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory

theorem dickson_finite_below_every {ι : Type} (n : ℕ) (f : ι → Fin n → ℕ) :
    ∃ F : Finset ι, ∀ i, ∃ j ∈ F, f j ≤ f i := by
  classical
  set s : Set (Fin n → ℕ) := Set.range f
  have hpwo : s.IsPWO := Set.isPWO_of_wellQuasiOrderedLE s
  set m : Set (Fin n → ℕ) := {x | Minimal (· ∈ s) x}
  have hm : m.Finite := (setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn
    (hpwo.mono (fun x hx => hx.prop))
  have hpre : ∀ x ∈ m, ∃ j, f j = x := fun x hx => hx.prop
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, fun i => isEmptyElim i⟩
  choose! g hg using hpre
  refine ⟨hm.toFinset.image g, fun i => ?_⟩
  obtain ⟨x, hxi, hx⟩ := hpwo.exists_le_minimal (Set.mem_range_self i)
  exact ⟨g x, Finset.mem_image_of_mem g (hm.mem_toFinset.mpr hx), by rw [hg x hx]; exact hxi⟩

end GlobalTheory
end

