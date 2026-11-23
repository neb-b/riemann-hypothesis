module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2677
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTranslateLiftTorusImageEqAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Transl

theorem pG_comp_lift_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (a : 𝟙_ (Over (Sp R)) ⟶ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R I e ≫ g.b.left) → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
  intro R _ _ I D D₂ A A₂ G _ _ U U₂ g a β hβm e hβ hab h h₁ h₂
  let ae : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift (thick R I e ≫ a.left) (𝟙 _) (by
      rw [Category.assoc, Over.w a]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _)
  have hae : ae.left ≫ (fstG I e G).left = thick R I e ≫ a.left := pullback.lift_fst _ _ _
  have hh : h = (tr ae).left := by
    apply pullback.hom_ext
    · exact h₂.trans (tr_fst hae).symm
    · exact h₁.trans (Over.w (tr ae)).symm
  subst hh
  have k₁ := TorusCoord.im_mul (U.gt e) (toUnit _ ≫ ae) (𝟙 (thickObj R I e G))
  have k₂ : TorusCoord.im (U.gt e) (toUnit (thickObj R I e G) ≫ ae) = toUnit _ ≫ g.b := by
    apply Over.OverMorphism.ext
    show ((thickObj R I e G).hom ≫ ae.left) ≫ (U.gt e).pG.left = ((thickObj R I e G).hom ≫ thick R I e) ≫ g.b.left
    rw [Category.assoc, Category.assoc]
    exact congrArg ((thickObj R I e G).hom ≫ ·) (hab _ (Over.w ae) hae)
  have k₃ : TorusCoord.im (U.gt e) (𝟙 (thickObj R I e G)) = (U₂.gt e).pG ≫ β.hom :=
    Over.OverMorphism.ext ((Category.id_comp _).trans hβ.symm)
  have k₄ : (U₂.gt e).pG ≫ (β.hom * (toUnit _ ≫ g.b)) = ((U₂.gt e).pG ≫ β.hom) * (toUnit _ ≫ g.b) := by
    rw [MonObj.comp_mul, ← Category.assoc _ (toUnit _), comp_toUnit]
  rw [k₂, k₃, _root_.mul_comm (toUnit _ ≫ g.b), ← k₄] at k₁
  exact congrArg (fun q => q.left) k₁

end GlobalTheory.MumCmp.Transl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPair
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem linEnd_adjoint_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE g g' hg hg'
  obtain ⟨g₁, hg₁, hiso⟩ := _root_.GlobalTheory.Mum.GroupAdjoint.exists_adjoint_on_group R hR D A G hG U g hg.1
  have h₁ : LinEnd U.toUnifPre a' h g₁ := _root_.GlobalTheory.Mum.AdjEnd.linEnd_of_adjoint R hR D A G hG U a a' h h' hE g g₁ hg hg₁ hiso
  have hu := _root_.GlobalTheory.MumUniq.main R hR.1 D A G hG U a' h
  have heq : g₁ = g' := hu.2 g₁ g' fun e => congrFun (hu.1 _ _ h₁.2 hg'.2) e
  subst heq
  exact hiso

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperUnitarySetupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_model_transport_deeper_unitary_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame X₁.ρ ρ' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → spMap (ratHull R').val.toRingHom ≫ u' = X₁.uΩ → R' ≤ X₁.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀), ∃ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (u₂' : Sp (ratHull R₂) ⟶ Xo.XF cf), USame D.X.ρ ρ₂ (fun x => x) (RingHom.id _) ∧ ρ₂.i₀ = D.X.ρ.i₀ ∧ spMap (ratHull R₂).val.toRingHom ≫ u₂' = D.X.uΩ ∧ R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) ∧ ∃ (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₂ ρ₂.P.A (spMap (toRat R₂)) α₂ ∧ IsGrpPullback G₂ Xo.univ.t.G (u₂' ≫ pullback.fst _ _) β₂ ∧ LBIso (ρ₂.P.L.pull α₂) (Xo.univ.t.PP.L.pull β₂) ∧ (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) ∧ ∃ y₂ : R₂ →+* PadicAlgCl p, (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) ∧ (∀ a : D.X.o₁, ‖y₂ (algebraMap D.X.o₁ R₂ a)‖ ≤ 1) ∧ ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧ (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧ (∀ x₂ (w₂ : Sp (PadicAlgCl p) ⟶ G₂.left), w₂ ≫ α₂ = x₂.left ≫ u₂.φ → ∃ w : Sp (PadicAlgCl p) ⟶ G.left, w ≫ α = (T x₂).left ≫ u.φ ∧ w ≫ β = w₂ ≫ β₂) ∧ (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧ (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  first | exact @GlobalTheory.UPoinc.ULiftW.transport | exact GlobalTheory.UPoinc.ULiftW.transport | (intros; apply GlobalTheory.UPoinc.ULiftW.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitThetaConstantsTwoLevelsIntegralStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_trait_theta_constants_two_levels_integral : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (_ : Unif (IsLocalRing.maximalIdeal W) D A G) (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing W →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : W) → Odd m' → 3 ≤ m' → IsUnit (m' : W) → (letI := A.isAb.comm; HasTh₂ A.A A.L ρ m m' (spMap io) d d') → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap W (FractionRing W))) (fun b => d' b / a) := by
  first | exact @GlobalTheory.SiegTh.CmpUnif.cmp_unif | exact GlobalTheory.SiegTh.CmpUnif.cmp_unif | (intros; apply GlobalTheory.SiegTh.CmpUnif.cmp_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionDivisorEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LKGeo

theorem actOn_tmul_tmul' {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r a : R) (c : C) (v : V) :
    actOn rep R (r ⊗ₜ c) (a ⊗ₜ v) = (r * a) ⊗ₜ rep c v := by
  simp only [actOn, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, AlgHom.coe_comp, Function.comp_apply,
    Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  change r • (rep c).baseChange R (a ⊗ₜ v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem adj_actOn_afP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (actOn L.rep (AfP p) x v) w = (D.EF.baseChange ℚ).baseChange (AfP p) v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := by
  intro p _ D G L x v w
  induction x using TensorProduct.induction_on generalizing v w with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, MulOpposite.unop_add, hx, hy]
  | tmul r c =>
    rw [starT_tmul]
    induction v using TensorProduct.induction_on generalizing w with
    | zero => simp
    | add v v' hv hv' => simp only [map_add (f := _), LinearMap.add_apply, hv, hv']
    | tmul a v₀ =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
      | tmul a' w₀ =>
        rw [actOn_tmul_tmul', actOn_tmul_tmul', LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul, L.adj c v₀ w₀, mul_left_comm, _root_.mul_assoc]
        rfl

end GlobalTheory.LKGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionNearClosedFibreDescendsToBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnitDescent

theorem one_left_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    (1 : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f =
      f ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def]
  erw [Functor.obj.η_def]
  have hw : (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
      pullback.snd (𝟙_ (Over S)).hom f = 𝟙 T := by
    simpa using Over.w (toUnit (Over.mk (𝟙 T)) ≫ Functor.LaxMonoidal.ε (Over.pullback f))
  have hb : (toUnit (Over.mk (𝟙 S))).left = 𝟙 S := by
    simpa using Over.w (toUnit (Over.mk (𝟙 S)))
  have hc : pullback.fst (𝟙_ (Over S)).hom f = pullback.snd (𝟙_ (Over S)).hom f ≫ f := by
    have := pullback.condition (f := (𝟙_ (Over S)).hom) (g := f)
    simpa using this
  have hm : ((Over.pullback f).map (η : 𝟙_ (Over S) ⟶ G)).left ≫ pullback.fst G.hom f =
      pullback.fst (𝟙_ (Over S)).hom f ≫ (η : 𝟙_ (Over S) ⟶ G).left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  simp only [Over.comp_left, Category.assoc] at hw ⊢
  rw [hm, hc, hb]
  simp only [← Category.assoc] at hw ⊢
  rw [hw]
  simp

theorem unit_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u → ∃ e : Sp R ⟶ N.U.left, e ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hSA N hL hr
  haveI : IsNoetherianRing R := hA.1
  haveI : IsIntegrallyClosed R := hA.2.2.1
  haveI := N.isOpen
  have hone_w : (1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom = 𝟙 S := by
    simpa using Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  let x₀ := IsOpenImmersion.lift N.u (1 : Over.mk (𝟙 S) ⟶ G').left hr
  have hx₀u : x₀ ≫ N.u = (1 : Over.mk (𝟙 S) ⟶ G').left := IsOpenImmersion.lift_fac _ _ _
  have hx₀s : x₀ ≫ pullback.snd N.U.hom π = 𝟙 S := by
    rw [← N.u_over, ← Category.assoc, hx₀u, hone_w]
  let h := x₀ ≫ pullback.fst N.U.hom π
  have hh : h ≫ N.U.hom = π := by
    simp only [h, Category.assoc, pullback.condition]
    rw [← Category.assoc, hx₀s]
    simp
  obtain ⟨φ, hmon, hφ⟩ := _root_.GlobalTheory.Mum.Desc.exists_datum R hA S π hP hS hI G' hSA N hL
  let x := (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G').left
  have hxs : x ≫ pullback.snd G'.hom (pullback.fst π π) = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.fst π π)).obj G')
  have hxf : x ≫ pullback.fst G'.hom (pullback.fst π π) = pullback.fst π π ≫ (1 : Over.mk (𝟙 S) ⟶ G').left :=
    one_left_pullback _ _
  have hφ1 : x ≫ φ.hom.left =
      (1 : Over.mk (𝟙 (pullback π π)) ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
    rw [← Over.comp_left]
    congr 1
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have hprem : N.Pt (x ≫ pullback.snd G'.hom (pullback.fst π π) ≫ pullback.fst π π) (pullback.fst π π ≫ h)
      (x ≫ pullback.fst G'.hom (pullback.fst π π)) := by
    rw [reassoc_of% hxs, hxf]
    exact ⟨pullback.fst π π ≫ x₀, by simp [h], by rw [Category.assoc, hx₀s, Category.comp_id],
      by rw [Category.assoc, hx₀u]⟩
  obtain ⟨y₀, hy1, -, hy3⟩ := hφ _ _ x hprem
  rw [← Category.assoc, hφ1, one_left_pullback] at hy3
  have hy : y₀ = pullback.snd π π ≫ x₀ := by
    rw [← cancel_mono N.u, hy3, Category.assoc, hx₀u]
  have heq : pullback.fst π π ≫ h = pullback.snd π π ≫ h := by
    rw [← hy1, hy, Category.assoc]
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨e, he, -⟩ := _root_.GlobalTheory.MorDescent.descend R S (Sp R) S N.U.left π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq h heq
  obtain ⟨e₁, -, huniq⟩ := _root_.GlobalTheory.MorDescent.descend R S (Sp R) S (Sp R) π (𝟙 _) π (𝟙 S) hP hS hI inferInstance sq π
    pullback.condition
  refine ⟨e, ?_, x₀, he.symm, hx₀s, hx₀u⟩
  rw [huniq (e ≫ N.U.hom) (show π ≫ e ≫ N.U.hom = π by rw [← Category.assoc, he, hh]),
    huniq (𝟙 _) (show π ≫ 𝟙 _ = π by simp)]

end GlobalTheory.UnitDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedIntCastLeIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.IntDvdAdele

theorem valued_intCast_le_iff (v : HeightOneSpectrum ℤ) (r : ℤ) (k : ℕ) :
    Valued.v ((r : v.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) ↔ r ∈ v.asIdeal ^ k := by
  have e : ((r : v.adicCompletion ℚ)) = algebraMap ℤ (v.adicCompletion ℚ) r := (eq_intCast _ r).symm
  rw [e, valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, intValuation_le_pow_iff_mem]

def placeAt {p : ℕ} (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) : AwayP p :=
  ⟨⟨Ideal.span {(l : ℤ)},
    (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl),
    by simp [hl.ne_zero]⟩, by
    intro h
    have h' := Ideal.span_singleton_eq_span_singleton.1 h
    rw [Int.associated_iff_natAbs] at h'
    simp at h'
    exact hlp h'⟩

theorem placeAt_asIdeal {p : ℕ} (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) :
    (placeAt (p := p) l hl hlp).1.asIdeal = Ideal.span {(l : ℤ)} := rfl

theorem dvd_of_eq_mul_int : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (z : ℤ) (w : AfP p),
    IsIntAf w → (z : AfP p) = (n : AfP p) * w → (n : ℤ) ∣ z := by
  intro p _ n hn hcop z w hw hz
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro l k hl hlk
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hl' : l.Prime := hl
  have hln : l ∣ n := (dvd_pow_self l hk.ne').trans hlk
  have hlp : l ≠ p := by
    rintro rfl
    have h1 : Nat.Coprime l l := Nat.Coprime.coprime_dvd_left hln hcop
    exact hl'.one_lt.ne' ((Nat.coprime_self l).1 h1)
  set v := placeAt (p := p) l hl' hlp
  have hzv := congrArg (AfP.eval v) hz
  rw [map_intCast, map_mul, map_natCast] at hzv
  have hwv : Valued.v (AfP.eval v w) ≤ 1 := hw v
  have hnv : Valued.v (((n : ℤ) : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact_mod_cast hlk
  have hzle : Valued.v ((z : v.1.adicCompletion ℚ)) ≤ WithZero.exp (-(k : ℤ)) := by
    rw [hzv, map_mul]
    calc Valued.v ((n : v.1.adicCompletion ℚ)) * Valued.v (AfP.eval v w)
        ≤ Valued.v ((n : v.1.adicCompletion ℚ)) * 1 := by gcongr
      _ = Valued.v (((n : ℤ) : v.1.adicCompletion ℚ)) := by rw [_root_.mul_one, Int.cast_natCast]
      _ ≤ _ := hnv
  rw [valued_intCast_le_iff, placeAt_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hzle
  have : ((l ^ k : ℕ) : ℤ) ∣ z := by exact_mod_cast hzle
  exact Int.natCast_dvd.1 this

end GlobalTheory.IntDvdAdele
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeSpanEq
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.GenShift

open IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

theorem exists_twPow (s : TwSec U x Z (wtOf Dw 0 1)) : ∀ n : ℕ, Nonempty (TwSec U x Z (wtOf Dw 0 (n : ℤ))) := by
  intro n
  induction n with
  | zero => exact ⟨(TwSec.const x s.pts 1 one_ne_zero).copy (by rw [Nat.cast_zero, wtOf_zero])⟩
  | succ n ih =>
    obtain ⟨t⟩ := ih
    exact ⟨(t.mul s).copy (by rw [← wtOf_add, add_zero, Nat.cast_succ])⟩


set_option maxHeartbeats 1000000 in
theorem span_latW_add (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G G₀ : WTZ E) (hG : Even G.2)
    (hs : ∀ Z : Comp Xo c, Nonempty (TwSec U x Z G₀))
    (h : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⊤) :
    Submodule.span c.F (latW U (G + G₀) : Set (cuspW Xo c U (G + G₀))) = ⊤ := by
  classical
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [eq_top_iff]
  intro F _
  have hF : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF]
  refine Submodule.sum_mem _ fun Z _ => ?_
  obtain ⟨s⟩ := hs Z
  obtain ⟨φ, -, -, hA, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, -⟩ := GlobalTheory.FlatTw.Good.exists_twist_scalar s
  let p : cuspOn U Z (G + G₀) := ⟨idem Z * (F : Rul Xo c),
    GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, by rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)⟩
  let g : cuspOn U Z G := φ.symm p
  have hmem : (⟨(g : Rul Xo c), g.2.1⟩ : cuspW Xo c U G) ∈ Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) := by
    rw [h]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 c.F)) c.F _ _ hmem
  rw [Submodule.span_eq, Submonoid.smul_def, ← algebraMap_smul c.F] at ht
  set d : c.F := algebraMap (𝓞 c.F) c.F t with hd
  have hd0 : d ≠ 0 := by simpa [hd] using nonZeroDivisors.ne_zero t.2
  have hf : d • g ∈ latOn U Z G := (mem_latOn U).2 ht
  have hq := hA a ha0 hlo (d • g) hf ((a * d) • p) (by
    simp only [g, map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul, smul_smul])
  have hq' := (mem_latOn U).1 hq
  have had : a * d ≠ 0 := mul_ne_zero ha0 hd0
  have e : (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) =
      (a * d)⁻¹ • (⟨(((a * d) • p : cuspOn U Z (G + G₀)) : Rul Xo c), ((a * d) • p).2.1⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, smul_smul, inv_mul_cancel₀ had, one_smul, p]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hq')

end General

end GlobalTheory.GenShift
end
end

