module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1931
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0057
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFst
section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def IsProjMat {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (σ : 𝓞 E →+* R) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Matrix (Fin g) (Fin g) R) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S),
    EigRowsAt t (spMap φ ≫ ξ) (φ.comp σ) (bcV t φ e) (U.map φ) ∧
    ∀ w v, IsCombAtG t (spMap φ ≫ ξ) (bcV t φ e) w v → IsEigG t (φ.comp σ) v →
      Matrix.vecMul w (U.map φ) = ((discr E : ℤ) : S) • w


open GlobalTheory.FlatModel.Proj in
theorem exists_isProjMat {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t ξ e) (σ : 𝓞 E →+* R) :
    ∃ U : Matrix (Fin g) (Fin g) R, IsProjMat t ξ σ e U := by
  classical
  let b := RingOfIntegers.basis E
  obtain ⟨c, hc1, hc2⟩ := exists_dual b (discr_ne_zero E)
  have hbas : ∀ w, IsTanAtG t ξ w → ∃ a, IsCombAtG t ξ e a w := fun w hw => by
    have h0 : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
      have : dualMap (RingHom.id R) = RingHom.id _ := by ext s <;> simp [dualMap]
      rw [this]
      exact Spec.map_id _
    have := he.2 R (RingHom.id R) w (by rwa [h0, Category.id_comp])
    simp only [h0, h1, Category.id_comp] at this
    exact this.exists
  choose ρ hρ using fun (a : 𝓞 E) (k : Fin g) =>
    hbas _ (GlobalTheory.LieMet.isTan_tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k))))
  refine ⟨Matrix.of fun k j => ∑ i, σ (c i) * ρ (b i) k j, fun S _ φ => ?_⟩
  have he' := isTanBasis_bc he φ
  let T : Fin g → TanM (spMap φ ≫ ξ) t.G := fun j => GlobalTheory.LieMet.tanOf (he'.1 j)
  have hT : bcV t φ e = fun j => (tv (T j)).left := rfl
  have hA : ∀ a k, actR t.act a (T k) = ∑ j, φ (ρ a k j) • T j := fun a k => by
    refine (GlobalTheory.LieMet.isComb_iff T _ _).1 ?_
    have := GlobalTheory.GradedPieces.comb_map φ rfl (hρ a k)
    have e1 : spMap (dualMap φ) ≫ (tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k)))).left =
        (tv (actR t.act a (T k))).left := (Category.assoc _ _ _).symm
    rw [e1] at this
    exact this
  have hU : ∀ k, ∑ j, φ (∑ i, σ (c i) * ρ (b i) k j) • T j = ∑ i, (φ.comp σ) (c i) • actR t.act (b i) (T k) := fun k => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hA, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul, RingHom.comp_apply]
    exact Finset.sum_comm
  refine ⟨fun k u hu a => ?_, fun w v hw hv => ?_⟩
  · rw [hT] at hu
    rw [eq_of_comb T hu, GlobalTheory.ShFam.Pad.Pull.eig_iff]
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [hU]
    exact eig_proj _ _ b c hc1 a _
  · rw [hT] at hw
    have hv0 := eq_of_comb T hw
    have hv1 : ∀ a, actR t.act a (∑ i, w i • T i) = (φ.comp σ) a • ∑ i, w i • T i := fun a => by
      rw [← GlobalTheory.ShFam.Pad.Pull.eig_iff, ← hv0]
      exact hv a
    have h2 := proj_eig _ _ b c hc2 _ hv1
    have h3 : ∑ j, (∑ k, w k • fun j => φ (∑ i, σ (c i) * ρ (b i) k j)) j • T j =
        ∑ j, (((discr E : ℤ) : S) • w) j • T j := by
      have h4 : ∑ j, (((discr E : ℤ) : S) • w) j • T j = ((discr E : ℤ) : S) • ∑ j, w j • T j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      rw [h4]
      refine Eq.trans ?_ h2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hU]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have hu := he.2 S φ _ (GlobalTheory.LieMet.isTan_tv (∑ j, (((discr E : ℤ) : S) • w) j • T j))
    have h5 := hu.unique ((GlobalTheory.LieMet.isComb_iff T _ _).2 rfl) ((GlobalTheory.LieMet.isComb_iff T _ _).2 h3.symm)
    rw [h5]
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsFrameCoord (Y : Model Xo c β) {R : Type} [CommRing R] (ξ : Sp R ⟶ Y.X) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)) (U : Matrix (Fin g) (Fin g) R) {k : Type} [CommRing k]
    [Algebra c.F k] (φ : R →+* k) (y : FrPt Xo c k) (σ : E →+* ℂ) (M : Matrix (Fin (Dw.mult σ)) (Fin g) k)
    (C : Matrix (Fin g) (Fin (Dw.mult σ)) k) : Prop :=
  (∀ i, ∃ w : Sp (DualNumber k) ⟶ Y.oF.t.G.left,
    w ≫ Y.oF.t.G.hom = spMap (algebraMap k (DualNumber k)) ≫ GlobalTheory.AllWt.ptF y ∧ w ≫ Y.m0.toSABMap.φ = y.u σ i ∧
      IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (M i) (w ≫ Y.m.φ)) ∧
  C * M = U.map φ ∧ M * C = ((discr E : ℤ) : k) • (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) k)

def DetLaw (Z : Comp Xo c) (f : Rul Xo c) (σ₁ σ₂ : E →+* ℂ) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
  ∀ (k : Type) [Field k] [Algebra c.F k] (z y : FrPt Xo c k), LiesOn Z y → z.x = y.x →
    ∀ (g₁ : Matrix (Fin (Dw.mult σ₁)) (Fin (Dw.mult σ₁)) k) (g₂ : Matrix (Fin (Dw.mult σ₂)) (Fin (Dw.mult σ₂)) k),
      (∀ i, IsCombAt y.x (y.u σ₁) (g₁ i) (z.u σ₁ i)) → (∀ i, IsCombAt y.x (y.u σ₂) (g₂ i) (z.u σ₂ i)) →
      evR Xo c f z * g₁.det = g₂.det * evR Xo c f y

theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  infer_instance

theorem isPreimmersion_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsPreimmersion Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  unfold Model.j
  infer_instance

end GlobalTheory.FlatDenom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelAmpleQProjNoeth

open GlobalTheory.RelAmpleQProj

theorem isQProjOver_of_relAmple_noeth : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0})
    (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L →
    IsQProjOver (A.hom ≫ s) := by
  rintro K _ _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProjNoeth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GaloisQuotientRing
open GlobalTheory.GaloisQuotient

theorem isQProjOver_of_isGaloisCover : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  intro K _ _ X Y π sY Ga _ ρ hG _ _ hX
  have := hG.finite
  let τ : Ga →* Aut X := MonoidHom.mk'
    (fun a => Aut.of (⟨ρ a⁻¹, ρ a, by rw [← hG.mul, inv_mul_cancel, hG.one], by rw [← hG.mul, mul_inv_cancel, hG.one]⟩ :
      X ≅ X))
    fun a c => Aut.ext (Iso.ext (by
      change ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹
      rw [mul_inv_rev, hG.mul]))
  have := OrbitsInAffineOpens.of_isQProjOver hX τ
  obtain ⟨Y', q, hq⟩ := (exists_isAffineQuotient_iff τ).mpr inferInstance
  have hD := (GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hG).1
  obtain ⟨u, hu, -⟩ := hD _ q fun a => by
    simpa only [inv_inv] using (show ρ a⁻¹⁻¹ ≫ _ = _ from hq.comp_eq a⁻¹)
  let v := hq.desc π fun a => hG.inv a⁻¹
  have hv : q ≫ v = π := hq.comp_desc _ _
  have : IsIso u := ⟨v, (hD Y π hG.inv).unique (by rw [reassoc_of% hu, hv]) (Category.comp_id _),
    hq.hom_ext (by rw [reassoc_of% hv, hu, Category.comp_id])⟩
  obtain ⟨L, hL⟩ := exists_isAmpleLB_of_isAffineQuotient hq hX
  exact (hL.pull_of_isAffineHom u).isQProjOver sY

end GlobalTheory.GaloisQuotientRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShortRuleOfRaw
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.RawSpan

theorem isShortRule_of_raw : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ {n : ℕ} {Λ : GenLat E n} {N : ℕ},
    Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F},
    P ∈ harmL c Λ a → ∀ (x0 : Fin n → Dw.La) (f : Rul Xo c), f ∈ sec Xo c a n →
    (∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (x0Dat c x0) Λ N P y (f p y)) →
    IsShortRule Xo c (GlobalTheory.RawSpan.idCover nab n) Λ N x0 P ((betaH (Dw := Dw) c Λ)⁻¹ • f) := by
  intro E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hO a P hP x0 f hf h
  intro k _ _ i1 i2 hk y y₂ hov
  have e : i1 = i2 := (Algebra.algebra_ext _ _ fun a => hk a).symm
  subst e
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  letI : Algebra (idCover nab n).c₂.F k := i1
  have hyy : (y₂ : FrPt Xo c k) = y :=
    GlobalTheory.CoverSec.frOver_unique (idCover nab n) hL.globalFns (frOver_self nab n y₂) hov
  subst hyy
  have hβ := betaH_ne_zero (Dw := Dw) (c := c) Λ
  have hAT := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c
  have hW := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1
  obtain ⟨p, φ, y0, h0⟩ := hAT k y₂
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 (x0Dat c x0) 1
  obtain ⟨v1, hv1, -⟩ := hval k y₂
  have e1 : φ (f p y0) = v1 := hnat p.R k φ y0 y₂ h0 _ _ (h p y0) hv1
  have hsm : (betaH (Dw := Dw) c Λ)⁻¹ • f ∈ sec Xo c a n := Submodule.smul_mem _ _ hf
  have e2 : evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂ = φ (((betaH (Dw := Dw) c Λ)⁻¹ • f) p y0) :=
    GlobalTheory.CoverDescent.evR_of_test hW _ hsm.1 p φ y0 y₂ h0
  have e3 : ((betaH (Dw := Dw) c Λ)⁻¹ • f) p y0 = algebraMap c.F p.R (betaH (Dw := Dw) c Λ)⁻¹ * f p y0 :=
    Algebra.smul_def (betaH (Dw := Dw) c Λ)⁻¹ (f p y0)
  refine ⟨evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂, ?_, ?_⟩
  · have e4 : MvPolynomial.map ((idCover nab n).eF : c.F →+* (idCover nab n).c₂.F) P = P := MvPolynomial.map_id P
    rw [e4, GlobalTheory.LevelCoverDatum.noDelta_w]
    refine (GlobalTheory.Survey.BaseClassMove.shortValAt_beta Xo c nab _ Λ (betaH (Dw := Dw) c Λ) hβ N P y₂ _).2 ?_
    rw [e2, e3, map_mul, AlgHom.commutes, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hβ, map_one, one_mul, e1]
    exact hv1
  · exact ((congrArg (· * evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂) (evR_one_field k y₂)).trans (one_mul _)).symm
end GlobalTheory.RawSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitThetaKeyScalarGoodReductionChart
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.KeyUnitGood

theorem exists_unit_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K) (u : Aˣ)
    (hx : la x = algebraMap A B u) : ∃ v : Rˣ, x = algebraMap R K v := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h : e r = u := IsFractionRing.injective A B (by rw [← hla, hr, hx])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ u.isUnit)
    exact ⟨v, hr.symm⟩
  · have h : e r = (u⁻¹ : Aˣ) := IsFractionRing.injective A B (by rw [← hla, hr, map_inv₀, hx, map_units_inv])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ (u⁻¹).isUnit)
    exact ⟨v⁻¹, by rw [map_units_inv, hr, inv_inv]⟩

theorem isUnit_key_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y κ hκ M R K _ _ _ _ _ _ _ z hz y hy hab x hx
  have : CharZero R := (algebraMap R K).charZero
  obtain ⟨T, i, hi, hil⟩ : ∃ (T : Formalism.L2.Pj.CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i :=
    ⟨GlobalTheory.CountableCompletion.completionCDVR R, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance⟩
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  let iK : K →+* T.Fr := IsFractionRing.lift hiF
  have hiK : ∀ r, iK (algebraMap R K r) = algebraMap T.V T.Fr (i r) := fun r => IsFractionRing.lift_algebraMap hiF r
  have hsq : spMap iK ≫ spMap (algebraMap R K) = spMap (algebraMap T.V T.Fr) ≫ spMap i := by
    rw [← GlobalTheory.KeyAtBC.spMap_comp₀, ← GlobalTheory.KeyAtBC.spMap_comp₀]
    exact congrArg spMap (RingHom.ext hiK)
  have hpt : spMap iK ≫ spMap (algebraMap R K) ≫ z = spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z := by
    rw [← Category.assoc, hsq, Category.assoc]
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap i ≫ z) Y.t
  obtain ⟨tK, ⟨mK⟩⟩ := exists_sab (spMap (algebraMap T.V T.Fr)) t
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp m mK
  have hj : spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z = (spMap iK ≫ y) ≫ Y.j := by
    rw [← hpt, Category.assoc, hy]
  obtain ⟨n₁, -⟩ := ObjMaps.exists_sab_cancel (show SABMap Y.oF.t Y.t Y.j from Y.m) (hj ▸ n)
  obtain ⟨n₂, -⟩ := ObjMaps.exists_sab_comp Y.m0.toSABMap n₁
  have hp : IsProper t.G.hom := GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H D l Xo T _ t tK n₂ mK
    (Set.eq_univ_of_forall fun q => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 q).1
      (hab ⟨spMap i q, (Scheme.Hom.comp_apply _ _ _).symm⟩))
  obtain ⟨-, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv (show SABMap Y.oF.t Y.t Y.j from Y.m)
    Y.oF.proper Y.oF.ample Y.oF.ktriv n (by
      rw [hj]
      rintro _ ⟨q, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩)
  have hA' : Out.RelAmple t.G t.PP.L := GlobalTheory.GoodPol.relAmple_of_generic GlobalTheory.firstFiveLaws.1
    ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.cub mK.cart tK.PP.isLB
    (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mK) hA hK
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x iK
  have hzT : ⊤ ≤ (spMap i ≫ z) ⁻¹ᵁ M.U := le_preimage_comp _ hz
  have h₁ : KeyAt M (spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z) (le_preimage_comp _ hzT) x' := by
    have cast : ∀ (p q : Sp T.Fr ⟶ Y.X) (_ : p = q) hp hq, KeyAt M p hp x' → KeyAt M q hq x' := by
      rintro p q rfl _ _ h
      exact h
    exact cast _ _ hpt _ _ (GlobalTheory.KeyAtBC.keyAt_of_keyPB hx hx')
  obtain ⟨xT, -, hT⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hzT m hp hA' _ h₁
  obtain ⟨u, hu, -⟩ := hκ.2.2.1 T.V T.Fr xT x' (GlobalTheory.KeyAtBC.keyPB_of_keyAt hT h₁)
  exact exists_unit_of_map i iK hiK _ u ((hκ.2.1 K T.Fr iK x x' hx').symm.trans hu)

end GlobalTheory.KeyUnitGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarySplittingTransportedDoubledWeilDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblSchr

open Matrix

section Gen

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem actAB_one_reG (e : γ ≃ β) {JA : Matrix α α E} {J : Matrix β β E} {J' : Matrix γ γ E} (h : J' = J.submatrix e e)
    (g : GlobalTheory.WeilM.UG c J) (w : Matrix α β E) :
    GlobalTheory.WeilM.actAB c ((1 : GlobalTheory.WeilM.UG c JA), reG c e h g) (w.submatrix id e) =
      (GlobalTheory.WeilM.actB c g w).submatrix id e := by
  simp only [GlobalTheory.WeilM.actAB, GlobalTheory.WeilM.actB, reG_val, OneMemClass.coe_one, Units.val_one, Matrix.one_mul,
    Matrix.transpose_submatrix]
  exact Matrix.submatrix_mul_equiv _ _ _ _ _

theorem continuous_reG [TopologicalSpace E] (e : γ ≃ β) {J : Matrix β β E} {J' : Matrix γ γ E}
    (h : J' = J.submatrix e e) : Continuous (reG c e h) := by
  unfold reG
  refine Continuous.subtype_mk ?_ _
  refine (Continuous.units_map (Matrix.reindexAlgEquiv E E e.symm).toAlgHom.toMonoidHom ?_).comp continuous_subtype_val
  exact (continuous_id (X := Matrix β β E)).matrix_reindex e.symm e.symm

end Gen

section Read

variable {D : D7} [Invertible (2 : AF D.host.F)]

theorem dblD_rho_eq {S T : HSp D} {ξ : AF D.host.F ⊗[D.host.F] D.host.E} {JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E}
    {JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (ψ : AddChar (AF D.host.F) ℂ) (w : Matrix (Fin T.rank) (Fin S.rank ⊕ Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (dblD _ co).rho ψ w = (ddr co).rho ψ (w.submatrix id finSumFinEquiv.symm) := by
  unfold GlobalTheory.WeilM.Darboux.rho ddr
  rw [reD_e, Matrix.submatrix_submatrix]
  simp

end Read

end GlobalTheory.DblSchr

namespace GlobalTheory.DblSchr


set_option maxHeartbeats 1000000 in
theorem isUSplitting_omdOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co)
            (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco ωd hωd omd₀ htr
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have r1 : ResEta D 1 (GlobalTheory.Doubling.dblSp S).rank := GlobalTheory.Core.Rk.IP.FockModel.resEta_one_dbl S rT
  have hξd := GlobalTheory.DblSchr.dblGram_xi D S JB ξ hξ
  have hrat := GlobalTheory.DblSchr.ddr_rat D S T JA JB ξ κ co hco
  obtain ⟨hpres, himpl⟩ := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hadm := _root_.GlobalTheory.WeilAdm.transport_adm D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hunit := _root_.GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hcont := _root_.GlobalTheory.WeilCont.continuous_transport D ψ hψ (GlobalTheory.Doubling.dblSp S) T 1 χT h1 hT r1 rT JA (JBd S JB) ξ hJA hξd
    (κ ⊕ κ) (ddr co) hrat ωd hωd omd₀ htr
  have hom : ∀ g, omdOf omd₀ g = omd₀ (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) := fun _ => rfl
  refine { pres := ?_, impl := ?_, adm := ?_, unit := ?_, cont := ?_ }
  · intro g φ hφ
    rw [hom]
    exact hpres _ φ hφ
  · intro g w φ hφ
    have e1 := dblD_rho_eq co ψ w
    have e2 := dblD_rho_eq co ψ (GlobalTheory.WeilM.actB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) g w)
    have e3 := himpl (1, reG _ finSumFinEquiv.symm (incM_JBd S JB) g) (w.submatrix id finSumFinEquiv.symm) φ hφ
    have e4 := actAB_one_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (JA := incM D.host.F JA) (incM_JBd S JB) g w
    rw [e4] at e3
    rw [hom]
    exact (congrArg (fun f => omd₀ _ (f φ)) e1).trans (e3.trans (congrFun e2 _).symm)
  · intro g l hl
    rw [hom]
    exact hadm _ l hl
  · exact hunit.comp _
  · have hr := continuous_reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB)
    have hp : Continuous fun g => ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)),
        reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (incM_JBd S JB) g) := continuous_const.prodMk hr
    intro l hl φ hφ
    exact Continuous.congr ((hcont l hl φ hφ).comp hp) (fun g => rfl)

end GlobalTheory.DblSchr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugateStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_unitary_conjugate : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∃ κ : UA σ W.J → ℂ, ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val) := by
  first | exact @GlobalTheory.LinWShape.shape_right | exact GlobalTheory.LinWShape.shape_right | (intros; apply GlobalTheory.LinWShape.shape_right <;> assumption)
end

