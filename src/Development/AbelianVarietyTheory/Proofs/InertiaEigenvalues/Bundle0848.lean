module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormBoundGoodPointsExtendsAllPoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0832
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingRelationTransferIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnivCharCopy

theorem ring_relation_transfer_identity {R R' : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R} {H' : Formalism.BasicNotions.Host R'} {Ω Ω' : Type}
    [iΩ : Field Ω] [iΩ' : Field Ω'] [aΩ : Algebra H.E Ω] [aΩ' : Algebra H'.E Ω'] {T T' : Type}
    {cc : Ω ≃+* Ω} {cc' : Ω' ≃+* Ω'} {l : T → ℕ} {l' : T' → ℕ}
    {d : ∀ i (Q : Finset (PlE H)) (M : ℕ), G H.E Ω →* Multiplicative (DelQM H (l i) Q M)}
    {d' : ∀ i (Q : Finset (PlE H')) (M : ℕ), G H'.E Ω' →* Multiplicative (DelQM H' (l' i) Q M)}
    (hR : R = R') (hH : HEq H H') (hΩ : Ω = Ω') (hi : HEq iΩ iΩ') (ha : HEq aΩ aΩ') (hcc : HEq cc cc')
    (hT : T = T') (hl : HEq l l') (hd : HEq d d')
    (h : ∀ i Q M, d i Q M = GlobalTheory.GalChar.delU H cc (l i) Q M) :
    ∀ i Q M, d' i Q M = GlobalTheory.GalChar.delU H' cc' (l' i) Q M := by
  subst hR; cases hH; subst hΩ; cases hi; cases ha; cases hcc; subst hT; cases hl; cases hd
  exact h

theorem isUnivChar_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e), GlobalTheory.UnivChar.IsUnivChar D.nexp → GlobalTheory.UnivChar.IsUnivChar D'.nexp := by
  intro D D' ι e h hU
  exact ring_relation_transfer_identity h.gal.R h.gal.host (eq_of_heq h.gal.Om) h.gal.instOm h.gal.algOm h.set.cc
    (eq_of_heq h.set.Tw) h.set.l h.delU hU

end GlobalTheory.UnivCharCopy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SectionIntegralEqualCharAbelianLocus
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

namespace GlobalTheory.EqCharGood

theorem existsUnique_mulVec_of_inCell {V K : Type} [CommRing V] [CommRing K] (φ : V →+* K)
    (hφ : Function.Injective φ) {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V)
    (hc : GlobalTheory.Reg.InCell ix u) (cv : Fin n → V) (aK : Fin r → K)
    (h : (u.map φ).mulVec aK = fun i => φ (cv i)) : ∃! a, u.mulVec a = cv := by
  let A : Matrix (Fin r) (Fin r) V := u.submatrix ix id
  have hlow : A.BlockTriangular OrderDual.toDual := fun i j hij => hc.1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_lowerTriangular A hlow]
    exact Finset.prod_eq_one fun i _ => hc.2 i
  have hAu : IsUnit A.det := hdet ▸ isUnit_one
  have hAK : IsUnit (A.map φ).det := by
    have e : (A.map φ).det = φ A.det := (RingHom.map_det φ A).symm
    rw [e, hdet, map_one]; exact isUnit_one
  have hinjA : ∀ v w : Fin r → V, A.mulVec v = A.mulVec w → v = w := fun v w hvw => by
    have := congrArg (A⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hinjAK : ∀ v w : Fin r → K, (A.map φ).mulVec v = (A.map φ).mulVec w → v = w := fun v w hvw => by
    have := congrArg ((A.map φ)⁻¹).mulVec hvw
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAK, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  have hrow : ∀ (v : Fin r → V), A.mulVec v = fun i => u.mulVec v (ix i) := fun v => rfl
  let a : Fin r → V := A⁻¹.mulVec (fun i => cv (ix i))
  have ha : A.mulVec a = fun i => cv (ix i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
  have hmap : ∀ (M : Matrix (Fin n) (Fin r) V) (v : Fin r → V),
      (M.map φ).mulVec (fun i => φ (v i)) = fun i => φ (M.mulVec v i) := fun M v => by
    funext i
    exact (RingHom.map_mulVec φ M v i).symm
  have haK : (fun i => φ (a i)) = aK := by
    refine hinjAK _ _ ?_
    have e1 : (A.map φ).mulVec (fun i => φ (a i)) = fun i => φ (cv (ix i)) := by
      funext i
      exact (congrFun (hmap u a) (ix i)).trans (congrArg φ (congrFun ha i))
    rw [e1]
    funext i
    exact (congrFun h (ix i)).symm
  refine ⟨a, ?_, fun a' ha' => hinjA _ _ ((hrow a').trans ((funext fun i => congrFun ha' (ix i)).trans ha.symm))⟩
  funext i
  apply hφ
  have := congrFun (hmap u a) i
  rw [haK, h] at this
  exact this.symm

end GlobalTheory.EqCharGood

namespace GlobalTheory.EqCharGood


set_option maxHeartbeats 2000000 in
theorem inV_of_extIn_eqChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → ∀ y : IntFr Xo c T io, (letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) → evI y f ∈ (algebraMap T.V T.Fr).range := by
  intro E _ _ _ H Dw l Xo c a n f hf la Y hP T io hio y hy
  classical
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hS := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  obtain ⟨k, hk⟩ := exists_factor T io hio
  obtain ⟨y', z, h1, h2, h3, h4⟩ := hy
  have hs : y' ≫ Y.s = spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
    have e1 : spMap (algebraMap T.V T.Fr) ≫ (y' ≫ Y.s) =
        spMap (algebraMap T.V T.Fr) ≫ spMap (k.comp (la.valuation c.F).valuationSubring.subtype) := by
      rw [← Category.assoc, ← h3, Category.assoc, GlobalTheory.TraitDataIntrinsic.j_s, ← Category.assoc, h2, sp_comp,
        sp_comp, ← RingHom.comp_assoc, hk]
    obtain ⟨φ, hφ⟩ : ∃ φ : (la.valuation c.F).valuationSubring →+* T.V, y' ≫ Y.s = spMap φ :=
      ⟨(Spec.preimage (y' ≫ Y.s)).hom, by simp [spMap]⟩
    rw [hφ, sp_comp, sp_comp] at e1
    rw [hφ]
    congr 1
    have e2 := CommRingCat.hom_ext_iff.1 (Spec.map_injective e1)
    exact RingHom.ext fun x => hinj (RingHom.congr_fun e2 x)
  let _ : Algebra c.F T.V := k.toAlgebra
  let _ : Algebra c.F T.Fr := io.toAlgebra
  obtain ⟨zV, hzV1, hzV2⟩ := exists_lift Y y' k hs h4
  obtain ⟨J, _, M, hM⟩ := GlobalTheory.Reg.exists_finite_mchart_cover E H Dw l Xo c (la.valuation c.F).valuationSubring _ Y hP
  obtain ⟨j, hj⟩ := hM (y' (IsLocalRing.closedPoint T.V))
  obtain ⟨-, -, h3'⟩ := GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c _ _ Y
  obtain ⟨-, -, -, h4'⟩ := h3' (M j).U (M j).hU
  obtain ⟨f₀, hf₀, -⟩ := h4' T.V y' hj
  obtain ⟨ΛV⟩ := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.V f₀ zV hzV2 (hzV1.trans hf₀.symm)
  have hzj : z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp f₀) ≫ (M j).hU.fromSpec := by
    rw [h3, ← hf₀, ← Category.assoc, sp_comp]
  have hK := GlobalTheory.Reg.MChart.nonempty_lift E H Dw l Xo c _ _ Y (M j) T.Fr _ z h2 hzj
  rw [h1] at hK
  obtain ⟨ΛK⟩ := hK
  obtain ⟨g, hg, hgi⟩ := GlobalTheory.Reg.MChart.Lift.exists_coordinates E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 ΛK
  let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
  have hW : ∀ x, x ∈ W → InV T x := fun x h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h
  choose ix u b huW hu0 hu1 hbt hbd hgub using
    fun τ => GlobalTheory.exists_integral_pivot_decomposition T.Fr W _ _ (g τ) (hgi τ)
  choose u₀' hu₀' using fun τ i j => hW _ (huW τ i j)
  let u₀ : ∀ τ : E →+* ℂ, Matrix (Fin (M j).n) (Fin (Dw.mult τ)) T.V := fun τ => Matrix.of fun i j' => u₀' τ i j'
  have hu₀ : ∀ τ i j', algebraMap T.V T.Fr (u₀ τ i j') = u τ i j' := hu₀'
  have hcell : ∀ τ, GlobalTheory.Reg.InCell (ix τ) (u₀ τ) := fun τ =>
    ⟨fun i j hij => hinj (by rw [hu₀, map_zero]; exact hu0 τ i j hij),
     fun i => hinj (by rw [hu₀, map_one]; exact hu1 τ i)⟩

  have heigMap : ∀ τ (cv : Fin (M j).n → T.V),
      (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun i => algebraMap T.V T.Fr (cv i)) ↔ (M j).Eig f₀ τ cv := by
    intro τ cv
    refine forall_congr' fun a' => ?_
    have key : ∀ i, algebraMap T.V T.Fr ((((M j).ρ a').map f₀).mulVec cv i) =
        ((((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀)).mulVec (fun i => algebraMap T.V T.Fr (cv i))) i :=
      fun i => by rw [RingHom.map_mulVec]; rfl
    have key2 : ∀ i, algebraMap T.V T.Fr ((algebraMap c.F T.V (embK c τ a') • cv) i) =
        (algebraMap c.F T.Fr (embK c τ a') • fun i => algebraMap T.V T.Fr (cv i)) i := fun i => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      exact congrArg (· * _) (RingHom.congr_fun hk _)
    constructor
    · intro h
      funext i
      apply hinj
      rw [key, key2]
      exact congrFun h i
    · intro h
      funext i
      rw [← key, ← key2, h]
  have humap : ∀ τ, (u₀ τ).map (algebraMap T.V T.Fr) = u τ := fun τ => Matrix.ext fun i j' => hu₀ τ i j'
  have heigK : ∀ τ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => u τ j' i) := by
    intro τ i a'
    have hgc : ∀ i, (M j).Eig ((algebraMap T.V T.Fr).comp f₀) τ (fun j' => g τ j' i) := fun i =>
      (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ (hg τ i)).mp (y.1.eig τ i)
    have hG := (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols (((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀))
      (algebraMap c.F T.Fr (embK c τ a')) (g τ)).mpr fun i => hgc i a'
    have hd : IsUnit (b τ).det := by
      rw [Matrix.det_of_upperTriangular (hbt τ)]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => hbd τ i).isUnit
    have hU : ((M j).ρ a').map ((algebraMap T.V T.Fr).comp f₀) * u τ = algebraMap c.F T.Fr (embK c τ a') • u τ := by
      have e : u τ = g τ * (b τ)⁻¹ := by rw [hgub τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      rw [e, ← Matrix.mul_assoc, hG, Matrix.smul_mul]
    exact (GlobalTheory.Reg.CellChart.mul_eq_smul_iff_cols _ _ _).mp hU i
  have heigV : ∀ τ i, (M j).Eig f₀ τ (fun j' => u₀ τ j' i) := fun τ i =>
    (heigMap τ _).mp (by simpa only [hu₀] using heigK τ i)
  obtain ⟨hv1, hv2, hv3⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK
  have hbasis : ∀ τ cv, (M j).Eig f₀ τ cv → ∃! a, (u₀ τ).mulVec a = cv := by
    intro τ cv hcv
    have hcvK := (heigMap τ cv).mpr hcv
    obtain ⟨w, hw, -⟩ := hv1 (fun i => algebraMap T.V T.Fr (cv i))
    have htan := hv2 _ _ hw
    have heig := (GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK τ _ _ hw).mpr hcvK
    obtain ⟨a0, ha0, -⟩ := y.1.basis τ w htan heig
    have hv := (_root_.GlobalTheory.Reg.VecComb.isCombAt_iff_vec E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1.x ΛK _ (fun i j' => g τ j' i) (y.1.u τ) a0 w
      (hg τ)).mp ha0
    have heq : (∑ i, a0 i • fun j' => g τ j' i) = fun i => algebraMap T.V T.Fr (cv i) := (hv3 w htan).unique hv hw
    refine GlobalTheory.EqCharGood.existsUnique_mulVec_of_inCell (algebraMap T.V T.Fr) hinj (ix τ) (u₀ τ) (hcell τ) cv
      ((b τ).mulVec a0) ?_
    rw [humap, Matrix.mulVec_mulVec, ← hgub τ, ← heq]
    funext j'
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨yV, -, hyV⟩ := GlobalTheory.Reg.exists_frPt_tie hS E H Dw l Xo c _ _ Y (M j) T.V f₀ _ ΛV u₀ heigV hbasis
  let φ : T.V →ₐ[c.F] T.Fr := ⟨algebraMap T.V T.Fr, fun x => RingHom.congr_fun hk x⟩
  obtain ⟨zK, hzK⟩ := hE.bc _ _ φ yV
  have htK := GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c _ _ Y (M j) T.V T.Fr f₀ φ u₀ yV zK hyV hzK
  have hint : Integral T io zK := GlobalTheory.Reg.tie_integral hS E H Dw l Xo c _ _ Y (M j) hP T io f₀ ix u₀ hcell zK
    (GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun _ _ _ => rfl))
  have htu : (M j).Comparison₂ ((algebraMap T.V T.Fr).comp f₀) u zK :=
    GlobalTheory.Reg.CellChart.tie_congr htK (fun _ => rfl) (fun τ i j' => hu₀ τ i j')
  obtain ⟨t, ht⟩ := GlobalTheory.Reg.frBor_of_tie E H Dw l Xo c _ _ Y (M j) T.Fr _ y.1 zK ΛK u b
    (GlobalTheory.Reg.CellChart.lift_point_unique htu.choose ΛK) (fun τ => ⟨hbt τ, hbd τ⟩)
    (by rw [show (fun τ => u τ * b τ) = g from funext fun τ => (hgub τ).symm]; exact hg) htu
  show InV T (evI y f)
  rw [inV_of_frBor hf y ⟨zK, hE.test _ zK, hint⟩ t ht]
  show InV T (evR Xo c f zK)
  rw [(GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf T.V).1 T.Fr φ yV zK hzK]
  exact ⟨_, rfl⟩

end GlobalTheory.EqCharGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenExport
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

theorem isInv_twGL_iff {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (W : Submodule K (Fin a → K)) : IsInv (twGL χ r) W ↔ IsInv r W := by
  constructor
  · intro h g v hv
    have := W.smul_mem (((χ g)⁻¹ : Kˣ) : K) (h g v hv)
    rwa [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at this
  · intro h g v hv
    rw [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (h : IsSSRep r) : IsSSRep (twGL χ r) := fun W hW =>
  let ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff χ r W).1 hW)
  ⟨W', (isInv_twGL_iff χ r W').2 h1, h2⟩

variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

end GlobalTheory.TripInhab

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

end GlobalTheory.TripInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPairsEq
section
namespace GlobalTheory.WeightSumSplit

theorem sum_above {N : ℕ} (i : Fin N) (c : ℤ) :
    (∑ j : Fin N, if i < j then c else 0) = ((N : ℤ) - 1 - (i : ℕ)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi, nsmul_eq_mul]
  have hi := i.isLt
  congr 1
  omega

theorem sum_below {N : ℕ} (j : Fin N) (c : ℤ) :
    (∑ i : Fin N, if i < j then c else 0) = ((j : ℕ) : ℤ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio, nsmul_eq_mul]

theorem sum_pairs_eq (N : ℕ) (a : Fin N → ℤ) :
    (∑ i : Fin N, ∑ j : Fin N, if i < j then a i - a j else 0)
      = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  have h1 : ∀ i j : Fin N, (if i < j then a i - a j else 0) =
      (if i < j then a i else 0) - (if i < j then a j else 0) := by
    intro i j
    split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin N => if i < j then a j else 0)]
  simp_rw [sum_above, sum_below, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem wtS_eq : ∀ (N : ℕ) (a : Fin N → ℤ),
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((↑N : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * a i := by
  intro N a
  unfold GlobalTheory.CellDec.wtS
  exact sum_pairs_eq N a

end GlobalTheory.WeightSumSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVectorStatement
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ), Module.finrank ℝ (Fin a → Cinf E) ≤ N → ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A → (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J → c ξ = 0) → (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 → (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J → ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤ A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) → Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧ ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  first | exact @GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | exact GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest | (intros; apply GlobalTheory.RSTheta.summable_tsum_norm_le_of_le_shortest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSchurSquareCellProductEqEulerProduct
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCellSum

theorem schurDir_eq_tsum_locFac (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) :
    GlobalTheory.RSPole.schurDir q α x = ∑' ν : Fin n → ℤ, GlobalTheory.RSCell.locFac q α x ν := by
  let g : {l : Fin n → ℕ // Antitone l} → (Fin n → ℤ) := fun l i => (l.1 i : ℤ)
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    funext i
    have := congrFun h i
    simpa [g] using this
  have hs : Function.support (GlobalTheory.RSCell.locFac q α x) ⊆ Set.range g := by
    intro ν hν
    rw [Function.mem_support] at hν
    unfold GlobalTheory.RSCell.locFac at hν
    split_ifs at hν with h
    · refine ⟨⟨fun i => (ν i).toNat, fun i j hij => Int.toNat_le_toNat (h.1 hij)⟩, ?_⟩
      funext i
      simp [g, Int.toNat_of_nonneg (h.2 i)]
    · exact absurd rfl hν
  rw [← hg.tsum_eq hs, GlobalTheory.RSPole.schurDir]
  refine tsum_congr fun l => ?_
  have hA : Antitone (g l) ∧ ∀ i, 0 ≤ g l i :=
    ⟨fun i j hij => by simpa [g] using l.2 hij, fun i => by simp [g]⟩
  rw [GlobalTheory.RSCell.locFac, if_pos hA]
  simp [g]

theorem tsum_cellProd_sub_eq_eulD (E : Type) [Field E] [NumberField E] (n : ℕ)
    (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ) (l₀ : GlobalTheory.CellDec.abelian₂ E n T) :
    ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) α x := by
  let sh : GlobalTheory.CellDec.abelian₂ E n T ≃ GlobalTheory.CellDec.abelian₂ E n T :=
    { toFun := fun l => ⟨l.1 - l₀.1, fun v hv => by simp [l.2 v hv, l₀.2 v hv]⟩
      invFun := fun l => ⟨l.1 + l₀.1, fun v hv => by simp [l.2 v hv, l₀.2 v hv]⟩
      left_inv := fun l => Subtype.ext (by simp)
      right_inv := fun l => Subtype.ext (by simp) }
  have h1 : ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x l.1 :=
    sh.tsum_eq (fun l => GlobalTheory.RSCell.cellProd T α x l.1)
  rw [h1]
  have hsupp : ∀ l : GlobalTheory.CellDec.abelian₂ E n T, ∀ w ∈ l.1.support, w ∉ T := fun l w hw hT =>
    (Finsupp.mem_support_iff.1 hw) (l.2 w hT)
  let e : GlobalTheory.CellDec.abelian₂ E n T ≃ ({w : HeightOneSpectrum (𝓞 E) // w ∉ T} →₀ (Fin n → ℤ)) :=
    { toFun := fun l => l.1.subtypeDomain (fun w => w ∉ T)
      invFun := fun ν => ⟨ν.extendDomain, fun v hv => by simp [Finsupp.extendDomain_apply, hv]⟩
      left_inv := fun l => Subtype.ext (Finsupp.extendDomain_subtypeDomain l.1 (hsupp l))
      right_inv := fun ν => Finsupp.subtypeDomain_extendDomain ν }
  let f : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → (Fin n → ℤ) → ℝ≥0∞ :=
    fun w ν => GlobalTheory.RSCell.locFac (Ideal.absNorm w.1.asIdeal) (α w) x ν
  have hf0 : ∀ w, f w 0 = 1 := fun w => GlobalTheory.RSCell.locFac_zero _ _ _
  let h : HeightOneSpectrum (𝓞 E) → (Fin n → ℤ) → ℝ≥0∞ := fun w ν =>
    if hw : w ∈ T then 1 else GlobalTheory.RSCell.locFac (Ideal.absNorm w.asIdeal) (α ⟨w, hw⟩) x ν
  have h2 : ∀ l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x l.1 = (e l).prod f := by
    intro l
    have : (e l).prod f = (l.1.subtypeDomain (fun w => w ∉ T)).prod (fun a b => h a.1 b) := by
      refine Finset.prod_congr rfl fun a _ => ?_
      simp only [h, dif_neg a.2, f]
      rfl
    rw [this, Finsupp.prod_subtypeDomain_index (hsupp l)]
    rfl
  rw [tsum_congr h2, e.tsum_eq (fun ν => ν.prod f),
    (GlobalTheory.EulerSum.euler_product_intVec_ennreal n f hf0).2, GlobalTheory.RSPole.eulD]
  refine tprod_congr fun w => ?_
  rw [schurDir_eq_tsum_locFac]

end GlobalTheory.RSCellSum
end
end

