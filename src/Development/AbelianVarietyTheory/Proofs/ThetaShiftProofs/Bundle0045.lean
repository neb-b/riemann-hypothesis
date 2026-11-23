module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0041
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.LinOfPoly
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegree
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.ArcCM.cfOf_linear_and_degree : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∃ φ : sec Xo c a' n →ₗ[c.F] K₁, ∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ ∀ F ∈ sec Xo c a' n, cfOf d.yF d.μ d.jj F ≠ 0 → ∑ v, d.μ v = absA Dw a' := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ d a' n
  have hP : ∀ F ∈ sec Xo c a' n, ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁),
      algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (absA Dw a') := fun F hF =>
    GlobalTheory.ArcQ.evR_arc_isHomogeneous hK.laws hK.laws2 E H Dw l Xo c (hK.ev E H Dw l Xo c) K₁ d a' n F hF
  have hcomp : ∀ a : c.F, algebraMap c.F (ArcS Dw K₁) a =
      algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)
        (algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a) := fun _ => rfl
  have hnum : ∀ F : sec Xo c a' n,
      algebraMap _ (ArcS Dw K₁) (arcNum (evR Xo c F.1 d.yF)) = evR Xo c F.1 d.yF := fun F =>
    (hP F.1 F.2).elim fun P hP' => by
      rw [← hP'.1, LinOfPoly.arcNum_map]
  have hadd : ∀ F G : sec Xo c a' n, arcNum (evR Xo c (F + G).1 d.yF) =
      arcNum (evR Xo c F.1 d.yF) + arcNum (evR Xo c G.1 d.yF) := fun F G =>
    LinOfPoly.inj _ K₁ (by
      rw [map_add (f := _), hnum, hnum, hnum, Submodule.coe_add, LinOfPoly.evR_add])
  have hsmul : ∀ (a : c.F) (F : sec Xo c a' n), arcNum (evR Xo c (a • F).1 d.yF) =
      algebraMap c.F (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) a *
        arcNum (evR Xo c F.1 d.yF) := fun a F =>
    LinOfPoly.inj _ K₁ (by
      rw [hnum, Submodule.coe_smul, LinOfPoly.evR_smul, map_mul, hnum F, hcomp])
  refine ⟨⟨{ toFun := fun F => cfOf d.yF d.μ d.jj F.1, map_add' := ?_, map_smul' := ?_ }, fun F => rfl⟩, ?_⟩
  · intro F G
    simp only [cfOf]
    rw [hadd, MvPolynomial.coeff_add, HahnSeries.coeff_add]
  · intro a F
    simp only [cfOf]
    rw [hsmul, MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C_mul, LinOfPoly.laur_alg,
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, RingHom.id_apply]
    simp [Algebra.smul_def]
  · intro F hF hne
    obtain ⟨P, hP1, hP2⟩ := hP F hF
    rw [← Finsupp.degree_eq_sum]
    by_contra hd
    apply hne
    simp only [cfOf]
    rw [← hP1, LinOfPoly.arcNum_map, hP2.coeff_eq_zero hd]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcRigidityTwoModelsOfMono
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem arc_rigidity_two_models_of_mono : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y = y' ∧ (Mono Y.j → ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ) :=
  rigidArc_of_mono

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcSectionValueAtSpecialisedPointsThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcSection_value_at_specialised_points_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), AnFin Λ.A → ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → θ ≠ 0 → Λ.u.IsFn th θ → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → ⊤ ≤ χ ⁻¹ᵁ U → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ (v : Λ.A.V) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Ψ.pi w v).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (rw * Λ.A.Sum 1 0 θ w v * Ψ.fr w j₀ v) := by
  first | exact @GlobalTheory.ArcSectionValue.section_value | exact GlobalTheory.ArcSectionValue.section_value | (intros; apply GlobalTheory.ArcSectionValue.section_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfVanishOnInvertibleLetterBlocks
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

namespace GlobalTheory.ArcDense

theorem eq_zero_of_eval_off {σ : Type} (D P : MvPolynomial σ ℂ) (hD : D ≠ 0)
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x D ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have h0 : D * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x D = 0
    · rw [hx, zero_mul]
    · rw [h x hx, mul_zero]
  exact (mul_eq_zero.mp h0).resolve_left hD

noncomputable def coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K)) :
    MvPolynomial σ ℂ :=
  ∑ μ ∈ Q.support, MvPolynomial.monomial μ (ι ((Q.coeff μ).coeff j))

theorem coeff_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (ν : σ →₀ ℕ) : (coefPoly ι j Q).coeff ν = ι ((Q.coeff ν).coeff j) := by
  classical
  rw [coefPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h]; simp

theorem eval_coefPoly {σ K : Type} [Field K] (ι : K →+* ℂ) (j : ℤ) (Q : MvPolynomial σ (LaurentSeries K))
    (x : σ → ℂ) : MvPolynomial.eval x (coefPoly ι j Q) =
      ∑ μ ∈ Q.support, ι ((Q.coeff μ).coeff j) * ∏ v ∈ μ.support, x v ^ μ v := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coefPoly, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  rfl

theorem coeff_eq_zero_of_vanish_on_invBl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c), (∀ x : ArcLt Dw → ℂ, GlobalTheory.ArcQ.InvBl x → ∑ i, a i * ajAt d ι (F i) x = 0) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro E _ _ _ H Dw l Xo c K₁ _ _ d ι m a F h μ
  classical
  let D : MvPolynomial (ArcLt Dw) ℂ :=
    ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (MvPolynomial.X ⟨τ, (i, k)⟩ : MvPolynomial (ArcLt Dw) ℂ)).det
  have hDe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x D =
      ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩).det := by
    intro x
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    simp
  have hD : D ≠ 0 := by
    intro h0
    have h1 := hDe (fun v => if v.2.1 = v.2.2 then 1 else 0)
    rw [h0, map_zero] at h1
    have h2 : ∀ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)).det = 1 := by
      intro τ
      have : (Matrix.of fun i k : Fin (Dw.mult τ) => (if i = k then (1 : ℂ) else 0)) = 1 := by
        ext i k
        simp [Matrix.one_apply]
      rw [this, Matrix.det_one]
    simp only [h2, Finset.prod_const_one] at h1
    exact zero_ne_one h1
  let P : MvPolynomial (ArcLt Dw) ℂ :=
    ∑ i, MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))
  have hP : P = 0 := by
    refine eq_zero_of_eval_off D P hD fun x hx => ?_
    rw [hDe] at hx
    have hx' : InvBl x := fun τ => (Finset.prod_ne_zero_iff.mp hx) τ (Finset.mem_univ τ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h x hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, eval_coefPoly]
    rfl
  have := congrArg (AddMonoidAlgebra.coeff · μ) hP
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at this
  change (∑ i, (MvPolynomial.C (a i) * coefPoly ι d.jj (arcNum (evR Xo c (F i) d.yF))).coeff μ) = 0 at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.coeff_C_mul, coeff_coefPoly]
  rfl

end GlobalTheory.ArcDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
  first | exact @GlobalTheory.ArcQ.arcBasis_baseChange | exact GlobalTheory.ArcQ.arcBasis_baseChange | (intros; apply GlobalTheory.ArcQ.arcBasis_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DiscrMulXiIntegral
section
noncomputable section

namespace GlobalTheory.XiIntegral

section Tangent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

def origin (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem gtTanR_iff (ν : GtPt D (epsR R)) : GtTanR ν ↔ origin R ≫ ν.b = 1 ∧
    ∀ χ y J, Good D.P.L y J → val (ν.s χ) (origin R).left y J = 1 := by
  constructor
  · rintro ⟨g₀, h₀, h⟩
    obtain ⟨h₁, h₂⟩ := (ConstLie.isZero_iff_zeroAlong (ρ := origin R) h).1 h₀
    refine ⟨h₁, fun χ y J hJ => ?_⟩
    have := h₂ χ _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · rintro ⟨h₁, h₂⟩
    obtain ⟨g₀, h⟩ := ConstLie.exists_isPullGt (origin R) ν
    obtain ⟨b, v⟩ := (TorusModel.isPull_iff _ _ _).1 h
    exact ⟨g₀, ⟨b.trans h₁, fun χ => corr_of_val D.P.isLB fun y J hJ =>
      (v χ y J hJ).trans ((h₂ χ y J hJ).trans (val_one _).symm)⟩, h⟩

theorem gtTanR_of_isZero {ν : GtPt D (epsR R)} (h : ν.IsZero) : GtTanR ν := by
  have hb : ν.b = 1 := h.1
  exact (gtTanR_iff ν).2 ⟨by rw [hb, MonObj.comp_one], fun χ y J hJ => (val_corr hJ (h.2 χ) _).trans (val_one _)⟩

theorem gtTanR_of_scale {a : R} {ν ν' : GtPt D (epsR R)} (h : GtPt.IsPull (spMap (epsScaleR a)) ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  have s : (origin R).left ≫ spMap (epsScaleR a) = (origin R).left :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by simp [epsScaleR]))
  refine (gtTanR_iff ν').2 ⟨Over.OverMorphism.ext ?_, fun χ y J hJ => ?_⟩
  · rw [← h₁, Over.comp_left, Over.comp_left, h.1, ← Category.assoc, s]
  · refine (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_)
    rw [s]
    exact h₂ χ y J hJ

theorem gtTanR_of_isAdd {ν ν' ν'' : GtPt D (epsR R)} (h : ν.IsAdd ν' ν'') (ht : GtTanR ν) (ht' : GtTanR ν') :
    GtTanR ν'' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  obtain ⟨h₁', h₂'⟩ := (gtTanR_iff ν').1 ht'
  have hb : ν''.b = ν.b * ν'.b := h.1
  refine (gtTanR_iff ν'').2 ⟨by rw [hb, MonObj.comp_mul, h₁, h₁', _root_.mul_one], fun χ y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) (origin R).left).trans (val_mul hJ _ _ _))
  have c := val_cub D.cub (origin R) hJ (DegPre.cT D (epsR R) χ) ν.b ν'.b
  have c' := congrArg (fun z => cubV D.cub y J ((origin R) ≫ DegPre.cT D (epsR R) χ)
    ((origin R) ≫ ν.b) z) h₁'
  have cz (x x' : Over.mk (𝟙 (Sp R)) ⟶ D.P.A) : cubV D.cub y J x x' 1 = 1 := by
    have hm : lift x (lift x' 1) = lift x x' ≫ faceMap (G := D.P.A) 2 := by
      simp [faceMap, x2, pzero, Hom.one_def]
    refine Eq.trans ?_ ((val_corr (hJ := hJ) (D.cub.face 2) (lift x x').left).trans (val_one _))
    refine Eq.trans ?_ (val_pull (hJ := hJ) ..).symm
    show val D.cub.t (lift x (lift x' 1)).left y J = _
    rw [hm, Over.comp_left]
    all_goals rfl
  have c := c.trans (c'.trans (cz _ _))
  have e' := (congrArg₂ (· * ·) rfl c).symm.trans (e.trans (congrArg₂ (· * ·) (h₂ χ y J hJ) (h₂' χ y J hJ)))
  simpa using e'

theorem gtTanR_of_gtComb {m : ℕ} {cf : Fin m → R} {e : Fin m → GtPt D (epsR R)} {ν : GtPt D (epsR R)}
    (h : GtComb cf e ν) (he : ∀ i, GtTanR (e i)) : GtTanR ν := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  have : ∀ i, GtTanR (p i) := fun i => Fin.induction (gtTanR_of_isZero h₀)
    (fun j ih => gtTanR_of_isAdd (ha j) ih (gtTanR_of_scale (hu j) (he j))) i
  exact this _

end

end Tangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem exists_intHom {E : Type} [Field E] [NumberField E] [IsCMField E] {K₁ : Type} [Field K₁] [NumberField K₁]
    (τK : E →+* K₁) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X) :
    ∃ φ : X →+ 𝓞 K₁, ∀ x, (φ x : K₁) = ((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x)) := by
  obtain ⟨-, hadd, -, hint, -⟩ := GlobalTheory.ArcQ.pairE_properties E X ξ
  have hi : ∀ x, IsIntegral ℤ (((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x))) := fun x => by
    have h := (hint x).map (τK.comp (IsCMField.complexConj E).toRingEquiv.toRingHom).toIntAlgHom
    simpa [cc] using h
  refine ⟨AddMonoidHom.mk' (fun x => ⟨_, hi x⟩) fun x y => ?_, fun x => rfl⟩
  apply RingOfIntegers.ext
  show _ * τK (cc (pairE ξ (x + y))) = _ * τK (cc (pairE ξ x)) + _ * τK (cc (pairE ξ y))
  rw [hadd]
  simp [cc, mul_add]

theorem discr_mul_xi_integral : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)), s.kind τ k = none → ∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂] ν₁ := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ _ hρ _ _ _ τ k hk
  have hG : Out.GlobalFnsSt := hK.laws.globalFns
  obtain ⟨φ, hφ⟩ := exists_intHom (labK c K₁ τ) s.ξ
  obtain ⟨hb, hd⟩ := s.xi τ k hk
  obtain ⟨hw1, -, hw3⟩ := GlobalTheory.TorusTangent.main hG Tv.V M.aw.D₀
  obtain ⟨-, -, hK3⟩ := GlobalTheory.TorusTangent.main hG K₁ d.a.D₀
  obtain ⟨hF1, hF2, -⟩ := GlobalTheory.TorusTangent.main hG Tv.Fr M.aK.D₀
  obtain ⟨-, hadd, -⟩ := GlobalTheory.ArcQ.pairE_properties E d.a.D₀.X s.ξ
  let φw : M.aw.D₀.X →+ Tv.V :=
    ρ.toAddMonoidHom.comp (φ.comp (M.pK.xe.toAddMonoidHom.comp M.pw.xe.symm.toAddMonoidHom))
  let φ₀ : d.a.D₀.X →+ K₁ := AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE s.ξ x))) fun x y => by
    rw [hadd]; simp [cc]
  let φ₂ : M.aK.D₀.X →+ Tv.Fr := io.toAddMonoidHom.comp (φ₀.comp M.pK.xe.toAddMonoidHom)
  obtain ⟨ν, ⟨hν, hνb, hνd⟩, -⟩ := hw1 φw
  obtain ⟨ν₁, h₁, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pw hG ν
  obtain ⟨e₂, h₂, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pK hG (d.e τ k)
  have t₁ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pw hG h₁ hν
  have t₂ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pK hG h₂ (s.tan τ k)
  obtain ⟨b₁, d₁⟩ := hw3 Tv.Fr M.aK.D₀ _ M.pw φw ν ν₁ hνb hνd h₁
  obtain ⟨b₂, d₂⟩ := hK3 Tv.Fr M.aK.D₀ _ M.pK φ₀ (d.e τ k) e₂ hb hd h₂
  obtain ⟨ν', hν'⟩ := GlobalTheory.ConstLie.exists_gtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂]
  have t₃ : GtTanR ν' := gtTanR_of_gtComb hν' fun i => by fin_cases i; exact t₂
  obtain ⟨b₃, d₃⟩ := hF2 φ₂ _ e₂ ν' t₂ b₂ d₂ hν'
  have key : ∀ x, algebraMap Tv.V Tv.Fr (φw (M.pw.xe x)) = (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂) x := fun x => by
    show algebraMap Tv.V Tv.Fr (ρ (φ (M.pK.xe (M.pw.xe.symm (M.pw.xe x))))) =
      ((NumberField.discr E : ℤ) : Tv.Fr) * io (labK c K₁ τ (cc (pairE s.ξ (M.pK.xe x))))
    rw [AddEquiv.symm_apply_apply, hρ, hφ, map_mul, map_intCast]
  have e : ν₁ = ν' := (hF1 (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂)).unique
    ⟨t₁, b₁, fun x j hj => (d₁ x j hj).trans (congrArg _ (key x))⟩ ⟨t₃, b₃, d₃⟩
  exact ⟨ν, ν₁, e₂, hν, h₁, h₂, e ▸ hν'⟩

end GlobalTheory.XiIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FderivStarStarZero
section
noncomputable section

namespace GlobalTheory.ArchConj

section Diff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt.Arch GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
open GlobalTheory.ArchMetricCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem fderiv_star_star_zero {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (star ∘ F ∘ star) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases hF : DifferentiableAt ℂ F 0
  · have d := hF.hasFDerivAt.star_star
    rw [star_zero] at d
    rw [d.fderiv]
    simp
  · have hG : ¬ DifferentiableAt ℂ (star ∘ F ∘ star) 0 := fun hG => hF (by
      have := hG.star_star
      have e : star ∘ (star ∘ F ∘ star) ∘ star = F := funext fun z => by simp
      rwa [star_zero, e] at this)
    rw [fderiv_zero_of_not_differentiableAt hF, fderiv_zero_of_not_differentiableAt hG]
    simp

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)
variable {X : Scheme.{0}} {L : LB X} {φ : A.left ⟶ X} {g : ℕ} (u : HolUnif A (L.pull φ) g)

theorem cj_isDiff' {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'}
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    (cjUnif h u).IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := fun q _ => by
    have := subsingleton_dual ℂ
    have hq := hU (show q ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rw [e2] at hq
    rw [Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) q (spMap (dualMap (starRingEnd ℂ)) q)]
    exact hq
  have e1 : (fun z => valAt' ((cjUnif h u).ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => cj_val h _ U f
  rw [e1, fderiv_star_star_zero]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg (starRingEnd ℂ) e3

theorem isLieNormAt_conjugate {K : Type} [Field K] {P : Out.PolAV (Sp K)} {σ : K →+* ℂ} {t : epsR K ⟶ P.A} {v : ℝ}
    (H : IsLieNormAt P t σ v) : IsLieNormAt P t (ComplexEmbedding.conjugate σ) v := by
  obtain ⟨P', φ, w, t', h, hw, e, u, Hm, χ, z, hAH, hd, rfl⟩ := H
  have hg := g_eq h
  obtain ⟨A', _, ψ, hc⟩ : ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (ψ : A'.left ⟶ P'.A.left),
      IsGrpPullback A' P'.A cj ψ := ⟨_, _, _, isGrpPullback_pullback P'.A cj⟩
  have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ t'.left) ≫ P'.A.hom = (epsR ℂ).hom ≫ cj := by
    rw [Category.assoc, Over.w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let t'' : epsR ℂ ⟶ A' := Over.homMk (hc.1.lift _ _ sq) (hc.1.lift_snd _ _ _)
  have e' : t''.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left := hc.1.lift_fst _ _ _
  have h' : IsGrpPullback A' P.A (spMap (ComplexEmbedding.conjugate σ)) (ψ ≫ φ) :=
    (hc.comp h).congr (spMap_conjugate σ) rfl
  have e'' : t''.left ≫ ψ ≫ φ = spMap (dualMap (ComplexEmbedding.conjugate σ)) ≫ t.left := by
    rw [← Category.assoc, e', Category.assoc]
    refine (congrArg _ e).trans ?_
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap]
  have hM := pull_isLB P.isLB φ
  have hAH' := cj_isAH hc (carry u P'.isLB hM hw) (carry_isAH _ _ hw hAH)
  have hd' := cj_isDiff' hc (carry u P'.isLB hM hw) e' (w := z) hd
  have hz : (z ⬝ᵥ Hm.mulVec (star z)).re = (star z ⬝ᵥ (Hm.map star).mulVec (star (star z))).re := by
    have := hermSq_star Hm (star z)
    rw [star_star] at this
    exact this.symm
  obtain ⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩ := P
  obtain rfl : P'.g = g := hg
  exact ⟨pullPol _ h', ψ ≫ φ, idIso _, t'', h', idIso_isGen (pull_isLB isLB _), e'',
    cjUnif hc (carry u P'.isLB hM hw), _, _, star z, hAH', hd', by rw [hz]; rfl⟩

end Diff

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem norms_conj : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th ((starRingEnd ℂ).comp σ) v) ∧ ∀ η' : epsR K ⟶ P.A, Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' ((starRingEnd ℂ).comp σ) v :=
  fun _ _ _ P σ v => ⟨fun rig th H => (ArchMetricCompare.isL2Sq_iff_isThNormAt P rig _ th v).1
    (ArchMetricCompare.isL2Sq_conjugate_embedding ((ArchMetricCompare.isL2Sq_iff_isThNormAt P rig σ th v).2 H)),
    fun _ H => isLieNormAt_conjugate H⟩

end GlobalTheory.ArchConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ModelsAtOfGoodLevel
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem modelsAt_of_good_level : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ModelsAt Xo c := by
  intro hK E _ _ _ H Dw l Xo c hr hg
  classical
  have key : ∀ Xs : ∀ l' : Level H, Moduli Dw l', ModelsAt (Xs l) c := by
    intro Xs p W hp hW
    obtain ⟨Y, hY, -⟩ := hK.models.2 E H Dw hr Xs
    obtain ⟨h2, h4⟩ := hY p W hp hW
    exact ⟨Y p W hp hW ⟨l, c, hg p hp⟩, (h4 _).2.2, (h2.1 ⟨l, c, hg p hp⟩).2.2.1⟩
  have h := key (Function.update (fun l' => Classical.choice (hK.n1ab E H Dw l' hr)) l Xo)
  rwa [Function.update_self] at h

end GlobalTheory.ArcCM
end

