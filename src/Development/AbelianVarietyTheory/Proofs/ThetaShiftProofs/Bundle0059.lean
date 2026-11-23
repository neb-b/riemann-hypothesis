module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldNormalisedDegenerationData
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0208
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcInOverValuationRing
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem isPolFibre_prj {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'}
    {D₀ : Out.DegPre R} {D₁ : Out.DegPre R'} (p : Out.IsPullDeg f D₀ D₁) : IsPolFibre f D₀.P D₁.P (prj p) :=
  ⟨H1.dim_unique _ D₁.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec D₁.P.A (Classical.arbitrary (PrimeSpectrum R'))), pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem exists_arcIn_over_valuationRing : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (ρ : 𝓞 K₁ →+* Tv.V) (O : Type) [CommRing O] (β : O →+* c.F) (b : O →+* Tv.V), (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → (∀ x, algebraMap Tv.V Tv.Fr (b x) = io (algebraMap c.F K₁ (β x))) → ∃ (aw : ArcIn Dw l β Tv.V b) (aK : ArcIn Dw l (RingHom.id c.F) Tv.Fr (io.comp (algebraMap c.F K₁))) (pw : Out.IsPullDeg (algebraMap Tv.V Tv.Fr) aw.D₀ aK.D₀) (pK : Out.IsPullDeg io a.D₀ aK.D₀) (ψ : aw.D₀.P.A.left ⟶ s.B.A.left), InBC (algebraMap Tv.V Tv.Fr) aw (aK.restrict β) pw ∧ InBC io a aK pK ∧ IsPolFibre ρ s.B aw.D₀.P ψ ∧ prj pw ≫ ψ = prj pK ≫ s.φB ∧ TauCan aw.D₀ n' := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s Tv io ρ O _ β b hρ hb
  letI := H.starRing
  obtain ⟨aK, pK, hBC, -⟩ := GlobalTheory.ArcPull.exists_isBC hK.laws.polBaseChange hK.laws.globalFns a io io.injective
  have hB : IsPolFibre (algebraMap (𝓞 K₁) K₁) s.B a.D₀.P s.φB :=
    (isFibreOf_iff_isPolFibre _ _ _ s.B s.toCMPart.xB s.φB).1 s.good.2.2.2.1
  obtain ⟨Pv, ψ, hψ⟩ := exists_isPolFibre hK.laws.polBaseChange ρ s.B
  have hcomp : io.comp (algebraMap (𝓞 K₁) K₁) = (algebraMap Tv.V Tv.Fr).comp ρ :=
    RingHom.ext fun x => (hρ x).symm
  have hχ : IsPolFibre ((algebraMap Tv.V Tv.Fr).comp ρ) s.B aK.D₀.P (prj pK ≫ s.φB) :=
    hcomp ▸ GlobalTheory.CM.EllComp.isPolFibre_comp hB (isPolFibre_prj pK)
  obtain ⟨φ, hφψ, hφ⟩ := GlobalTheory.CM.EllComp.exists_isPolFibre_lift hψ hχ
  obtain ⟨DV, p, rfl, hp, hq⟩ := _root_.GlobalTheory.DvrDeg.exists_extension hK Tv.V Tv.Fr Pv aK.D₀ φ hφ
  obtain rfl : prj p = φ := eq_of_heq hp
  obtain ⟨oB, hoB⟩ := polOActPull _ _ _ s.B DV.P ψ hψ.2.1 hψ.2.2 (𝓞 E) s.oa
  have htau : TauCan aK.D₀ n' :=
    (_root_.GlobalTheory.TauCanPull.tauCan_iff_of_isPullDeg hK K₁ Tv.Fr io a.D₀ aK.D₀ pK n' io.injective a.bimult aK.bimult).1 s.tau
  have hact : ∀ x, (aK.oa.onB.act x).left ≫ prj p = prj p ≫ (oB.act x).left := fun x => by
    have h₁ : (aK.oa.onB.act x).left ≫ prj pK = prj pK ≫ (a.oa.onB.act x).left := hBC.act x
    have w := hφ.2.1.1.w
    generalize prj p = u at hφψ w ⊢
    generalize prj pK = u' at hφψ h₁
    refine hψ.2.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hoB, reassoc_of% hφψ, hφψ, reassoc_of% h₁, s.act]
    · rw [Category.assoc, Category.assoc, Over.w, w, ← Category.assoc, Over.w]
  obtain ⟨aw, pw, rfl, hpw, hin, ht⟩ := GlobalTheory.T.arcData_descends_principalIdealSubring hK E H Dw l c O β Tv.V Tv.Fr (algebraMap Tv.V Tv.Fr) b
    ((io.comp (algebraMap c.F K₁)).comp β) (aK.restrict β) DV p n' oB (IsFractionRing.injective _ _)
    (RingHom.ext fun x => (hb x).symm) s.n_pos htau hact (fun v => hq _ _ aK.bimult) (fun v => hq _ _ aK.bimult)
  obtain rfl : pw = p := eq_of_heq hpw
  exact ⟨aw, aK, pw, pK, ψ, hin, (inBC_iff_isBC io a aK pK).2 hBC, hψ, hφψ, ht⟩

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataDescentNumberField
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem DescNum.isPolFibre_of_isPullDeg {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'}
    {D : Out.DegPre R} {D' : Out.DegPre R'} (p : Out.IsPullDeg f D D') : IsPolFibre f D.P D'.P (prj p) :=
  ⟨H1.dim_unique _ D'.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D.P.smoothDim)
    (eSec D'.P.A (Classical.arbitrary (PrimeSpectrum R'))), pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem DescNum.epi_of_isPullback_field {K K' : Type} [Field K] [Field K'] (f : K →+* K') {X X' : Scheme.{0}} {φ : X' ⟶ X}
    {s' : X' ⟶ Sp K'} {s : X ⟶ Sp K} (h : IsPullback φ s' s (spMap f)) : Epi φ := by
  letI := f.toAlgebra
  haveI h₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat K K')
  haveI h₂ : Surjective (spMap f) := ⟨fun p => ⟨(⊥ : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  haveI : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip h₁
  haveI : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip h₂
  exact Flat.epi_of_flat_of_surjective φ

theorem exists_arcIn_numberField : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (σ₁ : K →+* ℂ) (σ : c.F →+* ℂ) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left) (n : ℕ), letI := H.starRing; σ₁.comp (algebraMap c.F K) = σ → 0 < n → IsPolFibre (σ₁.comp (algebraMap (𝓞 K) K)) B.pol aC.D₀.P φ → (∀ x, (aC.oa.onB.act x).left ≫ φ = φ ≫ (B.t.act.act x).left) → TauCan aC.D₀ n → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (_ : Algebra c.F K₂) (i : K →ₐ[c.F] K₂) (σ₂ : K₂ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₂ (algebraMap c.F K₂)) (p : Out.IsPullDeg σ₂ a.D₀ aC.D₀) (ψ : a.D₀.P.A.left ⟶ B.pol.A.left), σ₂.comp (i : K →+* K₂) = σ₁ ∧ InBC σ₂ a aC p ∧ TauCan a.D₀ n ∧ IsPolFibre ((i : K →+* K₂).comp (algebraMap (𝓞 K) K)) B.pol a.D₀.P ψ ∧ ∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left := by
  intro hK E _ _ _ H Dw l c K _ _ _ σ₁ σ B aC φ n hσ hn hφ hact htau
  letI := H.starRing
  obtain ⟨oa, hoa, -⟩ := GlobalTheory.LamF.exists_oAct_rosatiConj hK.laws E H (fun _ => rfl) K B
  obtain ⟨P, φP, hP⟩ := exists_isPolFibre hK.laws.polBaseChange (algebraMap (𝓞 K) K) B.pol
  obtain ⟨φ₁, hφ₁, e₁⟩ := PolFibre.cancel hP hφ
  obtain ⟨K₂, _, _, i₂, σ₂, D₂, p₂, ψ₂, hi₂, hψ₂, e₂⟩ :=
    _root_.GlobalTheory.NormDescent.exists_numberField_pre hK K σ₁ P aC.D₀ φ₁ n hn hφ₁ aC.even aC.bimult htau
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨K₃, _, _, i₃, σ₃, D₃, q, p₃, hi₃, e₃, hQ⟩ :=
    _root_.GlobalTheory.QkNumberField.exists_numberField_qk hK K₂ σ₂ D₂ aC.D₀ p₂ n l.M' hn hM aC.bimult htau.1
  have hψ : IsPolFibre ((i₃.comp i₂).comp (algebraMap (𝓞 K) K)) B.pol D₃.P ((prj q ≫ ψ₂) ≫ φP) :=
    PolFibre.comp hP (PolFibre.comp hψ₂ (DescNum.isPolFibre_of_isPullDeg q))
  have eψ : prj p₃ ≫ (prj q ≫ ψ₂) ≫ φP = φ := by
    rw [← e₁, ← e₂, ← e₃]; simp only [Category.assoc]
  generalize (prj q ≫ ψ₂) ≫ φP = ψ at hψ eψ
  obtain ⟨oB, hoB⟩ := polOActPull _ _ _ B.pol D₃.P ψ hψ.2.1 hψ.2.2 (𝓞 E) oa
  letI : Algebra c.F K₃ := ((i₃.comp i₂).comp (algebraMap c.F K)).toAlgebra
  let i : K →ₐ[c.F] K₃ := { i₃.comp i₂ with commutes' := fun _ => rfl }
  have hσ₃ : σ₃.comp (i₃.comp i₂) = σ₁ := by rw [← RingHom.comp_assoc, hi₃, hi₂]
  have hb : σ = σ₃.comp (algebraMap c.F K₃) := by rw [← hσ, ← hσ₃]; rfl
  have hp₃ := (pull_grp p₃).1
  have hcomm : ∀ x, (aC.oa.onB.act x).left ≫ prj p₃ = prj p₃ ≫ (oB.act x).left := fun x => by
    have w : prj p₃ ≫ D₃.P.A.hom = aC.D₀.P.A.hom ≫ spMap σ₃ := hp₃.w
    generalize prj p₃ = π at eψ w
    refine hψ.2.1.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, eψ, hoB, ← Category.assoc, eψ, hact, hoa]
    · rw [Category.assoc, Category.assoc, Over.w, w, ← Category.assoc, Over.w]
  obtain ⟨a, p', ha, hp', hbc, hta⟩ := GlobalTheory.T.arcData_descends_principalIdealSubring hK E H Dw l c c.F (RingHom.id c.F) K₃ ℂ σ₃ (algebraMap c.F K₃) σ
    aC D₃ p₃ n oB σ₃.injective hb hn htau hcomm (fun v => hQ _ (Nat.dvd_lcm_left _ _) _)
    (fun v => hQ _ (Nat.dvd_lcm_right _ _) _)
  subst ha
  obtain rfl := eq_of_heq hp'
  refine ⟨K₃, inferInstance, inferInstance, inferInstance, i, σ₃, a, p', ψ, hσ₃, hbc, hta, hψ, fun x => ?_⟩
  have hepi : Epi (prj p') := DescNum.epi_of_isPullback_field σ₃ hp₃
  have h := hbc.2.2.2.1 x
  generalize prj p' = π at eψ h hepi
  rw [← cancel_epi π, ← Category.assoc, ← h, Category.assoc, eψ, ← Category.assoc, eψ, hact]

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmObjOfPeriod
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.PeriodObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D D' : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)}

theorem mem_lat_iff (hP : IsPeriod D ty P) (ρ : ℂ) (a : D.La) :
    a ∈ PureType.lat hP ρ ↔ P (H.rt • a) = ρ • P a := by
  refine ⟨fun h => funext fun j => ?_, fun h j hj => ?_⟩
  · rw [hP.1, Pi.smul_apply, smul_eq_mul]
    by_cases hj : ty j (H.rt : E) = ρ
    · rw [hj]
    · rw [h j hj, mul_zero, mul_zero]
  · have := congrFun h j
    rw [hP.1, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_mul_right_iff.1 this).resolve_left hj

theorem exists_lat_move (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (gam : D.La ≃ₗ[𝓞 E] D'.La)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {p q : ℕ} (Z : GlobalTheory.CM.CMLat hP p q) :
    ∃ Z' : GlobalTheory.CM.CMLat hP' p q, Z'.hh = Z.hh :=
  ⟨{ D₁ := Z.D₁
     sigP := Z.sigP
     sigM := Z.sigM
     f := fun j => gam.toLinearMap ∘ₗ Z.f j
     pure := fun j a => by
       refine (mem_lat_iff hP' _ _).2 ?_
       show P' (H.rt • gam (Z.f j a)) = _ • P' (gam (Z.f j a))
       rw [← map_smul, hh, hh, (mem_lat_iff hP _ _).1 (Z.pure j a), map_smul]
     hh := Z.hh
     form := fun j a b => (hE _ _).trans (Z.form j a b)
     span := by
       obtain ⟨n, hn, hs⟩ := Z.span
       refine ⟨n, hn, fun a => ?_⟩
       obtain ⟨x, hx⟩ := hs (gam.symm a)
       refine ⟨x, ?_⟩
       have := congrArg gam hx
       set_option synthInstance.maxHeartbeats 100000 in
         rw [map_nsmul, gam.apply_symm_apply, map_sum] at this
       exact this }, rfl⟩

theorem isExp_move {R : Type} [CommRing R] {T : GlobalTheory.CM.PAT H (Sp R)} {σ : R →+* ℂ} (hP : IsPeriod D ty P)
    (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hE : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    (hh : ∀ a, P' (gam a) = h (P a)) {e : (Fin g → ℂ) → (Over.mk (spMap σ) ⟶ T.t.G)}
    (he : GlobalTheory.CM.IsExp T σ D' ty P' e) : GlobalTheory.CM.IsExp T σ D ty P fun z => e (h z) := by
  obtain ⟨hP', hol, add, onto, ker, lin, weil⟩ := he
  have hd : Differentiable ℂ h := h.toContinuousLinearEquiv.differentiable
  refine ⟨hP, fun U f => ⟨?_, ?_⟩, fun z w => ?_, onto.comp h.surjective, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · exact (hol U f).1.preimage hd.continuous
  · exact (hol U f).2.comp hd.differentiableOn fun z hz => hz
  · beta_reduce
    rw [map_add (f := _), add]
  · refine (ker _).trans ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩
      exact ⟨gam.symm a, h.injective (by rw [← hh, gam.apply_symm_apply, ha])⟩
    · rintro ⟨a, rfl⟩
      exact ⟨gam a, hh a⟩
  · let m : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have hm : ∀ z, m z = fun k => ty k (a : E) * z k := fun _ => rfl
    have hc : h.toLinearMap.restrictScalars ℝ ∘ₗ m = m ∘ₗ h.toLinearMap.restrictScalars ℝ :=
      LinearMap.ext_on_range hP.2.2.2.1 fun x => by
        show h (m (P x)) = m (h (P x))
        rw [← hh, hm, hm, ← funext (hP.1 a x), ← funext (hP'.1 a (gam x)), ← hh, map_smul]
    have hz : h (m z) = m (h z) := LinearMap.congr_fun hc z
    show e (h (m z)) = _
    rw [hz, hm, lin]
  · beta_reduce
    rw [map_smul, map_smul, ← hh, ← hh]
    exact weil k _ _ c hk (by rw [hE]; exact hc)

end GlobalTheory.ArcCM.PeriodObj

namespace GlobalTheory.ArcCM

theorem exists_cmObj_of_period : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)) (hP : IsPeriod DB ty PB) (Z : GlobalTheory.CM.CMLat hP DB.p DB.q), 1 ≤ DB.p + DB.q → IsTypeFn H DB.p DB.q ty → l.A = 1 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (σ₁ : K →+* ℂ) (ρ : 𝓞 K) (X : GlobalTheory.CM.CMObj H K ρ σ₁ DB.p DB.q) (ex : (Fin g → ℂ) → (Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G)), σ₁.comp (algebraMap c.F K) = c.F.val.toRingHom ∧ σ₁ (ρ : K) = H.rt0 ∧ X.hh = Z.hh ∧ GlobalTheory.CM.IsExp X.B (σ₁.comp (algebraMap (𝓞 K) K)) DB ty PB ex := by
  intro kn E _ _ _ H l c DB g ty PB hP Z hpq hty hA
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  obtain ⟨FU⟩ := kn.n1c E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, he⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq
    rfl hty DB LinearMap.id PB ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨i, P', hP', hy⟩ := FU.onto y he.1
  obtain ⟨gam, h, hE, -, -, hh⟩ := (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed kn.theta kn.laws E H DB l Xo
    (algebraMap (KA l) ℂ) g ty hpq rfl hty DB (FU.Di i) LinearMap.id (FU.t i) PB P' y (FU.u i P') e (FU.ex i P') he
    ⟨FU.over_σ i P' hP', hP', ⟨FU.ex_add i P' hP', FU.ex_onto i P' hP', ExpUniqFamily.isHolTo_ex FU i P' hP',
      (FU.ex_diff i P' hP').1, (FU.ex_diff i P' hP').2⟩, FU.ex_ker i P' hP', FU.ex_lin i P' hP', FU.ex_weil i P' hP',
      FU.ex_eta i P' hP', FU.ex_etaA i P' hP'⟩).1 hy.symm
  obtain ⟨Z', hZ'⟩ := PeriodObj.exists_lat_move hP hP' gam h hE hh Z
  obtain ⟨K, _, hk, ρ, X, y₀, t₀, m, m', gA, tyA, PA, eA, F, hle, hρ, hX, -, hy₀, -⟩ :=
    kn.cm E H DB l Xo g ty FU i P' hP' Z' c.F c.fin
  obtain ⟨eB, heB, -⟩ := GlobalTheory.CM.ExCompare.exists_isExp_of_family FU i hP' (algebraMap (𝓞 K) K) (algebraMap K ℂ)
    X.B m m' hy₀
  exact ⟨K, inferInstance, inferInstance, (IntermediateField.inclusion hle).toRingHom.toAlgebra, algebraMap K ℂ, ρ, X,
    fun z => eB (h z), RingHom.ext fun _ => rfl, hρ, hX.trans hZ', PeriodObj.isExp_move hP gam h hE hh heB⟩

end GlobalTheory.ArcCM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFrBor
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix

namespace GlobalTheory.ValNorm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_idx (hσ : GoodEmb c σ) (X : Data E r) (hr : r = Dw.p + Dw.q) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r, (∀ j,
      (X.p0 ≤ ((idx j).2 : ℕ) ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = X.p0 + (e j).2) ∨
      (((idx j).2 : ℕ) < X.p0 ∧ conjEmb (idx j).1.1 = relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = X.p0 - 1 - (e j).2 ∧ ((e j).2 : ℕ) < X.p0)) ∧
      ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
        if ((idx j).2 : ℕ) < X.p0 then
          hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  refine ⟨idx, fun j => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · exact Or.inl ⟨by omega, b, c'⟩
    · exact Or.inr ⟨by omega, by rw [b]; exact hcc _, c', d⟩
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dite_eq_left hn]
      rfl

theorem exists_move (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (x b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) :
    ∃ h₀ : Matrix (Fin g) (Fin g) ℂ,
      (∀ v : Fin r → E, (fun j => perFr (U.X k) (rmul x b) v (relab c σ (e j).1) (e j).2) =
        h₀ *ᵥ fun j => perFr (U.X k) x v (relab c σ (e j).1) (e j).2) ∧
      (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
        ∏ j, h₀⁻¹ j j ^ (a ((e j).1, (e j).2) + n / 2) = bchar (laU U a n k) b := by
  obtain ⟨idx, hi, hper⟩ := exists_idx hσ (U.X k) hr hp0 hty e
  obtain ⟨hbij, -, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ j j', PerBor.moveMat (U.X k).p0 idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega)] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
      · omega
    · rw [if_pos a1] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · omega
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
  have hdet := PerBor.det_of_support _ _ hinj _ hs
  have hdiag := PerBor.moveMat_diag (U.X k).p0 idx hb
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat (U.X k).p0 idx b).det := by
    rw [hdet, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  refine ⟨PerBor.moveMat (U.X k).p0 idx b, fun v => ?_, PerBor.inv_support _ _ _ hu hs, fun a n => ?_⟩
  · exact PerBor.moveMat_mulVec _ idx hb (U.X k).Gm x v _ _ (fun j => hper _ _ j) (fun j => hper _ _ j)
  · unfold bchar
    refine Eq.trans ?_ (Fintype.prod_prod_type'
      (fun (τ : (U.X k).Ψ) (i : Fin r) => b τ i i ^ laU U a n k τ i))
    rw [← idx.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [PerBor.inv_diag _ _ hinj _ hu hs, hdiag]
    have hinv := Function.leftInverse_invFun hbij.1 (e j).1
    unfold laU
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega), if_pos a1, b1, hinv,
        show ((idx j).2 : ℕ) - (U.X k).p0 = (e j).2 by omega, inv_inv, ← zpow_natCast]
      congr 1
    · rw [if_pos a1, if_neg (by omega), b1, hinv,
        show (U.X k).p0 - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring

theorem exists_frBor (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0)
    (x : (U.X k).dom) (b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) (h : rmul x.1 b ∈ (U.X k).dom) :
    ∃ (t : Ix Dw → (CAt σ)ˣ) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)),
      FrBor t (U.un k x) (U.un k ⟨_, h⟩) ∧ FrChg G (t none : CAt σ) (U.un k x) (U.un k ⟨_, h⟩) ∧
      ∀ a n, toC (wchar (ex Dw a n) t) * bchar (laU U 0 n k) b =
        toC (t none : CAt σ) ^ n * bchar (laU U a n k) b := by
  obtain ⟨h₀, hP, htri, hw⟩ := exists_move hσ U k hr hp0 hty Uw.e x.1 b hb
  have hp := Uw.period k x
  have hp' := Uw.period k ⟨_, h⟩
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ _ _ Uw.F (Uw.ik k)
    (Uw.Pm k x) (Uw.Pm k ⟨_, h⟩) (LinearEquiv.refl _ _) h₀ hp hp' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
    (fun a => ⟨0, by simp⟩) (fun a => by
      have e1 : Uw.Pm k x a = _ := funext (Uw.Pm_eq k x a)
      have e2 : Uw.Pm k ⟨_, h⟩ a = _ := funext (Uw.Pm_eq k ⟨_, h⟩ a)
      rw [LinearEquiv.refl_apply, e1, e2]
      exact hP _)
  obtain ⟨hy1, hy2⟩ := Uw.lie k x
  obtain ⟨hy1', hy2'⟩ := Uw.lie k ⟨_, h⟩
  have hxx : (U.un k ⟨_, h⟩).x = (U.un k x).x := hy1'.trans (hu.symm.trans hy1.symm)
  have hder : ∀ τ i, IsDerivAt0 (fun z => (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left)
      (h₀⁻¹ *ᵥ Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ((U.un k ⟨_, h⟩).u τ i) := by
    intro τ i
    refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) hp (Uw.ik k)
      (Uw.Pm k ⟨_, h⟩) (Matrix.mulVecLin h₀) hp' hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy2' τ i
  obtain ⟨G, t₀, -, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) _ _).1 hxx
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := GlobalTheory.NormUnBor.diag_ne_zero Uw.e h₀⁻¹ hinv htri
  let d : Fin Uw.g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (Uw.e.symm p))
  refine ⟨t, G, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (Uw.e.symm ⟨τ, i'⟩) (Uw.e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩,
    hG, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [Uw.e.apply_symm_apply, Uw.e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F _ _ hp _ _ _ (hy2 τ) _ _).2 ?_
    rw [GlobalTheory.NormUnBor.col_eq_sum Uw.e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hG.2.2
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n
    rw [← hw a n, ← hw 0 n]
    show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) * _ = _
    rw [Fintype.prod_option, mul_assoc]
    congr 1
    rw [← Equiv.prod_comp Uw.e, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (Uw.e.symm (Uw.e j)) (Uw.e.symm (Uw.e j)) ^ a ((Uw.e j).1, (Uw.e j).2) * _ = _
    rw [Uw.e.symm_apply_apply, ← pow_add, Pi.zero_apply, zero_add]

theorem exists_unit (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ ∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1 := by
  obtain ⟨_, b, hb, hg, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  refine ⟨b, hb, ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun τ i => ?_⟩
  unfold dmin lminor
  rw [hg, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

end GlobalTheory.ValNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LamDegreeParameters
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem GlobalTheory.ArcCM.lamDegSt_logOm₂ : Known → ∀ (D : D7) (T : Core D) (large₂ : SizeData₂ D), T.Q.Pins → GlobalTheory.LamF.LamDegSt T.Q.H large₂.logOm :=
  fun _ D T large₂ h => (GlobalTheory.LamF.lambdaBundle_conditions_iff.1 _ _ _).2 (GlobalTheory.LamF.lam_ind_len_deg.2.2 D T.Q h.1 large₂)
end

