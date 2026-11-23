module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.DimPosOfHasType
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CoeffMemOfLoc
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmMetrisedLineLengthsEqSectionLieNorms
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries ComplexOrder

namespace GlobalTheory.ArcCM.NormTie

theorem isThNormAt_of_keyArchAt {K K' : Type} [Field K] [NumberField K] [Field K'] {x : KeyIn K} {T abelian₂ : MLine K}
    {σ : K →+* ℂ} (h : KeyArchAt x T abelian₂ σ) (y : KeyIn K') (τ : K' →+* ℂ)
    (hy : ∀ z : KeyIn ℂ, KeyPB z x σ → KeyPB z y τ) : Arch.IsThNormAt y.P y.rig y.th τ (T.n σ ^ 2) := by
  obtain ⟨z, u, Hm, W, χ, θ, Fd, hpb, hA, hR, hF, -, hD, e, -⟩ := h
  obtain ⟨φ, he, w, hg, F, hφ, hw, h1, h2, -⟩ := hy z hpb
  exact ⟨z.P, z.rig, z.th, φ, he, w, hφ, hw, h1, h2, u, Hm, χ, θ, Fd, hA, hR, hF, hD, e⟩

theorem isLieNormAt_of_isVecLine {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} {i : Fin x.P.g} {ℓ : MLine K} (h : IsVecLine A x φ i ℓ) (σ : K →+* ℂ) :
    Arch.IsLieNormAt x.P (x.v i) σ (Real.log (ℓ.n σ)) := by
  obtain ⟨xs, u, Hm, χ, W, hg, hpb, hA, hW, e⟩ := h.2.2 σ
  obtain ⟨ψ, hg', hψ, hv⟩ := GlobalTheory.KeyFibre.exists_isPolFibre_of_keyPB K ℂ σ x xs hpb
  obtain ⟨w, hw⟩ := LBIso.symm hψ.2.2
  refine ⟨xs.P, ψ, w, _, hψ.2.1, hw, hv (i.cast hg.symm), u, Hm, χ, W, hA, hW, ?_⟩
  rw [← e, Real.log_pow]
  push_cast
  ring

section Pull

variable {K : Type} [Field K] {D₀ : Out.DegPre K} {DC : Out.DegPre ℂ} {σ : K →+* ℂ} (p : Out.IsPullDeg σ D₀ DC)

include p in
theorem g_eq : DC.P.g = D₀.P.g :=
  ReciprocityTheory.ChartRestriction.G.H1.dim_unique DC.P.A.hom DC.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec DC.P.A (default : PrimeSpectrum ℂ))

theorem isPolFibre_prj : IsPolFibre σ D₀.P DC.P (prj p) :=
  ⟨g_eq p, pull_grp p, LBIso.symm ⟨p.w, p.w_gen⟩⟩

theorem exists_keyPB {th : D₀.P.L.Sec} {thC : DC.P.L.Sec} (h : ThBC p th thC) (hg : 1 ≤ D₀.P.g) (hn : ThNZ th)
    (v : Fin D₀.P.g → (epsR K ⟶ D₀.P.A)) (hv : IsLieBasis v) :
    ∃ hg' hn' v' hv', KeyPB ⟨DC.P, hg', DC.rig, DC.rig_gen, thC, hn', v', hv'⟩
      ⟨D₀.P, hg, D₀.rig, D₀.rig_gen, th, hn, v, hv⟩ σ := by
  have e := g_eq p
  have c₁ : IsCommMonObj D₀.P.A := D₀.P.isAb.comm
  have c₂ : IsCommMonObj DC.P.A := DC.P.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange K ℂ σ D₀.P.A DC.P.A (prj p) (pull_grp p)
    D₀.P.isAb.smooth D₀.P.g v hv
  refine ⟨e ▸ hg, GlobalTheory.ArcQBC.thNZ_of_thBC p h hn, fun i => v' (i.cast e), GlobalTheory.KeyTf.isLieBasis_cast e hb',
    prj p, p.he, p.w, e, Chart.dualMapR σ, pull_grp p, p.w_gen, p.w_rig,
    GlobalTheory.KeyPow.appLE_eq_of_stalk _ th thC ((GlobalTheory.ArcQBC.through_iff _ _).1 h), fun a => ?_, ?_, fun i => hv' _⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end Pull

theorem exists_isLieNormAt (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (hv : IsTangent v) :
    ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (z : Fin P.g → ℂ),
      u.IsAH Hm χ ∧ u.IsDiff z v ∧
        Arch.IsLieNormAt P v (RingHom.id ℂ) (Real.log (Real.pi * (hermForm Hm z z).re) / 2) := by
  obtain ⟨rig, hr⟩ := P.rigid
  obtain ⟨u, Hm, χ, -, hA, -, hd, -⟩ := hU P rig hr
  obtain ⟨z, hz, -⟩ := hd v hv
  obtain ⟨h₁, h₂⟩ := GlobalTheory.polFibre_id_comp_cancel.1 ℂ P v
  obtain ⟨w, hw⟩ := LBIso.symm h₁.2.2
  exact ⟨u, Hm, χ, z, hA, hz, P, _, w, v, h₁.2.1, hw, h₂, u, Hm, χ, z, hA, hz, rfl⟩

theorem exists_letter_bound (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E]
    [StarRing (𝓞 E)] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c : Coeff l} (hs : ∀ a : 𝓞 E, star a = H.bar a)
    {nΨ n' f : ℕ} {o : LamObj c nΨ n'} {La : ℝ} (hG : LamObjGood o f La) (L : LamLetters o) (hLg : L.IsGood)
    (σ : o.K₁ →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ o.xB.P.A.left) (hQ : IsPolFibre σ o.xB.P Q ψ)
    (m : Fin o.xB.P.g) (u : epsR o.K₁ ⟶ o.xB.P.A) (uC : epsR ℂ ⟶ Q.A) (hu : L.IsLetter m u)
    (hC : IsVecOver σ ψ u uC) :
    ∃ x, Arch.IsLieNormAt Q uC (RingHom.id ℂ) x ∧ (0 < La → x ≤ Real.log (La * (L.ℓ m).n σ)) := by
  have hB := hG.2.2.2.1
  have hp : IsPolFibre (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB.P o.φB :=
    (isFibreOf_iff_isPolFibre (𝓞 o.K₁) o.K₁ (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB o.φB).1 hB
  obtain ⟨h, Hh⟩ := (GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL o.K₁ o.B
    (GlobalTheory.CM.GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis)).1
  obtain ⟨w, hw1, hw2⟩ := hLg.2.2.1 m
  obtain rfl : u = w := by
    refine Over.OverMorphism.ext (hp.2.1.1.hom_ext ?_ ((Over.w u).trans (Over.w w).symm))
    unfold LamLetters.IsLetter at hu hw1
    cases hq : L.src m with
    | inl q => rw [hq] at hu hw1; exact hu.trans hw1.symm
    | inr q => rw [hq] at hu hw1; exact hu.trans hw1.symm
  have c₁ : IsCommMonObj o.xB.P.A := o.xB.P.isAb.comm
  have ht : IsTangent u := by
    rw [(LieComb.isLieComb_iff_tanExp _ _).1 hw2]
    exact LieComb.isTangent_tanExp o.xB.basis.1 _
  obtain ⟨uu, Hm, χ, z, hA, hz, hN⟩ := exists_isLieNormAt hU Q uC (hC.isTangent hQ.2.1 ht)
  refine ⟨_, hN, fun hLa => ?_⟩
  have e := GlobalTheory.CM.LieMetric.form_eq_pi_mul_hermForm hU hL o.K₁ o.B _ h Hh σ Q ψ uu Hm χ hQ hA
    _ _ _ _ _ _ z z hw2 hw2 hC hC hz hz
  have e' : Real.pi * (hermForm Hm z z).re = (h.form σ (L.U m) (L.U m)).re := by
    rw [e, Complex.re_ofReal_mul]
  have b := (lamLen_of_isHerm hU hL E H l c nΨ n' f o La hG L hLg hp h Hh σ).2 m
  have hd := GlobalTheory.LamF.Ind.lamInd E H l c hs nΨ n' f o La hG L hLg
  have hne : L.U m ≠ 0 := fun h0 => hd (Matrix.det_eq_zero_of_row_eq_zero m (congrFun h0))
  have hpos : 0 < (h.form σ (L.U m) (L.U m)).re := by
    have := (h.posDef σ 1 ![L.U m] (by simpa [linearIndependent_unique_iff] using hne)).diag_pos (i := 0)
    exact (Complex.pos_iff.1 this).1
  rw [e']
  have := Real.log_le_log hpos b
  rw [Real.log_pow] at this
  push_cast at this
  linarith

theorem lengths_eq_norms : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ), letI := H.starRing; Arch.IsThNormAt a.D₀.P a.D₀.rig th em (s.Tl.n em ^ 2) ∧ (∀ i, Arch.IsLieNormAt s.xΨ.P (s.xΨ.v i) em (Real.log ((s.ℓΨ i).n em))) ∧ (∀ i, Arch.IsLieNormAt s.x'.P (s.x'.v i) em (Real.log ((s.ℓ' i).n em))) ∧ ∀ (DC : Out.DegPre ℂ) (p : Out.IsPullDeg em a.D₀ DC), (∀ thC, ThBC p th thC → Arch.IsThNormAt DC.P DC.rig thC (RingHom.id ℂ) (s.Tl.n em ^ 2)) ∧ ∀ m (u : epsR K₁ ⟶ a.D₀.P.A) (uC : epsR ℂ ⟶ DC.P.A), s.L.IsLetter m u → uC.left ≫ prj p = spMap (dualMap em) ≫ u.left → ∃ x, Arch.IsLieNormAt DC.P uC (RingHom.id ℂ) x ∧ (0 < La → x ≤ Real.log (La * (s.L.ℓ m).n em)) := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s em
  letI := H.starRing
  have hG := s.good
  have hA : KeyArchAt s.xB s.Tl s.LamL em := hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 em
  refine ⟨isThNormAt_of_keyArchAt hA s.xB em fun _ h => h,
    fun i => isLieNormAt_of_isVecLine (hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i) em,
    fun i => isLieNormAt_of_isVecLine (hG.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i) em, fun DC p => ⟨fun thC hC => ?_,
    fun m u uC hu hC => ?_⟩⟩
  · obtain ⟨hg', hn', v', hv', h⟩ := exists_keyPB p hC s.g_pos s.th_nz s.v s.basis
    exact isThNormAt_of_keyArchAt hA ⟨DC.P, hg', DC.rig, DC.rig_gen, thC, hn', v', hv'⟩ (RingHom.id ℂ) fun z hz =>
      GlobalTheory.KeyCancel.keyPB_cancel K₁ ℂ ℂ _ _ z em (RingHom.id ℂ) h (by rwa [RingHom.id_comp])
  · exact exists_letter_bound hK.theta hK.laws (fun _ => rfl) hG s.L s.L_good em DC.P (prj p) (isPolFibre_prj p)
      m u uC hu hC

end GlobalTheory.ArcCM.NormTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsScaled
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.Letters

theorem exists_scaled {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} {n : ℕ}
    {sB : ∀ T : Over (Sp R), (T ⟶ D₀.P.A) → Out.GtPt D₀ T} (h : IsSplit D₀ n sB) (r : R) {w : epsR R ⟶ D₀.P.A}
    (hw : IsTangent w) : ∃ ν, GtTanR ν ∧ Out.GtPt.IsPull (spMap (epsScaleR r)) (sB (epsR R) w) ν := by
  let sc : epsR R ⟶ epsR R := Over.homMk (spMap (epsScaleR r)) (by
    show spMap (epsScaleR r) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R))
    rw [spMap_comp_spMap]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])
  let z : Over.mk (𝟙 (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
    rw [spMap_comp_spMap]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact Spec.map_id (CommRingCat.of R))
  have hz : z ≫ sc ≫ w = 1 := by
    apply Over.OverMorphism.ext
    have e : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR r) =
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
      rw [spMap_comp_spMap]
      congr 1
      ext a <;> simp [epsScaleR]
    show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR r) ≫ w.left = _
    rw [← Category.assoc, e, hw]
    exact (Category.id_comp _).symm
  refine ⟨sB _ (sc ≫ w), ⟨sB _ 1, TanPart.isZero_of_isAdd (by simpa using h.2.1 _ 1 1), ?_⟩, h.2.2 _ _ sc w⟩
  have := h.2.2 _ _ z (sc ≫ w)
  rwa [hz] at this

theorem exists_kind {I J : Type} (N m : I → ℕ) (h : ∀ τ, N τ = m τ + 1) (e : (Σ b, Fin (m b)) ≃ J) :
    ∃ kind : ∀ τ, Fin (N τ) → Option J, ∀ τ, Function.Injective (kind τ) ∧ (∃ k, kind τ k = none) ∧
      ∀ j, (∃ k, kind τ k = some j) ↔ (e.symm j).1 = τ := by
  let u : ∀ τ, Fin (N τ) ≃ Option (Fin (m τ)) := fun τ => (finCongr (h τ)).trans (finSuccEquiv _)
  refine ⟨fun τ k => (u τ k).map fun i => e ⟨τ, i⟩, fun τ => ⟨?_, ⟨(u τ).symm none, by simp⟩, fun j => ⟨?_, ?_⟩⟩⟩
  · exact (Option.map_injective (e.injective.comp sigma_mk_injective)).comp (u τ).injective
  · rintro ⟨k, hk⟩
    obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 hk
    simp
  · rintro rfl
    exact ⟨(u _).symm (some (e.symm j).2), by simp⟩

theorem exists_section (hT : Out.SecTwistSt) {K : Type} [Field K] (P : Out.PolAV (Sp K)) :
    ∃ th : P.L.Sec, ∀ s : Sp K, ∃ x : P.A.left, P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT P
  obtain ⟨a, -, hu⟩ := hb b
  refine ⟨b, KeyPow.exists_mem_nonzeroLocus _ b ?_⟩
  by_contra hn
  push Not at hn
  exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)

theorem exists_cmIn : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (ρ : 𝓞 K₁) (σ₁ : K₁ →+* ℂ) (X : GlobalTheory.CM.CMObj H K₁ ρ σ₁ (Dw.p - 1) (Dw.q - 1)) (ψ : a.D₀.P.A.left ⟶ X.B.pol.A.left) (n' : ℕ) (La c₁ : ℝ) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ), letI := H.starRing; 1 ≤ Dw.p → 1 ≤ Dw.q → 3 ≤ Dw.p + Dw.q → σ₁.comp (algebraMap c.F K₁) = c.F.val.toRingHom → σ₁ (ρ : K₁) = H.rt0 → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → IsPolFibre (algebraMap (𝓞 K₁) K₁) X.B.pol a.D₀.P ψ → (∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (X.B.t.act.act x).left) → 0 < n' → TauCan a.D₀ n' → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (s : CMIn a e th jj n' La c₁), s.ξ = ξ ∧ s.ν₀ = ν₀ := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a ρ σ₁ X ψ n' La c₁ ξ ν₀ jj hp hq hpq hσ hρ hLa hψ hact hn hτ hrk hξ hβ htr
  letI := H.starRing
  obtain ⟨th, hth⟩ := exists_section hK.laws2.secTwist a.D₀.P
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis a.D₀.P.A a.D₀.P.smoothDim
  have hf : 0 < Module.finrank ℚ E / 2 := by
    have e := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have gB : X.B.g = Module.finrank ℚ E / 2 * (Dw.p - 1 + (Dw.q - 1)) :=
    (_root_.GlobalTheory.CM.EigDec.eigen_decomposition E H K₁ ρ X.B ⟨a.D₀.P, ψ, hψ, v, hv⟩ _ _ X.split X.typeB X.ρ_sq).2.2.2.1
  have hg : 1 ≤ a.D₀.P.g := by
    rw [hψ.1]
    show 1 ≤ X.B.g
    rw [gB]
    exact Nat.mul_pos hf (by omega)
  have hlab : ∀ τ, τ ∈ psiSet H ↔ labK c K₁ τ (H.rt : E) = (ρ : K₁) := fun τ => by
    have e : σ₁ (labK c K₁ τ (H.rt : E)) = τ (H.rt : E) := RingHom.congr_fun hσ (embF c τ (H.rt : E))
    rw [← σ₁.injective.eq_iff, e, hρ]
    rfl
  let xB : KeyIn K₁ := ⟨a.D₀.P, hg, a.D₀.rig, a.D₀.rig_gen, th, hth, v, hv⟩
  obtain ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩ :=
    exists_lamObjGood_of_cmObj hK.laws2.secTwist hK.theta hK.laws hK.hom E H l c (fun _ => rfl) K₁ ρ σ₁ _ _ X La hlab
      hLa xB ψ ((isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K₁) K₁) X.B.pol xB ψ).2 hψ)
  obtain ⟨L, hL, hm⟩ := exists_lamLetters_isGood E H l c _ _ _ _ La hgood
  obtain ⟨kind, hkind⟩ := exists_kind Dw.mult L.m (fun τ => by
    unfold Datum.mult
    split_ifs with h
    · rw [(hm τ).1 h]; omega
    · rw [(hm τ).2 h]; omega) L.e
  obtain ⟨sB, hsB⟩ := GlobalTheory.ArcCM.exists_isSplit hK K₁ a.D₀ n' hn hτ.1
  have tor : ∀ τ : E →+* ℂ, ∃ ν : Out.GtPt a.D₀ (epsR K₁), GtTanR ν ∧ ν.b = Out.DegPre.zeroT a.D₀ (epsR K₁) ∧
      ∀ x, DlogTan ν x (labK c K₁ τ (cc (pairE ξ x))) := fun τ =>
    ((GlobalTheory.TorusTangent.main hK.laws.globalFns K₁ a.D₀).1 (AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE ξ x)))
      fun x y => by rw [(pairE_properties E a.D₀.X ξ).2.1, cc, map_add (f := _), map_add (f := _)]; rfl)).exists
  have ab : ∀ m : Fin a.D₀.P.g, ∃ ν : Out.GtPt a.D₀ (epsR K₁), GtTanR ν ∧ ∃ w : epsR K₁ ⟶ a.D₀.P.A, L.IsLetter m w ∧
      Out.GtPt.IsPull (spMap (epsScaleR ((n' : K₁)⁻¹))) (sB (epsR K₁) w) ν := fun m => by
    obtain ⟨w, hw, hc⟩ := hL.2.2.1 m
    obtain ⟨ν, h₁, h₂⟩ := exists_scaled hsB ((n' : K₁)⁻¹) (w := w) (GlobalTheory.Reg.isTangent_of_isLieComb hv.1 hc)
    exact ⟨ν, h₁, w, hw, h₂⟩
  choose et het using tor
  choose ea hea using ab
  refine ⟨fun τ k => (kind τ k).elim (et τ) ea, th,
    { B := X.B.pol, oa := oa, AΨ := (X.A true).pol, oaΨ := oaΨ, A' := (X.A false).pol, oa' := oa'
      φΨ := fun i => X.φ (Sum.inl i), φ' := fun i => X.φ (Sum.inr i)
      hΨ := fun i => X.hh (Sum.inl i), h' := fun i => X.hh (Sum.inr i)
      g_pos := hg, th_nz := hth, v := v, basis := hv, xΨ := xΨ, x' := x', φB := ψ, φΨg := φΨ, φ'g := φ'
      τΨ := τΨ, τ' := τ', ℓΨ := ℓΨ, ℓ' := ℓ', Tl := Tl, LamL := LamL
      good := hgood, act := fun x => by rw [hoa]; exact hact x
      L := L, L_good := hL, n_pos := hn, tau := hτ, sB := sB, split := hsB, rk := hrk, ξ := ξ, ξ_ne := hξ
      ν₀ := ν₀, beta := hβ, tr := htr, kind := kind, full := hkind
      tan := fun τ k => ?_, xi := fun τ k h => ?_, eta := fun τ k m h => ?_ }, rfl, rfl⟩
  · cases kind τ k with
    | none => exact (het τ).1
    | some m => exact (hea m).1
  · rw [h]; exact (het τ).2
  · rw [h]; exact (hea m).2

end GlobalTheory.ArcCM.Letters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NdegLineOptionLe
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

private theorem prod_option_eq_prod_isSome_of_none_eq_one {V M : Type} [Fintype V] [CommMonoid M] {g : ℕ} (k : V → Option (Fin g))
    (F : V → Option (Fin g) → M) (h1 : ∀ v, F v none = 1) :
    ∏ v, F v (k v) = ∏ w : {v // (k v).isSome = true}, F w.1 (some ((k w.1).get w.2)) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v => (k v).isSome = true) (fun v => F v (k v))]
  have h2 : ∏ w : {v // ¬ (k v).isSome = true}, F w.1 (k w.1) = 1 := by
    refine Finset.prod_eq_one (fun w _ => ?_)
    have hw : k w.1 = none := by simpa using w.2
    rw [hw, h1]
  rw [h2, _root_.mul_one]
  refine Finset.prod_congr rfl (fun w _ => ?_)
  rw [Option.some_get]

private theorem mLine_prodPow_option_elim_eq_prodPow_isSome {K : Type} [Field K] [NumberField K] {g : ℕ} (ℓ : Fin g → MLine K)
    {V : Type} [Fintype V] (k : V → Option (Fin g)) (mu : V → ℕ) :
    MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu =
      MLine.prodPow (fun w : {v // (k v).isSome = true} => ℓ ((k w.1).get w.2)) (fun w => mu w.1) := by
  unfold MLine.prodPow
  congr 1
  · exact prod_option_eq_prod_isSome_of_none_eq_one k (fun v o => (o.elim MLine.one ℓ).I ^ mu v) (fun v => by simp [MLine.one])
  · funext σ
    exact prod_option_eq_prod_isSome_of_none_eq_one k (fun v o => (o.elim MLine.one ℓ).n σ ^ mu v) (fun v => by simp [MLine.one])

theorem ndeg_line_option_le {K : Type} [Field K] [NumberField K] {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K)
    (de : MLine K) (La logOm : ℝ) {V : Type} [Fintype V] (k : V → Option (Fin g)) (mu : V → ℕ) (n G : ℕ)
    (h : CMNumbers0 abelian₂ ℓ de La logOm) (hG : g ≤ G) :
    ((de.pow n).tensor (MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu).dual).Good ∧
    ((de.pow n).tensor (MLine.prodPow (fun v => (k v).elim MLine.one ℓ) mu).dual).ndeg ≤
      (pDeg logOm + (1 / 2) * Real.log La) * (((∑ v, mu v : ℕ) : ℝ) + ((G * n : ℕ) : ℝ)) := by
  rw [mLine_prodPow_option_elim_eq_prodPow_isSome ℓ k mu]
  have hN := degree_norm_base K g abelian₂ ℓ de La logOm {v // (k v).isSome = true} (fun w => (k w.1).get w.2)
    (fun w => mu w.1) n h
  have hLa : 1 ≤ La := h.2.2.2.1
  have hP : 0 ≤ pDeg logOm + (1 / 2) * Real.log La := by
    have h0 := Real.log_nonneg hLa
    have h1 := abs_nonneg logOm
    unfold pDeg
    linarith
  refine ⟨hN.1, le_trans hN.2 (mul_le_mul_of_nonneg_left ?_ hP)⟩
  have hs : ∑ w : {v // (k v).isSome = true}, (mu w.1 : ℝ) ≤ ∑ v, (mu v : ℝ) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun v => (k v).isSome = true) (fun v => (mu v : ℝ))]
    have h0 : 0 ≤ ∑ w : {v // ¬ (k v).isSome = true}, (mu w.1 : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  have hgG : (g : ℝ) * n ≤ (G : ℝ) * n :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hG) (Nat.cast_nonneg n)
  push_cast
  linarith

theorem valLine_ndeg_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (logOm : ℝ) (mo : ArcLt Dw →₀ ℕ) (n : ℕ), 1 ≤ La → LamDegSt H logOm → (s.valLine mo n).Good ∧ (s.valLine mo n).ndeg ≤ (pDeg logOm + (1 / 2) * Real.log La) * (((∑ v, mo v : ℕ) : ℝ) + ((Module.finrank ℚ E / 2 * (Dw.p + Dw.q) * n : ℕ) : ℝ)) := by
  intro hK E _ _ _ H Dw l c K₁ _ _ _ a e th jj n' La c₁ s logOm mo n hLa hdeg
  letI := H.starRing
  have hcm := cmNumbers_of_good hK E H l c (Dw.p - 1) (Dw.q - 1) (Module.finrank ℚ E / 2) s.toCMPart.obj La logOm
    (fun _ => rfl) s.good s.L s.L_good hLa hdeg
  have hg : a.D₀.P.g ≤ Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have h9 : a.D₀.P.g = Module.finrank ℚ E / 2 * (Dw.p - 1 + (Dw.q - 1)) := s.good.2.2.2.2.2.2.2.2.1
    rw [h9]
    apply Nat.mul_le_mul_left
    omega
  exact ndeg_line_option_le (K := K₁) s.LamL s.L.ℓ s.Tl.dual La logOm (fun v : ArcLt Dw => s.kind v.1 v.2.2) mo n
    (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) hcm hg

end GlobalTheory.ArcCM
end

