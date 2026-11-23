module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGenerator
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolating
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmLatticeDataAbelianPartSplitPoint
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbelianLetterIntegral
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcCM.EtaInt

open GlobalTheory.CM.IntCoord (sc)

theorem sc_mul {S : Type} [CommRing S] (s t : S) : sc s ≫ sc t = sc (s * t) := by
  refine Over.OverMorphism.ext ((spMap_comp_spMap _ _).trans ?_)
  show spMap _ = spMap _
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR, _root_.mul_assoc]

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  refine (spMap_comp_spMap _ _).trans ?_
  change spMap ((dualMap g).comp (dualMap f)) = spMap (dualMap (g.comp f))
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem sc_over {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} {G : Over (Sp A)} {G' : Over (Sp B)}
    {φ : G'.left ⟶ G.left} {v : epsR A ⟶ G} {v' : epsR B ⟶ G'} (h : v'.left ≫ φ = spMap (dualMap f) ≫ v.left) (a : A) :
    (sc (f a) ≫ v').left ≫ φ = spMap (dualMap f) ≫ (sc a ≫ v).left := by
  show (spMap (epsScaleR (f a)) ≫ v'.left) ≫ φ = spMap (dualMap f) ≫ spMap (epsScaleR a) ≫ v.left
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ v.left) (LieCombBaseChange.dualMap_epsScale f a).symm

theorem eq_sc_of_isLieComb {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G] {n : ℕ} {v : Fin n → (epsR S ⟶ G)}
    {c : Fin n → S} {a : S} {u w : epsR S ⟶ G} (hu : IsLieComb c v u) (hw : IsLieComb (a • c) v w) : w = sc a ≫ u := by
  rw [CM.IntCoord.isLieComb_iff] at hu hw
  have e := map_list_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G) (sc a)) (List.ofFn fun i => sc (c i) ≫ v i)
  rw [List.map_ofFn, ← hu] at e
  refine hw.trans (Eq.trans ?_ e.symm)
  congr 2
  funext i
  show sc (a * c i) ≫ v i = sc a ≫ sc (c i) ≫ v i
  rw [← Category.assoc, sc_mul]

theorem isTangent_sc {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G] {v : epsR S ⟶ G} (h : IsTangent v) (a : S) :
    IsTangent (sc a ≫ v) := by
  show _ ≫ spMap (epsScaleR a) ≫ v.left = _
  rw [← Category.assoc, spMap_comp_spMap]
  refine Eq.trans (congrArg (fun q => spMap q ≫ v.left) (RingHom.ext fun x => ?_)) h
  simp [epsScaleR]

theorem c_pow_of_pull {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] {f : A →+* B}
    {D : Out.DegPre A} {D' : Out.DegPre B} (p : Out.IsPullDeg f D D') {n : ℕ} (h : ∀ y, D.c y ^ n = 1) (y : D'.X) :
    D'.c y ^ n = 1 := by
  have gp := pull_grp p
  let U : Over.mk ((𝟙_ (Over (Sp B))).hom ≫ spMap f) ⟶ 𝟙_ (Over (Sp A)) := toUnit _
  have hU : U.left = spMap f := ((Category.comp_id _).symm.trans (Over.w U)).trans (Category.id_comp _)
  have e : pushHom gp _ (D'.c y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom U (D.c (p.xe y)) :=
    Over.OverMorphism.ext ((p.c_pr y).trans (congrArg (· ≫ (D.c (p.xe y)).left) hU.symm))
  have e' : pushHom gp _ (D'.c y ^ n) = pushHom gp _ 1 := by
    rw [map_pow, e, ← map_pow, h, map_one, map_one]
  exact Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) e') ((Over.w _).trans (Over.w _).symm))

theorem lift_through_split (hK : Known) {K V F : Type} [CommRing K] [IsDomain K] [IsNoetherianRing K] [CommRing V]
    [IsDomain V] [IsNoetherianRing V] [CommRing F] [IsDomain F] [IsNoetherianRing F] {io : K →+* F} {j : V →+* F}
    (hio : Function.Injective io) (hj : Function.Injective j) {DK : Out.DegPre K} {DV : Out.DegPre V} {DF : Out.DegPre F}
    (pK : Out.IsPullDeg io DK DF) (pw : Out.IsPullDeg j DV DF) {n : ℕ} (hn : 0 < n) (hc : ∀ y, DV.c y ^ n = 1)
    {sB : ∀ T : Over (Sp K), (T ⟶ DK.P.A) → Out.GtPt DK T} (hs : IsSplit DK n sB) {u : epsR K ⟶ DK.P.A} {a : K}
    {e : Out.GtPt DK (epsR K)} (he : Out.GtPt.IsPull (spMap (epsScaleR a)) (sB _ u) e) {v : epsR V ⟶ DV.P.A}
    (hv : IsTangent v) {u₁ : epsR F ⟶ DF.P.A} (hu₁ : u₁.left ≫ prj pK = spMap (dualMap io) ≫ u.left) (x : F)
    (h : (sc (x * io a) ≫ u₁).left ≫ prj pw = spMap (dualMap j) ≫ v.left) :
    ∃ (ν : Out.GtPt DV (epsR V)) (ν₁ e₂ : Out.GtPt DF (epsR F)),
      GtTanR ν ∧ LetBC pw ν ν₁ ∧ LetBC pK e e₂ ∧ GtComb ![x] ![e₂] ν₁ := by
  obtain ⟨sV, hV⟩ := GlobalTheory.ArcCM.exists_isSplit hK V DV n hn hc
  obtain ⟨sF, hF⟩ := GlobalTheory.ArcCM.exists_isSplit hK F DF n hn (c_pow_of_pull pw hc)
  obtain rfl : e = sB _ (sc a ≫ u) := TorsionPairTest.isPull_unique he (hs.2.2 _ _ (sc a) u)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.SplitBC.split_baseChange hK V F j DV DF pw n sV sF hj hV hF v _ h
  refine ⟨_, _, _, h₁ hv, h₂,
    (GlobalTheory.SplitBC.split_baseChange hK K F io DK DF pK n sB sF hio hs hF _ _ (sc_over hu₁ a)).2,
    ![sF _ (sc (x * io a) ≫ u₁)], ![sF _ 1, sF _ (sc (x * io a) ≫ u₁)], fun i => ?_, ?_, fun i => ?_, rfl⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hF.2.2 _ _ (sc x) (sc (io a) ≫ u₁)
    rw [← Category.assoc, sc_mul] at this
    exact this
  · have := hF.2.1 (epsR F) 1 1
    rw [_root_.mul_one] at this
    exact TanPart.isZero_of_isAdd this
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    have := hF.2.1 (epsR F) 1 (sc (x * io a) ≫ u₁)
    rw [_root_.one_mul] at this
    exact this

theorem isUnit_of_notMem {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {Tv : CDVR}
    {io : K →+* Tv.Fr} {ρ : 𝓞 K →+* Tv.V} (ho : OverLa w Tv.V io 1)
    (hρ : ∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : IsUnit (ρ s) := by
  have h1 : w.valuation K (s : K) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).2 hs
  have h0 : (s : K) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  have h2 := ho.2 (s : K)
  rw [vLa, h1, vV] at h2
  have h3 : valV Tv.V (io (s : K)) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 h0)
  have h4 : valV Tv.V (io (s : K)) = 1 := by
    rw [← WithZero.exp_log h3]
    simp only [WithZero.log_one, neg_zero, mul_zero, neg_eq_zero] at h2
    rw [h2, WithZero.exp_zero]
  rw [← hρ] at h4
  have h5 := ((IsDiscreteValuationRing.maximalIdeal Tv.V).valuation_eq_one_iff_notMem (K := Tv.Fr)).1 h4
  by_contra hu
  exact h5 hu

theorem letter_unique {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c : Coeff l} {nΨ n' : ℕ} {o : LamObj c nΨ n'} (L : LamLetters o)
    (hB : IsFibreOf o.B o.xB (gmap o.K₁) o.φB) {k : Fin o.xB.P.g} {u u' : epsR o.K₁ ⟶ o.xB.P.A} (h : L.IsLetter k u)
    (h' : L.IsLetter k u') : u = u' := by
  refine Over.OverMorphism.ext (hB.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  unfold LamLetters.IsLetter at h h'
  rcases hs : L.src k with q | q <;> rw [hs] at h h' <;> exact h.trans h'.symm

theorem letter_integral {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H} {c : Coeff l} {nΨ n' f : ℕ} {o : LamObj c nΨ n'} {La : ℝ}
    (ho : LamObjGood o f La) {L : LamLetters o} (hL : L.IsGood) (p : HeightOneSpectrum (𝓞 o.K₁)) {k : Fin o.xB.P.g}
    {cl : o.K₁} (hcl : IsLocGen p cl (L.ℓ k).I) {u : epsR o.K₁ ⟶ o.xB.P.A} (hu : L.IsLetter k u) :
    ∃ (s : 𝓞 o.K₁) (t : epsR (𝓞 o.K₁) ⟶ o.B.A), s ∉ p.asIdeal ∧ IsTangent t ∧
      (sc ((s : o.K₁) * cl) ≫ u).left ≫ o.φB = spMap (dualMap (algebraMap (𝓞 o.K₁) o.K₁)) ≫ t.left := by
  have hB := ho.2.2.2.1
  obtain ⟨M, hM, -⟩ := ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  have hf := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB o.φB).1 hB
  obtain ⟨s, hs, hm⟩ := (isModelAt_integral_iff_mem_lieLat _ o.B o.xB o.φB hf p M hM _).1
    (letter_integral_of_isLocGen E H l c nΨ n' f o La ho L hL p M hM k cl hcl)
  obtain ⟨t, ht, w, hw, hc⟩ := ((CM.integral_tangent_coordinates _ o.B _).2.2.2.2.1 _).1 hm
  obtain ⟨u', hu', hU⟩ := hL.2.2.1 k
  obtain rfl := letter_unique L hB hu hu'
  have e : s • cl • L.U k = ((s : o.K₁) * cl) • L.U k := by
    rw [mul_smul]; exact (algebraMap_smul o.K₁ s _).symm
  have hc' : IsLieComb (((s : o.K₁) * cl) • L.U k) o.xB.v w := e ▸ hc
  exact ⟨s, t, hs, ht, eq_sc_of_isLieComb hU hc' ▸ hw⟩

end GlobalTheory.ArcCM.EtaInt

namespace GlobalTheory.ArcCM

open EtaInt
open GlobalTheory.CM.IntCoord (sc)

theorem abelian_letter_integral : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) (m : Fin d.a.D₀.P.g) (cl : K₁), s.kind τ k = some m → IsLocGen w cl (s.line τ k).I → ∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![io ((n' : K₁) * cl)] ![e₂] ν₁ := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ ho hρ hψ hsq hτ τ k m cl hk hcl
  letI := H.starRing
  obtain ⟨u, hu, he⟩ := s.eta τ k m hk
  have hcl' : IsLocGen w cl (s.L.ℓ m).I := by
    have : s.line τ k = s.L.ℓ m := by unfold CMIn.line; rw [hk]; rfl
    exact this ▸ hcl
  obtain ⟨r, t, hr, ht, hrt⟩ := letter_integral s.good s.L_good w hcl' hu
  obtain ⟨r', hr'⟩ := (isUnit_of_notMem ho hρ hr).exists_left_inv
  obtain ⟨v, hv, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
  obtain ⟨u₁, hu₁, -⟩ := existsUnique_isVecOver (pull_grp M.pK).1 u
  obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver (pull_grp M.pw).1 v
  have hu₁' : u₁.left ≫ prj M.pK = spMap (dualMap io) ≫ u.left := hu₁
  have hv₁' : v₁.left ≫ prj M.pw = spMap (dualMap (algebraMap Tv.V Tv.Fr)) ≫ v.left := hv₁
  have hv' : v.left ≫ ψ = spMap (dualMap ρ) ≫ t.left := hv
  have hrt' : (sc ((r : K₁) * cl) ≫ u).left ≫ s.φB = spMap (dualMap (algebraMap (𝓞 K₁) K₁)) ≫ t.left := hrt
  have hring : (algebraMap Tv.V Tv.Fr).comp ρ = io.comp (algebraMap (𝓞 K₁) K₁) := RingHom.ext hρ
  have e₁ : v₁ = sc (io ((r : K₁) * cl)) ≫ u₁ := by
    refine Over.OverMorphism.ext (((pull_grp M.pw).1.paste_horiz hψ.2.1.1).hom_ext ?_
      ((Over.w _).trans (Over.w _).symm))
    show v₁.left ≫ prj M.pw ≫ ψ = (sc (io ((r : K₁) * cl)) ≫ u₁).left ≫ prj M.pw ≫ ψ
    have a₁ : v₁.left ≫ prj M.pw ≫ ψ = spMap (dualMap ((algebraMap Tv.V Tv.Fr).comp ρ)) ≫ t.left := by
      rw [← Category.assoc, hv₁', Category.assoc, hv', ← Category.assoc, dual_comp]
    have a₂ : (sc (io ((r : K₁) * cl)) ≫ u₁).left ≫ prj M.pK ≫ s.φB =
        spMap (dualMap (io.comp (algebraMap (𝓞 K₁) K₁))) ≫ t.left := by
      rw [← Category.assoc, sc_over hu₁', Category.assoc, hrt', ← Category.assoc, dual_comp]
    rw [a₁, hsq, a₂, hring]
  have hn : (n' : K₁) ≠ 0 := Nat.cast_ne_zero.2 s.n_pos.ne'
  refine lift_through_split hK io.injective (IsFractionRing.injective Tv.V Tv.Fr) M.pK M.pw s.n_pos hτ.1 s.split he
    (isTangent_sc (hv.isTangent hψ.2.1 ht) r') hu₁' _ ?_
  have e₂ : io ((n' : K₁) * cl) * io (n' : K₁)⁻¹ = algebraMap Tv.V Tv.Fr r' * io ((r : K₁) * cl) := by
    rw [← map_mul, mul_right_comm, mul_inv_cancel₀ hn, _root_.one_mul, map_mul, ← hρ, ← _root_.mul_assoc, ← map_mul, hr',
      map_one, _root_.one_mul]
  rw [e₂, ← sc_mul, Category.assoc, ← e₁]
  exact sc_over hv₁' r'

end GlobalTheory.ArcCM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointEqOfModelsOverBaseStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem _root_.GlobalTheory.T.arc_framed_point_eq_of_models_over_base :
    Out.Laws → Out.Laws2 → Out.Laws5 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
      (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
      (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn Dw l (RingHom.id c.F) k bF)
      (V V' : ValuationSubring ℂ) (Y : Model Xo c (c.V V).subtype)
      (Y' : Model Xo c (c.V V').subtype) (χ : Sp (PowerSeries k) ⟶ Y.X)
      (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : Wit Y (a.restrict (c.V V).subtype) χ)
      (W' : Wit Y' (a.restrict (c.V V').subtype) χ'),
    χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V).subtype) →
    χ' ≫ Y'.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V').subtype) →
    ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec),
    ThNZ th →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Nontrivial S] (ι : PowerSeries k →+* S)
      (y y' : FrPt Xo c S),
    IsUnit (ι PowerSeries.X) →
    GlobalTheory.ArcQ.IsArcFr W e th ι y → GlobalTheory.ArcQ.IsArcFr W' e th ι y' → y = y' :=
  @GlobalTheory.ArcQ.isArcFr_eq_of_overBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDiscStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_framedPoint_integral_open_disc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) [IsPrincipalIdealRing A] (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec), ArcBasis W ρ e → ThNZ th → PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (ev : PowerSeries A →+* T.V), Function.Injective (ev.comp (PowerSeries.C (R := A))) → (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ev (PowerSeries.C (R := A) (ρ τ x)))) → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y → Integral T io y := by
  exact @GlobalTheory.ArcQ.integral_of_isArcFr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelOneSectionEqKappaThetaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_levelOne_section_eq_kappa_theta : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GlobalTheory.ArcPts.GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → ∃ T₂ : ℝ, ∀ T ≥ T₂, ∀ (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fu.Di K.i).La) (S : Finset (Fin g)) (h : Matrix (Fin g) (Fin g) ℂ) (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)), ThetaHyp W th σ fam → (∀ u v, (Fu.Di K.i).EF (bas u) (bas v) = -omegaStd u v) → (∀ u, Λ.ε (K.gam (bas u)).y = 0 ↔ ∀ k ∈ S, u (.inr k) = 0) → (∀ w k, h.mulVec (K.Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ h.mulVec (K.Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ → IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ → (∃ w fr, T < w.im ∧ IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr) → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ k ∈ S, c₁ k = 0) ∧ (∀ w : ℂ, T < w.im → IsFnInRigFrame a.D₀ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (K.h.symm z)).b.left)) th (fun z => κ * thetaCharOff S (τ w) c₁ c₂ (h.mulVec z))) ∧ ∀ (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ), ⊤ ≤ χ ⁻¹ᵁ U → s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U) → PullHyp W σ w₂ U s r → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u K.i (K.Pw w)) (fun z => (Fu.ex K.i (K.Pw w) z).left) (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) = valAt' x _ (w₁.s (fun _ => j, k)).val * (κ * rw * thetaChar (τ w) c₁ c₂ (h.mulVec z) * fr j₀ z) := by
  first | exact @GlobalTheory.ArcPts.arc_theta | exact GlobalTheory.ArcPts.arc_theta | (intros; apply GlobalTheory.ArcPts.arc_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAnalyticModelOnFrameOrbitIsolatingStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (n' : ℕ) (ν₀ : E), Formalism.L2.PjFree.GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → letI := H.starRing; ∃ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (jj : ℤ) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ ∧ ξ ≠ 0 ∧ Module.finrank (𝓞 E) A.X = 1 ∧ (∀ y y', (2 * l.M' : ℤ) ∣ A.be y y') ∧ BetaAt ξ l.M' A.be ν₀ jj ∧ PrimAn H A ∧ (∀ y, n' • A.ct y ∈ A.abelian₂) ∧ AbDat H A DB tyB eB ∧ DB.p = Dw.p - 1 ∧ DB.q = Dw.q - 1 := by
  first | exact @GlobalTheory.AnAtFrame.exists_anArc_onOrbit | exact GlobalTheory.AnAtFrame.exists_anArc_onOrbit | (intros; apply GlobalTheory.AnAtFrame.exists_anArc_onOrbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmLatticeDataAbelianPartSplitPointStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_lattice_data_abelianPart_split_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La : ℝ) (lam : Fin (r - 2) → Fin r → E), Formalism.L2.PjFree.GoodEmb c σ → IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La (hX ▸ x) lam → letI := H.starRing; ∀ (A : AnArc (𝓞 E)) (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] A.La) (ξ : Module.Dual ℤ A.X) (DB : Datum H) (tyB : Fin A.gB → (E →+* ℂ)) (eB : DB.La ≃+ A.abelian₂), OnOrbit Uw k ξ' x A gam ξ → Module.finrank (𝓞 E) A.X = 1 → DB.p = Dw.p - 1 → DB.q = Dw.q - 1 → ∀ hB : AbDat H A DB tyB eB, ∃ Z : GlobalTheory.CM.CMLat hB.2.2.2.2 DB.p DB.q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  first | exact @GlobalTheory.ArcCM.SplitLat.exists_cmLat_abelianPart | exact GlobalTheory.ArcCM.SplitLat.exists_cmLat_abelianPart | (intros; apply GlobalTheory.ArcCM.SplitLat.exists_cmLat_abelianPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcQ.FrBC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem isRigIso_iff {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) :
    IsRigIso m L' L w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl))

theorem exists_rigIso_cancel {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w'' : LB.Iso L''.L (L.L.pull n.F)) (hw : IsRigIso m L' L w) (hw'' : IsRigIso n L'' L w'') :
    ∃ w' : LB.Iso L''.L (L'.L.pull m'.F), IsRigIso m' L'' L' w' ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ G''.left) (y : Y) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        m.F (m'.F (f y)) ∈ L.L.U j → m'.F (f y) ∈ L'.L.U i → f y ∈ L''.L.U k →
        gw w'' f y j k = gw w (f ≫ m'.F) y j i * gw w' f y i k := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  rw [isRigIso_iff] at hw hw''
  obtain ⟨g, r⟩ := hw
  obtain ⟨g'', r''⟩ := hw''
  obtain ⟨w', T⟩ := exists_cancel L.isLB w w'' g g'' L'.isLB L''.isLB
  exact ⟨w', (isRigIso_iff _ _ _ _).2 ⟨T.pgen_cancel L.isLB g g'',
    T.pmaps_cancel L.isLB (fun _ => m'.e_comm) r r''⟩, T⟩

theorem gs_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} {θ : LB.Sec L} (h : IsoMaps w σ s) (p : PullSec F θ s)
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have a := congrArg (gs r z _) (h (fun _ => j) k)
  have le : (L.pull F).U (fun _ => j) ≤ F ⁻¹ᵁ L.U j := fun q hq => mem_pull.1 hq
  refine Eq.trans ?_ ((gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _)))))
  rw [p (fun _ => j) le]
  exact (gs_appLE F _ _ le r z (mem_pull.2 hj) _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isoMaps_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {x : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (n : SABMap t'' t x) (hx : x = g ≫ f)
    (hφ : n.φ = m'.φ ≫ m.φ) {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {w'' : LB.Iso t''.PP.L (t.PP.L.pull n.φ)}
    (hw : RigIso m w) (hw'' : RigIso n w'') {θ : LB.Sec t.PP.L} {θ' : LB.Sec t'.PP.L} {σ : LB.Sec t''.PP.L}
    {s : LB.Sec (t.PP.L.pull m.φ)} {s'' : LB.Sec (t.PP.L.pull n.φ)} (i : IsoMaps w θ' s) (p : PullSec m.φ θ s)
    (i'' : IsoMaps w'' σ s'') (p'' : PullSec n.φ θ s'') :
    ∃ w' : LB.Iso t''.PP.L (t'.PP.L.pull m'.φ), RigIso m' w' ∧ IsoMaps w' σ (thfPull t'.PP.L m'.φ θ') := by
  have he : n.cm.e = m'.cm.e ≫ m.cm.e := by rw [n.base, m'.base, m.base, hx]
  obtain ⟨w', r', tri⟩ := exists_rigIso_cancel m.cm m'.cm n.cm hφ he t''.PP t'.PP t.PP w w'' hw hw''
  refine ⟨w', r', fun (a : PUnit → t'.PP.L.ι) k => fn_ext fun y hy => ?_⟩
  have hi : m'.φ y ∈ t'.PP.L.U (a PUnit.unit) := mem_pull.1 hy.1
  obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (m'.φ y))
  have pt : n.φ y = m.φ (m'.φ y) := congrArg (fun q => q y) hφ
  have e1 := gs_of_isoMaps i p (𝟙 _ ≫ m'.φ) y j (a PUnit.unit) hj hi
  have e2 := gs_of_isoMaps i'' p'' (𝟙 _) y j k (pt ▸ hj) hy.2
  have e3 := tri _ (𝟙 _) y j (a PUnit.unit) k hj hi hy.2
  have e4 : (𝟙 _ ≫ m'.φ) ≫ m.φ = 𝟙 _ ≫ n.φ := by rw [Category.assoc, hφ]
  rw [e4, e2, e3, Units.val_mul, _root_.mul_assoc, Units.mul_right_inj] at e1
  refine (gs_res _ y _ hy _).trans ((gs_appLE m'.φ _ _ _ (𝟙 _) y hy.1 _).trans (e1.symm.trans ?_))
  refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
  exact congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (φ.comp io) = spMap φ ≫ spMap io := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← spMap_comp', ← spMap_comp']
  congr 1
  exact Formalism.L2.Pj.dualMap_alg φ

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (io : R →+* S) (φ : S →+* T) :
    spMap (dualMap (φ.comp io)) = spMap (dualMap φ) ≫ spMap (dualMap io) := by
  rw [← spMap_comp']
  congr 1
  exact Formalism.L2.Pj.dualMap_comp io φ

end GlobalTheory.ArcQ.FrBC

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames


open FrBC in
theorem isArcFr_witBC : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A'] (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A') (p : Out.IsPullDeg f a.D₀ a'.D₀) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)), Mono Y.j → InBC f a a' p → WitBC f p W W' → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A')) th th', (∀ τ k, LetBC p (e τ k) (e' τ k)) → ThBC p th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι' : PowerSeries A' →+* S) (y : FrPt Xo c S), IsArcFr W e th (ι'.comp (PowerSeries.map f)) y → IsArcFr W' e' th' ι' y := by
  intro hL hL2 E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W A' _ _ _ _ b' a' f p W' hj hin hwit e e' th th' he hth
    S _ _ ι' y h
  obtain ⟨m, hm, hlie, hθ⟩ := _root_.GlobalTheory.ArcBaseChange.main
    hL hL2 E H Dw l Xo c O β Y A b a χ W A' b' a' f p W' hin hwit
  obtain ⟨z, G, m1, m2, φ, zj, zx, φb, φ1, φ2, hu, θ, w1, w2, σ, s1, θ2, hT, r1, r2, i1, i2, p2, hg⟩ := h
  have hio : spMap (ι'.comp (PowerSeries.map f)) = spMap ι' ≫ spMap (PowerSeries.map f) := spMap_comp' _ _
  have key : ∀ (g : Sp S ⟶ Sp (PowerSeries A)) (n : SABMap G W.t g), g = spMap ι' ≫ spMap (PowerSeries.map f) →
      ∃ m' : SABMap G W'.t (spMap ι'), n.φ = m'.φ ≫ m.φ := by
    intro g n hg
    subst hg
    exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
  obtain ⟨m', e₂⟩ := key _ m2 hio
  obtain ⟨w, θ', rw', iw⟩ := pull_sec W.t W'.t m θ
  have pw : PullSec m.φ θ (thfPull W.t.PP.L m.φ θ) := fun _ _ => rfl
  obtain ⟨w', r', i'⟩ := exists_isoMaps_cancel m m' m2 hio e₂ rw' r2 iw pw i2 p2
  refine ⟨z, G, m1, m', φ, ?_, zx, φb, φ1, ?_, fun τ k => ?_, θ', w1, w', σ, s1, _,
    hθ w th th' θ θ' _ rw' hth hT pw iw, r1, r', i1, i', fun _ _ => rfl, hg⟩
  · rw [zj, hio, Category.assoc]
  · rw [φ2, hm, e₂, Category.assoc]
  · obtain ⟨v, q₀, h1, h2, h3, -⟩ := hu τ k
    have vb : v.left ≫ W.t.G.hom = spMap (algebraMap _ (DualNumber (PowerSeries A))) := Over.w v
    have pb : (q₀ ≫ G.G.hom) ≫ spMap (ι'.comp (PowerSeries.map f)) =
        spMap (algebraMap S (DualNumber S)) ≫ spMap (ι'.comp (PowerSeries.map f)) := by
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc]
      exact (congrArg (· ≫ W.t.G.hom) h3).trans (by rw [Category.assoc, vb, dual_alg])
    have pz : (q₀ ≫ G.G.hom) ≫ z = spMap (algebraMap S (DualNumber S)) ≫ z := by
      rw [← cancel_mono Y.j, Category.assoc, zj, ← Category.assoc, pb, Category.assoc, Category.assoc, zj]
    let q := m1.cart.1.lift (y.u τ k) _ (y.tan τ k).1
    have hq : q ≫ m1.φ = y.u τ k := m1.cart.1.lift_fst _ _ _
    have qb : q ≫ G.G.hom = spMap (algebraMap S (DualNumber S)) := m1.cart.1.lift_snd _ _ _
    have qφ : q ≫ φ = q₀ ≫ φ := by
      apply Y.m0.toSABMap.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc]
        exact ((congrArg _ φ1).trans (hq.trans h2.symm)).trans (congrArg _ φ1.symm)
      · rw [Category.assoc, Category.assoc, φb, ← Category.assoc, ← Category.assoc, qb, pz]
    have q2 : q ≫ m2.φ = q₀ ≫ m2.φ := by
      apply W.m.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc]
        refine (congrArg _ φ2.symm).trans (Eq.trans ?_ (congrArg _ φ2))
        rw [← Category.assoc, qφ, Category.assoc]
      · rw [Category.assoc, Category.assoc, m2.cart.1.w, ← Category.assoc, ← Category.assoc, qb, pb]
    have cond : (spMap (dualMap (PowerSeries.map f)) ≫ v.left) ≫ W.t.G.hom =
        spMap (algebraMap (PowerSeries A') (DualNumber (PowerSeries A'))) ≫ spMap (PowerSeries.map f) := by
      rw [Category.assoc, vb, dual_alg]
    let v' : epsR (PowerSeries A') ⟶ W'.t.G := Over.homMk (m.cart.1.lift _ _ cond) (m.cart.1.lift_snd _ _ cond)
    have hv : v'.left ≫ m.φ = spMap (dualMap (PowerSeries.map f)) ≫ v.left := m.cart.1.lift_fst _ _ cond
    have vb' : v'.left ≫ W'.t.G.hom = spMap (algebraMap _ (DualNumber (PowerSeries A'))) := Over.w v'
    refine ⟨v', q, hlie _ _ v v' (he τ k) h1 hv, hq, ?_, qb⟩
    apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      refine (congrArg _ e₂.symm).trans ((q2.trans h3).trans (Eq.trans ?_ (congrArg _ hv.symm)))
      rw [dual_comp, Category.assoc]
    · rw [Category.assoc, Category.assoc, m'.cart.1.w, vb', dual_alg, ← Category.assoc, qb]

end GlobalTheory.ArcQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalTrivialisationIffNormalisedArcStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTauCanonicalTrivialisation_iff_normalised_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (b : O →+* ℂ) (a : ArcIn Dw l β ℂ b) (Λ : GtAn₀ a) (n : ℕ), letI := H.starRing; (TauCan a.D₀ n ↔ NormAn Λ.A n) := by
  first | exact @GlobalTheory.KappaAn.tauCan_iff_normAn | exact GlobalTheory.KappaAn.tauCan_iff_normAn | (intros; apply GlobalTheory.KappaAn.tauCan_iff_normAn <;> assumption)
end

