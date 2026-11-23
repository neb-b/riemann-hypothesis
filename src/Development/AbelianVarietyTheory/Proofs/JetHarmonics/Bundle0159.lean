module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0121
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesDifferByIsometryAndTriangularOfPeriods
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.KLeSubOneOfLt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem k_le_sub_one_of_lt (R : Ranks) (l : ℕ) (h : 4 * R.t * R.r + 1 < l) : (R.k : ℝ) ≤ (l : ℝ) - 1 := by
  have h1 : R.k ≤ R.r := by have := R.two_le_m; unfold Ranks.r; omega
  have h2 : 1 ≤ R.t := by have := R.three_m_lt_t; omega
  have h3 : R.r ≤ 4 * R.t * R.r := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : R.k + 1 ≤ l := by omega
  have h5 : ((R.k + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast h4
  push_cast at h5
  linarith

theorem leafDepthRam_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepthRam N O := by
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg hSz hx hb tF
  obtain ⟨hPi, hDep, -⟩ := laws_and_nuFinAt D L Pm Tp hK T EX hM hR.star_eq
  obtain ⟨-, hW⟩ := sizes_le_two_mul D L Pm hx hb
  refine DepthTie.leafDepthRam_core_sat T (depOf T EX Tp hK) O ι N (numOf D L) hPi hM.pins hR.inR hR.E_eq hR.σ_eq
    hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hR.star_eq (fun j => hDep.chartEx _ (hR.inR j)) hPg hSz tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ ⟨?_, hR.k_eq⟩ (fun j => (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)) 1 ?_ ?_ ?_ ?_
  · rw [hR.f_eq]
    show ((2 * D.R.n : ℕ) : ℝ) = 2 * ((D.R.n : ℕ) : ℝ)
    push_cast
    ring
  · intro j
    have h1 := (GlobalTheory.WeightExponents.weight_exponents D T.Q hM.pins (ι j) (hR.inR j) (lR Tp hK (ι j))).1
    have h2 := (mul_rows_lR_le_kaR D L Pm Tp hK (ι j) (plOf D (false, 0))).2.2
    show O.T * ((DF (T.Q.Dw (ι j)) (wtA (lR Tp hK (ι j))) : ℕ) : ℝ) ≤ (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)
    rw [h1, hR.T_eq]
    exact_mod_cast h2
  · intro j
    have h1 := (DF_kaR_le D L Pm Tp hK hx hb (ι j) (hR.inR j)).1
    unfold OnObj.sB OnObj.Se
    rw [one_mul, hR.k_eq, hR.wt_eq, hR.f_eq, hR.Sc_eq, hR.eta_eq]
    exact h1
  · unfold PageRam
    rw [one_mul, hR.k_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq]
    exact ⟨k_le_sub_one_of_lt D.R _ D.host.qd_big.1, k_le_sub_one_of_lt D.R _ D.host.qd_big.2⟩
  · intro j t
    obtain ⟨h1, h2, h3⟩ := hW (ι j) (hR.inR j)
    rw [h3, h3, hR.bp_eq]
    exact ⟨(h1 _).1, (h1 _).1, (min_le_left _ _).trans (h2 t)⟩

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepthLevelRun
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem leafDepthLevel_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepthLevel N O := by
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF
  have hL := (_root_.GlobalTheory.RunDepth.laws_and_nuFinAt D L Pm Tp hK T EX hM hR.star_eq).1
  refine DepthTie.leafDepthLevel_core T (depOf T EX Tp hK) O ι N (numOf D L) hL hR.E_eq hR.σ_eq hR.nn_eq hR.T_eq
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hR.conj (fun j => _root_.GlobalTheory.RunDepth.numOf_Dplus_Dminus D L Pm Tp hK (ι j) (hR.inR j)) hPg tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ (fun j => (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)) ?_ ?_ ?_
  · intro j
    have h1 : DF (T.Q.Dw (ι j)) ((depOf T EX Tp hK).aL (ι j)) = WeightAlgebra.DF (lR Tp hK (ι j)) :=
      (_root_.GlobalTheory.WeightExponents.weight_exponents D T.Q hM.pins (ι j) (hR.inR j) (lR Tp hK (ι j))).1
    have h2 := (_root_.GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK (ι j) (plOf D (false, 0))).2.2
    simp only [h1, hR.T_eq]
    exact_mod_cast h2
  · intro j
    have h := (_root_.GlobalTheory.RunDepth.DF_kaR_le D L Pm Tp hK hx hb (ι j) (hR.inR j)).2
    rw [hR.jets_eq_fact, hR.g2_eq]
    exact ⟨h 0, h 1⟩
  · intro w _ hw
    have key : ∀ v : HeightOneSpectrum (𝓞 K), plc v = plc w → (plc w : ℝ) - 1 ≤ DepthTie.e2 T.Q.c v := by
      intro v hv
      have hc : resCharOf (placeBelow (K := T.Q.c.F) v) = plc w := (DepthTie.resChar_below v).trans hv
      have hd : resCharOf (placeBelow (K := T.Q.c.F) v) ∣ T.Q.l.M := by
        rw [hc, level_M T hM]
        rcases hw with h | h
        · rw [h, hR.jets_eq_fact]; exact Dvd.intro _ rfl
        · rw [h, hR.g2_eq]; exact Dvd.intro_left _ rfl
      have h := _root_.GlobalTheory.RunDepth.resChar_sub_one_le_ramOverZ_of_dvd_level _ _ T.Q.l T.Q.c _ hd
      rw [hc] at h
      have h' : plc w ≤ DepthTie.e2 T.Q.c v + 1 := by unfold DepthTie.e2; omega
      have h'' : (plc w : ℝ) ≤ (DepthTie.e2 T.Q.c v : ℝ) + 1 := by exact_mod_cast h'
      linarith
    exact ⟨key w rfl, key _ (plc_conjPl w)⟩

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevActMemMlat
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem fromTest_mvPt {K : Type} [Field K] {ιB : Type}
    {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
    {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop}
    {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ιB → Sˣ) → pts S → pts S → Prop}
    {G : Type} [Group G] {actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop}
    (hL : ActLaws pts mapR borR actR) (g : G) {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : FromTest pts mapR (mvPt pts actR g y) := by
  obtain ⟨p, φ, z, hz⟩ := hy
  exact ⟨p, φ, _, hL.nat g _ S φ z _ y _ hz (mvPt_spec hL.total g z) (mvPt_spec hL.total g y)⟩

theorem levAct_mem_Mlat : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) (act : P → (recB h.toLawsCore).Cusp j w → (recB h.toLawsCore).Cusp j w), IsLevAct T h j w ℓ act → ∀ g, ∀ F ∈ (recB h.toLawsCore).Mlat j w, act g F ∈ (recB h.toLawsCore).Mlat j w := by
  intro D T h j hj w P ℓ act hact g F hF
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hp.2.1.2
  have hc : (F.1 : T.R j) ∈ T.C j w := cutR_le T.C j w F.2
  have hnat := ((mem_cusp _ _ _ _ _ _).1 hc).1.1
  rintro la _ ⟨⟨q, S, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  let := io.toAlgebra
  have hmv := mvPt_spec hL.total (ℓ g) y.1
  let y' : IntFr (T.Q.Xo j) T.Q.c S io :=
    ⟨_, fromTest_mvPt hL (ℓ g) y.2.1, GlobalTheory.T.integral_framedPoint_of_level_move _ _ _ _ _ _ (levFull (T.Q.Dw j) T.Q.l (ℓ g)) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V e (evI y' F.1) := hF la _ ⟨PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (act g F).1 = evI y' F.1 := by
    rw [hact g F]
    exact evalAt_actL hL (h.evalWD j hj) frMap_trans_id (ℓ g) hnat y.1
  show 0 ≤ nval S.V e (evI y (act g F).1)
  rw [e1]
  exact h0

end GlobalTheory.FormTies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionMemCuspForms
section
namespace GlobalTheory.LevelCusp

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem exists_match (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖)
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {k k' : U.Comp} {x : (U.X k).dom} {x' : (U.X k').dom}
    {y' : FrPt Xo c (CAt σ)} {t : Ix Dw → (CAt σ)ˣ} (hm : FrMove ρ ν (U.un k x) y') (hb : FrBor t (U.un k' x') y')
    (hx : IsUnitFr (U.X k) x.1) (hx' : IsUnitFr (U.X k') x'.1) :
    ∃ (a : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k') a), ∃ b ∈ Bor (U.X k').Ψ r,
      x'.1 = rmul (lact a (castFr h.psi x.1)) b ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ j, cabs (t j : CAt σ) = 1 := by
  obtain ⟨gam, A, htr, hA0, hA, hAt⟩ := _root_.GlobalTheory.LevelCusp.exists_isometry_tri_of_frMove E H Dw l Xo c σ r U hσ hU ρ ν k k' x x' y' t hm hb
  have hgen := _root_.GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move E H Dw l Xo c σ r U hσ hU ρ ν k k' x x' y' t hm hb hx hx'
  obtain ⟨a, ε, hε, hξ, hav, hlat, hiso⟩ := GlobalTheory.T.exists_rational_isometry_of_trace_isometry E r (U.X k) (U.X k') (hxi k k') gam htr
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hrr, hty, -⟩ := hU
  have hΨ : (U.X k).Ψ = (U.X k').Ψ := Finset.ext fun τ => ((hty k).2 τ).trans ((hty k').2 τ).symm
  have hp : (U.X k).p0 = (U.X k').p0 := (hty k).1.trans (hty k').1.symm
  let e := Equiv.ofBijective _ hbij
  have he : ∀ τ, Formalism.L2.PjFree.relab c σ (e.symm τ) = τ := e.apply_symm_apply
  have m1 : ∀ τ ∈ (U.X k).Ψ, Dw.mult (e.symm τ) = r - (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_pos ((hrt _).1 (by rw [he]; exact ((hty k).2 τ).1 hτ)), (hty k).1]
    omega
  have m2 : ∀ τ ∉ (U.X k).Ψ, Dw.mult (e.symm τ) = (U.X k).p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg (fun h => hτ (((hty k).2 τ).2 (by rw [← he τ]; exact (hrt _).2 h))), (hty k).1]
  have hrel : ∀ τ, ∀ i < Dw.mult (e.symm τ), ∀ v ∈ (U.X k).Λ,
      Formalism.L2.PjFree.perFr (U.X k') x'.1 ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i =
        ∑ j ∈ Finset.range (Dw.mult (e.symm τ)), A (e.symm τ) i j * Formalism.L2.PjFree.perFr (U.X k) x.1 v τ j :=
    fun τ i hi v hv => by
      have := hA (e.symm τ) i hi ⟨v, hv⟩
      rwa [he, ← hav] at this
  rcases hε with rfl | rfl
  · have h : IsMatch (U.X k) (U.X k') a :=
      ⟨hΨ, hp, by rw [hξ, one_mul], fun u v => by rw [hiso, one_mul], hlat⟩
    obtain ⟨b, hb, hxb, hu⟩ := _root_.GlobalTheory.PeriodBorel.borel_of_periods E r _ _ a h (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel
    obtain ⟨h1, h2⟩ := hu hx hx'
    refine ⟨a, h, b, hb, hxb, h1, fun j => ?_⟩
    rcases j with _ | ⟨τ, i⟩
    · exact hgen
    · have := h2 (e τ) i (by rw [e.symm_apply_apply]; exact i.2)
      rw [e.symm_apply_apply, hAt] at this
      exact this
  · exact (GlobalTheory.T.not_antiIsometry_of_triangular_related_periods E r _ _ hΨ hp hr a hiso (fun τ => Dw.mult (e.symm τ)) m1 m2 x.1 x.2 x'.1 x'.2
      (fun τ => A (e.symm τ)) (fun τ => hA0 _) hrel).elim

theorem laU_match {k k' : U.Comp} {a : GL (Fin r) E} (h : IsMatch (U.X k) (U.X k') a)
    (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : (U.X k').Ψ) (i : Fin r) :
    Formalism.L2.PjFree.laU U w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := by
  unfold Formalism.L2.PjFree.laU
  rw [h.p0]

theorem rdU_mem_SS (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr : 1 ≤ r)
    (hxi : ∀ k k' (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ‖τ (U.X k').ξ0‖) {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom w n)
    {f g : Rul Xo c} (hf : f ∈ sec Xo c w n) (hg : g ∈ sec Xo c w n)
    (hfc : ∀ k, Formalism.L2.PjFree.rdU U f k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k))
    (hmv : ∀ y : FrPt Xo c (CAt σ), ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y' : FrPt Xo c (CAt σ)),
      FrMove ρ ν y y' ∧ evR Xo c g y = evR Xo c f y') (k : U.Comp) :
    Formalism.L2.PjFree.rdU U g k ∈ (U.X k).SS (Formalism.L2.PjFree.laU U w n k) := by
  have hsec := hU.2.2.2.2.1 w n hD g hg k
  obtain ⟨hun1, hun2⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  obtain ⟨⟨k', a, h⟩, c₀, hc⟩ := _root_.GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq (Frame (U.X k).Ψ r)
    (Σ k' : U.Comp, {a : GL (Fin r) E // IsMatch (U.X k) (U.X k') a}) (U.X k).dom (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected (GlobalTheory.frames_isConnected E r (U.X k)).nonempty
    (Formalism.L2.PjFree.rdU U g k) (fun i x => Formalism.L2.PjFree.rdU U f i.1 (lact i.2.1 (castFr i.2.2.psi x))) hsec.1
    (fun i => (hfc i.1).1.1.1.comp ((GlobalTheory.Dict.Extend.differentiable_lact i.2.1).comp
      (GlobalTheory.Dict.Pull.cast_diff i.2.2.psi)).differentiableOn fun x hx => i.2.2.mem_dom hx)
    (fun x hx => by
      obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
      obtain ⟨ρ, ν, y', hm, hv⟩ := hmv (U.un k x₀)
      obtain ⟨k', x', t, hx', hb⟩ := hun2 y'
      obtain ⟨a, h, b, hbB, hxb, hb1, ht⟩ := exists_match hσ hU hr hxi hm hb hx₀ hx'
      refine ⟨⟨k', a, h⟩, ?_⟩
      have hQ := (hfc k').1.1
      have v1 : Formalism.L2.PjFree.rdU U g k x₀.1 = Formalism.L2.PjFree.toC (evR Xo c g (U.un k x₀)) := dif_pos x₀.2
      have v2 : Formalism.L2.PjFree.rdU U f k' x'.1 = Formalism.L2.PjFree.toC (evR Xo c f (U.un k' x')) := dif_pos x'.2
      have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
        (inferInstanceAs (IsReduced ℂ)) w n f hf t _ y' hb
      have v4 : ‖Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)‖ = 1 := by
        have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ) =
          ∏ j, Formalism.L2.PjFree.toC (t j : CAt σ) ^ ex Dw w n j := rfl
        rw [this, norm_prod]
        exact Finset.prod_eq_one fun j _ => by
          rw [norm_pow, show ‖Formalism.L2.PjFree.toC (t j : CAt σ)‖ = 1 from ht j, one_pow]
      have v5 : ‖Formalism.L2.PjFree.rdU U g k x₀.1‖ = ‖Formalism.L2.PjFree.rdU U f k' x'.1‖ := by
        rw [v1, v2, hv, v3]
        exact (norm_mul (Formalism.L2.PjFree.toC (wchar (ex Dw w n) t : CAt σ)) _).trans (by rw [v4, one_mul]; rfl)
      have v6 : ‖bchar (Formalism.L2.PjFree.laU U w n k') b‖ = 1 := by
        unfold bchar
        simp only [norm_prod, norm_zpow, hb1, one_zpow, Finset.prod_const_one]
      rw [hxb, hQ.2.1 _ (h.mem_dom x₀.2) b hbB, norm_mul, v6, one_mul, e₀, hsec.2.1 x hx b₀ hb₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (laU_match h w n), norm_mul, norm_mul] at v5
      exact mul_left_cancel₀ (norm_ne_zero_iff.2 (AR.Up.OntoE.bchar_ne _ _ hb₀)) v5)
  exact _root_.GlobalTheory.LevelCusp.mem_SS_of_isMatch E r _ _ a h _ _ (laU_match h w n) _ _ c₀ hsec (hfc k') hc

end Free

end GlobalTheory.LevelCusp

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem GlobalTheory.LevelCusp.actLev_mem_cuspA : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l), ∀ f ∈ T.cuspA j (wtA w) w.n, actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ T.cuspA j (wtA w) w.n := by
  intro D T h j hj w γ f hf
  have hp := h.pins
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hp.2.1.2
  obtain ⟨hs, hc⟩ := (mem_cusp _ _ _ _ _ _).1 hf
  have hg : actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n :=
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hs
  refine (mem_cusp _ _ _ _ _ _).2 ⟨hg, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩
  have hU := h.unf j hj σ hσ
  refine GlobalTheory.LevelCusp.rdU_mem_SS (U := Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hσ hU (hU.1 ▸ hpq)
    (fun k k' τ => (h.xiAbs j hj σ hσ k τ).trans (h.xiAbs j hj σ hσ k' τ).symm) (dom_wtA w) hs hg
    (fun k => GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hc σ hσ) k) (fun y => ?_) k
  obtain ⟨ρ, ν, -, -, hm⟩ := mvPt_spec hL.total γ y
  exact ⟨ρ, ν, _, hm, evalAt_actL hL (h.evalWD j hj) frMap_trans_id γ hs.1 y⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnscaledWeightDepthFiniteBoundedAboveChartsStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unscaledWeightDepth_finite_bounded_above_charts : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), 2 * D.R.f * D.R.r ≤ w.n → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), letI := T.Q.H.starRing; nuW (T.Q.Xo j) T.Q.c la T.Q.l.M (wtA w) w.n = (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) ∧ 0 ≤ nuWt T w la ∧ nuWt T w la ≤ (WeightAlgebra.DF w : ℝ) / ((resCharOf la : ℝ) - 1) ∧ (WeightAlgebra.DF w < resCharOf la → nuWt T w la = 0) ∧ ∀ (T' : CDVR) (io : T.Q.c.F →+* T'.Fr) (e : ℕ), OverLa la T'.V io e → ∀ z : IntFr (T.Q.Xo j) T.Q.c T' io, z.IsAlg → ∀ C : IntegralChartA3 (T.Q.Xo j) T.Q.c T' io z, nuLocC C e T.Q.l.M (wtA w) w.n ≤ (((ramOverZ la : ℝ) * nuWt T w la : ℝ) : EReal) := by
  first | exact @GlobalTheory.DepthBd.nuWt_bounds | exact GlobalTheory.DepthBd.nuWt_bounds | (intros; apply GlobalTheory.DepthBd.nuWt_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueTranslatePullbackEqGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory

theorem value_translate_pullback_eq_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * l.M)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ → PullAl D' F oD' α 1 l.M θ θα → ∀ (p : QkPt D'.toPre F (1 * l.M)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * l.M)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * l.M)) (σ' : U'.toUnifPre.SecGF F (1 * l.M)) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * l.M) p w ζ → QkToAkU U'.toUnifPre F (1 * l.M) p x → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → PhiRel D'.toPre F (1 * l.M) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F (1 * l.M) σ' t → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * l.M) σ' h → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ Ppol ∈ harmA (Dw := Dw) c a n,
 letI := io.toAlgebra
 ∃ f ∈ thGen Xo c nab a n, ∃ e : F, 0 ≤ v e ∧ nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * l.M) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Ppol) = e * (∏ τ : E →+* ℂ, algebraMap T.Fr F (io (embK c τ α)) ^ (∑ i : Fin (Dw.mult τ), a (τ, i))) * algebraMap T.Fr F (evI y f) := by
  intro E _ _ _ H Dw l Xo c nab hN hT T io y C hTr P hTor hAlg ϖ hϖ Q hQ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hxe hoD α hα hMb θ θα _hNu hTh hPull p w ζ x t₀ t σ' h hw hζ hFin hQk hx hPhi hSm hExp hGerm a Ppol hPpol
  obtain ⟨xx, u, hu, hval⟩ := GlobalTheory.PtTie.harmonicValue_translate E H Dw l Xo c nab hN T io y C hTr P hTor hAlg ϖ hϖ Q hQ F v hv n D' A' G' pD pA pG U' PU oD' hxe hoD α l.M rfl hα hMb θ θα hTh hPull p w ζ x t₀ t (1 * l.M) rfl σ' h hw hζ hFin hQk hPhi hSm hExp hGerm hx
  unfold ThValTot at hT
  classical
  let f : Rul Xo c := fun p yy => (hT p.R yy a n xx Ppol hPpol).exists.choose
  have hrule : IsThRule Xo c nab xx Ppol f := by
    unfold IsThRule
    intro p yy
    exact (hT p.R yy a n xx Ppol hPpol).exists.choose_spec
  have hmem : f ∈ thGen Xo c nab a n := by
    simp only [thGen.eq_1, Set.mem_setOf_eq]
    exact ⟨xx, Ppol, hPpol, hrule⟩
  refine ⟨f, hmem, u, le_of_eq hu.symm, ?_⟩
  rw [hval a Ppol hPpol f hrule]
  simp only [GlobalTheory.PtTie.nrm, map_mul, map_prod, map_pow]
  ring

end GlobalTheory
end

