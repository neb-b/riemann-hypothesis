module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
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
public import Development.AutomorphicArithmetic.CMTraceForms.Places
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimesOfChartForm
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory

theorem leafDepthGood_of_chartForm : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  intro hUp
  obtain ⟨C0, h⟩ := _root_.GlobalTheory.GoodDepth.leafGood_run
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T hT EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm hR
  exact h D L Pm Tp hK T hT EX K Bs Df S P oc O ι Nm hR
    (fun j => _root_.GlobalTheory.goodPrime_packages hUp _ _ _ _ (T.Q.Xo (ι j)) T.Q.c)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeUnscaledAddBoundary
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.RecDepth

theorem depth_le : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  intro hHT D T h j hj hinj EX w c hO hR la y
  by_cases hla : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal
  · obtain ⟨i, hi⟩ := hla
    exact _root_.GlobalTheory.DepthOverLevel.depth_le_over_level hHT D T h j hj hinj EX w c hO hR la i hi y
  · exact _root_.GlobalTheory.DepthPrimeToLevel.depth_le D T h j hj hinj EX w c hO hR la (fun i hi => hla ⟨i, hi⟩) y

end GlobalTheory.RecDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBoundAtResidueCharacteristic
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem ramOverZ_pos_place {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 < ramOverZ la := by
  have h := Crude.crv_vLa_char la
  rw [Crude.crv_vLa_natCast_eq] at h
  have h0 : ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (Crude.resCharOf_prime la).ne_zero
  have h1 : la.intValuation ((resCharOf la : ℕ) : 𝓞 K) < 1 :=
    (la.intValuation_lt_one_iff_mem _).2 (Crude.crv_char_mem la)
  have h2 : WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K)) < 0 := by
    have := (WithZero.log_lt_log (la.intValuation_ne_zero _ h0) one_ne_zero).2 h1
    simpa using this
  omega

theorem vV_eq_zero_of_isUnit (T : CDVR) {x : T.V} (hx : IsUnit x) : vV T.V (algebraMap T.V T.Fr x) = 0 := by
  have h : valV T.V (algebraMap T.V T.Fr x) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    intro hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hx
  simp [vV, h]

theorem nuW_le_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitAt H.d p → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (la : HeightOneSpectrum (𝓞 c.F)), resCharOf la = p → ∀ (k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuW Xo c la k a n ≤ (((ramOverZ la : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  intro p _ hA hH E _ _ _ H Dw l Xo c inst hst f vd hvd hsp hT la hla k n a ha hn Ap hAp hle
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starSt E H inst hst
  letI := H.starRing
  have hE : IntChartEx Xo c := (GlobalTheory.IntChartExists.intChart_exists E H Dw l Xo c).2.1 hst
  refine max_le ?_ ?_
  · rw [EReal.coe_nonneg]
    positivity
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho => iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  have hv : vV T.V ((p : ℕ) : T.Fr) = (e : ℤ) * (ramOverZ la : ℤ) := by
    rw [← map_natCast io, ho.2, ← hla, Crude.crv_vLa_char]
  have he : 0 < e := ho.1
  have hnu : ¬ IsUnit ((p : ℕ) : T.V) := by
    intro hu
    have h0 := vV_eq_zero_of_isUnit T hu
    rw [map_natCast, hv] at h0
    have := ramOverZ_pos_place la
    have : (0 : ℤ) < (e : ℤ) * (ramOverZ la : ℤ) := by positivity
    omega
  refine (iInf_le _ C).trans ((GlobalTheory.T.integralChartDepth_le_residueChar_two p hA hH E H Dw l Xo c T io y C hy hnu hsp f vd hvd hT e k n a he ha hn Ap hAp hle).trans (le_of_eq ?_))
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  rw [hv, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_cancel_left₀ _ he']

end GlobalTheory.CharDepth
end

