module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.DIV.Cons
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Top (D : D7) : Type 1 extends Core D where
  G : In66 Q
  nab : ∀ j, NabV (Q.Xo j) Q.c
  dδ : ∀ j n, DeltaDat (Q.Xo j) Q.c n

variable {D : D7}

def badN (D : D7) : ℕ := D.host.QS * D.host.q * D.host.d * ∏ p ∈ D.host.levelPrimes, p

def wEt (D : D7) (j i : ℕ) : WeightFamilies.Wt D j :=
  WeightAlgebra.wscalar D j (WeightAlgebra.g0 D * i) (by unfold WeightAlgebra.g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)

structure LawsP (T : Top D) : Prop extends LawsCore T.toCore where

  allTest : ∀ j, InR D j → AllTest (T.Q.Xo j) T.Q.c

  reg : ∀ j, InR D j → regular₂ (T.Q.Xo j) T.Q.c (T.U j)

  datum_condition : T.G.PinDat
  tower : T.G.PinTower
  hasData_condition : T.G.HasData
  points_condition : T.G.PinPts
  lattice_condition : T.G.PinLat
  bc66 : T.G.BaseChange

  datIndep : ∀ j, 1 ≤ j → j < D.R.m → DatIndep (T.Q.Xo j) T.Q.c

  nabPin : ∀ j, InR D j → ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c (T.nab j)

  nabUniq : ∀ j, InR D j → NabUniq (T.Q.Xo j) T.Q.c

  thTot : ∀ j, InR D j → ThValTot (T.Q.Xo j) T.Q.c (T.nab j)
  thCusp : ∀ j, InR D j → ThInCusp (T.Q.Xo j) T.Q.c (T.nab j) (T.cuspA j)
  thNe : ∀ j, 1 ≤ j → j < D.R.m → ThNe0 (T.Q.Xo j) T.Q.c (T.nab j)

  kPsi : ∀ j, InR D j → KPsiIn (Dw := T.Q.Dw j) T.Q.c

structure LawsSh (T : Top D) : Prop where
  beta : ∀ j, InR D j → ∀ n, BetaExists (Dw := T.Q.Dw j) T.Q.c n (badN D)
  dLev : ∀ j, InR D j → ∀ n, (T.dδ j n).IsLev
  dNab : ∀ j, InR D j → ∀ n, ∃ _ : StarRing (𝓞 D.host.E), IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).nab₂

  dPd : ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ∀ j, InR D j → ∀ n, (T.dδ j n).pd = p

  dPhi : ∀ j, InR D j → ∀ n, D.R.r ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ (T.dδ j n).PhiPin ph ψ x₀ ∧ (T.dδ j n).PsiTie ψ

  dRoot : ∀ j, InR D j → ∀ n, ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* (T.dδ j n).c₂.Fˣ)
    (gdet : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom) → Cls),
    CMP (T.Q.Xo j) T.Q.c (T.dδ j n) _ Cls δ gdet false
  shTot : ∀ j, InR D j → ∀ a n, Dom a n →
    ShortValTot (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)
  shCusp : ∀ j, InR D j → ∀ a n, Dom a n → LastPos (T.Q.Dw j) a →
    ShortInCusp (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.cuspA j) a n (T.dδ j n)
  shNe : ∀ j, 1 ≤ j → j < D.R.m → ShortNe0 (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (T.dδ j) (T.cuspA j)

def Packet66Rest (Q : Par D) : Prop :=
  ∃ G : In66 Q, G.PinDat ∧ G.PinTower ∧ G.HasData ∧ G.PinPts ∧ G.PinLat ∧ G.BaseChange

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.HeightF1OfData
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem extVal_unit_zero (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    apply le_antisymm ((IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one _)
    have h2 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (R := T.V) (K := T.Fr) ((u⁻¹ : T.Vˣ) : T.V)
    have h3 : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    by_contra hlt
    rw [not_le] at hlt
    have : valV T.V (algebraMap T.V T.Fr (u : T.V)) * valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this
    exact lt_irrefl _ this
  simp [vV, h1]

def OrdTieQZ (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), IsNormDiscrete v → IsTrivOn c.F v →
    ∃ q : QPt Xo c,
      (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
        (((ordC (δ Z v) v (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 → ordQ Xo c q f = ⊤

theorem height_F1_of_data (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    {rU : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ rU)
    (hreg : regular₂ Xo c U) (htie : OrdTieQZ h δ)
    (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2)
    (hws : ∀ k, wR k ∈ cusp Xo c U uL.1 uL.2) (het : etR ∈ cusp Xo c U uet.1 uet.2)
    (hnz : NoCommonZero Xo c wR) (hnzet : NZAt h etR)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2) (hcc : 0 ≤ cc)
    (nuA : HeightOneSpectrum (𝓞 c.F) → ℝ)
    (halg : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v etR ∧
      (v etR ≠ ⊤ → (⨅ k, v (wR k)) ≤ (nuA la : EReal) + ((cc / (2 * i) : ℝ) : EReal) * v etR)) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).TrivialPlaceHyp := by
  classical
  have hc' : (0 : ℝ) ≤ cc / (2 * i) := div_nonneg hcc (by positivity)

  have hR2 := (hreg.1.2 ⟨uL, hdL⟩ ⟨uet, hdE⟩ (N + 1) (fun k => ⟨wR k, hws k⟩) ⟨etR, het⟩ nuA (cc / (2 * i)) hc'
    hnz (fun la y => halg la y.1 y.2)).2
  unfold Data.TrivialPlaceHyp
  intro Z v hAdm hTv
  obtain ⟨q, hq1, hq0⟩ := htie Z v hAdm.1 hTv

  have hqT : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
    refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
    obtain ⟨u, hu⟩ := q.triv a ha
    rw [← hu]
    exact extVal_unit_zero q.T u
  obtain ⟨hE0, hEb⟩ := hR2 ⟨_, hqT⟩
  dsimp only [dataOf, Data.n1] at *
  rw [← huet]
  have hEq : (((ordC (δ Z v) v (wtZ uet.1 uet.2) (valC h uet.1 uet.2 etR Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q etR :=
    hq1 uet.1 uet.2 etR (cusp_le_sec Xo c U _ _ het) (hnzet Z)
  have hEne : ordQ Xo c q etR ≠ ⊤ := by rw [← hEq]; exact EReal.coe_ne_top _
  have hb := hEb hEne
  obtain ⟨k0, hk0⟩ := exists_eq_ciInf_of_finite (f := fun k : Fin (N + 1) => ordQ Xo c q (wR k))
  have hk0le : ordQ Xo c q (wR k0) ≤ ((cc / (2 * i) : ℝ) : EReal) * ordQ Xo c q etR := by
    rw [hk0]; exact hb
  have hev : evC h Z (wR k0) ≠ 0 := by
    intro h0
    rw [hq0 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) h0, ← hEq, ← EReal.coe_mul] at hk0le
    exact EReal.coe_ne_top _ (top_le_iff.1 hk0le)
  have hval : valC h uL.1 uL.2 (wR k0) Z ≠ 0 := valC_ne_zero hev
  have hk0' := hq1 uL.1 uL.2 (wR k0) (cusp_le_sec Xo c U _ _ (hws k0)) hev
  rw [← hk0', ← hEq, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hk0le
  have hle : (⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR j) Z)) ≤
      ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) :=
    ciInf_le (Set.finite_range _).bddBelow (⟨k0, hval⟩ : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0})
  have hle' : ((⨅ j : {j // valC h uL.1 uL.2 (wR j) Z ≠ 0}, ordC (δ Z v) v (wtZ uL.1 uL.2)
      (valC h uL.1 uL.2 (wR j) Z) : ℤ) : ℝ) ≤ (ordC (δ Z v) v (wtZ uL.1 uL.2) (valC h uL.1 uL.2 (wR k0) Z) : ℝ) := by
    exact_mod_cast hle
  exact hle'.trans hk0le

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.HtXfer
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.HeightData NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
  {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra B.KO (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra B.KO (A c)]
  [∀ c, Algebra (𝓞 B.KO) (A c)] {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

theorem lN_nonneg' (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    0 ≤ Formalism.MainNotions.Gaps.HeightData.lN K la := by
  unfold Formalism.MainNotions.Gaps.HeightData.lN
  refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
  have h0 : Ideal.absNorm la.asIdeal ≠ 0 := fun h => la.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h0

theorem htConcl_toHtData_of (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1)
    (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ)
    (hD : (d.htOf hd hs).D = WeightFamilies.dimY D j) (hδ : (d.htOf hd hs).δ = G.del) (hi : (d.htOf hd hs).i = G.iet)
    (hg0 : (d.htOf hd hs).g0 = (g0 D : ℝ)) (hL : (d.htOf hd hs).L = wL.size) (hG : (d.htOf hd hs).G = Gc)
    (hPH : (d.htOf hd hs).PH = PH) (hPrw : (d.htOf hd hs).Prw = Prw) (hPet : (d.htOf hd hs).Pet = Pet)
    (hS : ∑ k, (d.htOf hd hs).S k ≤ ∑ k, WeightFamilies.meanLogSup B (G.th' k))
    (hI : ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Ila la ≤ (d.htOf hd hs).Ila la)
    (hN : ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Net la = (d.htOf hd hs).Net la)
    (h : Formalism.MainNotions.Gaps.HeightData.HtConcl (d.htOf hd hs)) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl (toHtData G Qf Gc PH Prw Pet) := by
  obtain ⟨hfin, hsum, hineq, heta⟩ := h
  have hle : ∀ la : HeightOneSpectrum (𝓞 B.KO),
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la := fun la =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast ENat.toNat_le_toNat (hI la) (hfin la)) (lN_nonneg' _ la)
  have hsum' : Summable fun la : HeightOneSpectrum (𝓞 B.KO) =>
      (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la :=
    Summable.of_nonneg_of_le (fun la => mul_nonneg (Nat.cast_nonneg _) (lN_nonneg' _ la)) hle hsum
  have hDr : ((d.htOf hd hs).D : ℝ) = (WeightFamilies.dimY D j : ℝ) := by exact_mod_cast hD
  have hδr : ((d.htOf hd hs).δ : ℝ) = (G.del : ℝ) := by exact_mod_cast hδ
  have hir : ((d.htOf hd hs).i : ℝ) = (G.iet : ℝ) := by exact_mod_cast hi
  refine ⟨fun la => ne_top_of_le_ne_top (hfin la) (hI la), hsum', ?_, fun he => ?_⟩
  · have ht := Summable.tsum_le_tsum hle hsum' hsum
    have hineq' : 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
          (((d.htOf hd hs).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (G.del : ℝ) * Real.log G.del + 2 * ∑ k, (d.htOf hd hs).S k +
        8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
        2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size := by
      rw [hDr, hδr, hL, hG, hPH, hPrw] at hineq
      exact hineq
    show 2 * ∑' la : HeightOneSpectrum (𝓞 B.KO),
          (((toHtData G Qf Gc PH Prw Pet).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN B.KO la ≤
        (G.del : ℝ) * Real.log G.del + 2 * ∑ k, WeightFamilies.meanLogSup B (G.th' k) +
        8 / 3 * (WeightFamilies.dimY D j : ℝ) * ((WeightFamilies.dimY D j : ℝ) + 4) * G.del * Prw * wL.size +
        2 * ((WeightFamilies.dimY D j : ℝ) + 4) * ((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size
    linarith
  · obtain ⟨hsN, hbN⟩ := heta trivial
    rw [hir, hg0, hDr, hδr, hG, hPH, hL, hPrw, hPet] at hbN
    have e : (fun la : HeightOneSpectrum (𝓞 B.KO) =>
          (toHtData G Qf Gc PH Prw Pet).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la) =
        fun la : HeightOneSpectrum (𝓞 B.KO) => (d.htOf hd hs).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la :=
      funext fun la => by rw [hN la]
    refine ⟨?_, ?_⟩
    · show Summable fun la : HeightOneSpectrum (𝓞 B.KO) =>
        (toHtData G Qf Gc PH Prw Pet).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la
      rw [e]; exact hsN
    · show (∑' la : HeightOneSpectrum (𝓞 B.KO),
          (toHtData G Qf Gc PH Prw Pet).Net la * Formalism.MainNotions.Gaps.HeightData.lN B.KO la) / (G.iet : ℝ) ≤
        (g0 D : ℝ) * (((WeightFamilies.dimY D j : ℝ) + 1) * G.del * (2 * Gc + 6 * PH) * wL.size +
          4 / 3 * (WeightFamilies.dimY D j : ℝ) * G.del * Prw * wL.size) + G.del * Pet
      rw [e]; exact hbN

section Ties

variable (d : Data B.KO ι Ω WT A) (hd : d.AxH 𝒜) (hs : d.S1)
    (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ)

def IlaTie : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Ila la ≤ (d.htOf hd hs).Ila la

def NetTie : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 B.KO), (toHtData G Qf Gc PH Prw Pet).Net la = (d.htOf hd hs).Net la

end Ties

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1
section
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def RegularityR2 (X : PJ D B P j) (E : PtExt X)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop) : Prop :=
  (∀ (wL wE : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (et : B.Cusp j wE)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (c : ℝ), 0 ≤ c → NoZero gens →
    (∀ la (y : X.Pt la), 0 ≤ X.vAt la y (X.inc wE et) ∧ (X.vAt la y (X.inc wE et) ≠ ⊤ →
      (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (X.vAt la y (X.inc wE et)).toReal : ℝ) : EReal))) →
    ∀ la (y' : E.Pt' la), 0 ≤ E.vAt' la y' (X.inc wE et) ∧ (E.vAt' la y' (X.inc wE et) ≠ ⊤ →
      (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤
        (((nus la : ℝ) + c * (E.vAt' la y' (X.inc wE et)).toReal : ℝ) : EReal))) ∧
  (∀ (wL : WeightFamilies.Wt D j) (n : ℕ) (gens : Fin n → B.Cusp j wL) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    NoZero gens →
    (∀ la (y : X.Pt la), (⨅ k, X.vAt la y (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal)) →
    ∀ la (y' : E.Pt' la), (⨅ k, E.vAt' la y' (X.inc wL (gens k))) ≤ ((nus la : ℝ) : EReal))

theorem iInf_span_eq {X : PJ D B P j} {wL : WeightFamilies.Wt D j} {n : ℕ} (g : Fin n → B.Cusp j wL)
    (la : HeightOneSpectrum (𝓞 B.KO)) (v : X.Forms → EReal) (hv0 : v 0 = ⊤)
    (hadd : ∀ F G, min (v F) (v G) ≤ v (F + G))
    (hsmul : ∀ (a : B.KO) F, a ≠ 0 → v (a • F) = (((vAdd la a : ℤ) : ℝ) : EReal) + v F)
    (hint : ∀ a : 𝓞 B.KO, (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO)) :
    (⨅ F ∈ Submodule.span (𝓞 B.KO) (Set.range g), v (X.inc wL F)) = ⨅ k, v (X.inc wL (g k)) := by
  apply le_antisymm
  · exact le_iInf fun k => iInf₂_le (g k) (Submodule.subset_span (Set.mem_range_self k))
  · refine le_iInf₂ fun F hF => ?_
    induction hF using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact iInf_le _ k
    | zero => simp [hv0]
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]; exact le_trans (le_min hx hy) (hadd _ _)
    | smul a x _ hx =>
      by_cases ha : (a : B.KO) = 0
      · have : a = 0 := by exact_mod_cast ha
        subst this; simp [hv0]
      · have hsm : X.inc wL (a • x) = (a : B.KO) • X.inc wL x := by
          rw [← map_smul]; congr 1; exact (algebraMap_smul B.KO a x).symm
        rw [hsm, hsmul _ _ ha]
        have h0 : (0 : EReal) ≤ (((vAdd la (a : B.KO) : ℤ) : ℝ) : EReal) := by
          exact_mod_cast hint a ha
        calc (⨅ k, v (X.inc wL (g k))) = 0 + ⨅ k, v (X.inc wL (g k)) := (zero_add _).symm
          _ ≤ _ := add_le_add h0 hx

def gd2Xplus {ka wL wF : WeightFamilies.Wt D j} {X : PJ D B P j} (G : GlobalFamilyData X ka wL wF) (E : PtExt X)
    (hM : IntAtExt X E) : GlobalFamilyData (xplus X E hM) ka wL wF :=
  ⟨G.N, G.w, G.del, G.th', G.rz, G.alz, G.th0, G.zc, G.rq, G.th, G.iet, G.et, G.mx⟩

theorem combBound_xplus {ka wL wF : WeightFamilies.Wt D j} (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E)
    (NoZero : ∀ {wL : WeightFamilies.Wt D j} {n : ℕ}, (Fin n → B.Cusp j wL) → Prop)
    (G : GlobalFamilyData X ka wL wF) (S : Scal B) (c : ℝ) (hc : 0 ≤ c) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hspan : Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL) (hNZ : NoZero G.w)
    (hint : ∀ (la : HeightOneSpectrum (𝓞 B.KO)) (a : 𝓞 B.KO), (a : B.KO) ≠ 0 → 0 ≤ vAdd la (a : B.KO))
    (hX : CombBound G S c nus) (hR2 : RegularityR2 X E NoZero) :
    CombBound (gd2Xplus G E hM) S c nus := by
  have dX : ∀ la (y : X.Pt la), X.depth S.sW wL la y = ⨅ k, X.vAt la y (X.inc wL (G.w k)) := by
    intro la y
    unfold PJ.depth
    rw [← hspan]
    exact iInf_span_eq G.w la (X.vAt la y) (X.vAt_zero la y) (X.vAt_add la y) (X.vAt_smul la y) (hint la)
  have dE : ∀ la (y : E.Pt' la), (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y (X.inc wL F)) =
      ⨅ k, E.vAt' la y (X.inc wL (G.w k)) := by
    intro la y
    rw [← hspan]
    exact iInf_span_eq G.w la (E.vAt' la y) (E.vAt'_zero la y) (E.vAt'_add la y) (E.vAt'_smul la y) (hint la)
  intro la y
  cases y with
  | inl y0 => exact hX la y0
  | inr y1 =>
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · have hc' : 0 ≤ c / (2 * (G.iet : ℝ)) := by positivity
      have := hR2.1 wL _ G.N G.w G.et nus _ hc' hNZ
        (fun la' y => by have h := (hX la' y).1 hj; rw [dX] at h; exact h) la y1
      show 0 ≤ E.vAt' la y1 (X.inc _ G.et) ∧ (E.vAt' la y1 (X.inc _ G.et) ≠ ⊤ →
        (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _)
      rw [dE]; exact this
    · have := hR2.2 wL G.N G.w nus hNZ (fun la' y => by have h := (hX la' y).2 hj; rw [dX] at h; exact h) la y1
      show (⨅ F ∈ X.WWc S.sW wL, E.vAt' la y1 (X.inc wL F)) ≤ _
      rw [dE]; exact this

section l2NormAlt

variable (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ)
    (h0 : ∀ j ka σ F, 0 ≤ N j ka σ F) (h1 : ∀ j ka σ F, N j ka σ F = 0 ↔ F = 0)
    (h2 : ∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F)
    (h3 : ∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G)
    (h4 : ∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

end l2NormAlt

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ThClassPinsRec
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open MvPolynomial Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def BadPin (bad q1 d cond : ℕ) : Prop := 2 ∣ bad ∧ q1 ∣ bad ∧ d ∣ bad ∧ cond ∣ bad

section Reps

variable {n : ℕ} {Tup : Type} (Cl' : Tup → Type)

def RepsCov (dδ : Tup → DeltaDat Xo c n) (bad : Tup → ℕ) (Lh : ∀ t, Cl' t → Submodule (𝓞 E) (Fin n → E))
    (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ) (gam : ∀ t, Cl' t → ℕ) : Prop :=
  ∀ t, RepsOK (l := (dδ t).l₂) (bad t) (La t) (Nc t) (gam t) ∧ LatPin (Lh t) (La t)

end Reps

section Io

variable {n : ℕ} {Ix : Type} [Fintype Ix] (emb : Ix → E →+* c.F) (lam : Ix → DomWeight n)

abbrev VVc : Type := ↥(Formalism.L2.DIV.VV c.F lam)


open Classical in
def rhoM (ga : Matrix (Fin n) (Fin n) E) : VVc c lam →ₗ[c.F] VVc c lam :=
  if h : IsUnit ga.det then Formalism.L2.DIV.rhoVr emb lam (Matrix.nonsingInvUnit ga h) else 0

def nab0M : Submodule (𝓞 c.F) (VVc c lam) := Formalism.L2.DIV.nabAtr emb lam (stdLat E n)

def hwOK (hw : VVc c lam) : Prop :=
  (hw : Formalism.L2.DIV.Pol c.F Ix n) = Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal c.F n (lam τ)

def IoLFRec (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam) : Prop :=
  hwOK c lam hw ∧ ∃ cga : Matrix (Fin n) (Fin n) E → c.F,
    IoLF c a io (rhoM c emb lam) cga (nab0M c emb lam) hw (pG (Dw := Dw) c a n)

end Io

section Dat

variable {n : ℕ}

variable {Tup : Type} (Cl' : Tup → Type)

def WPin (dδ : Tup → DeltaDat Xo c n) (φ : ∀ t, (Fin n → LevQc Dw (dδ t).l₂) → c.F)
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F) : Prop :=
  ∀ t (k : Cl' t) (q : Fin n → LevQ Dw (dδ t).l₂),
    (dδ t).eF (w t k q) = phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q

def CovPin (dδ : Tup → DeltaDat Xo c n) : Prop :=
  ∀ t, (dδ t).IsLev ∧ (dδ t).l₂.A = 1 ∧ ∃ _ : StarRing (𝓞 E), IsNab (dδ t).Xo₂ (dδ t).c₂ (dδ t).nab₂

end Dat

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.UnifGen
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem scal_mul {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem gen_unit {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul, mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one, one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

end Gen

end Formalism.L2.Pj
end
end

