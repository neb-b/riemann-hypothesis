module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormConjugatesOverIdealClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateCmValueCharacterPermutedWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBranchingConstantBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfSize

theorem bigN_le {D : D7} {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : (bigN D : ℝ) ≤ 10 * large₂.sc.b := by
  obtain ⟨-, -, hf, hm, -, hb, -⟩ := hs
  have hd : 1 ≤ D.host.d := D.host.hyp.2.1.one_lt.le
  have hm1 : 1 ≤ D.R.m := by omega
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hf
  have hN1 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
  have key : bigN D ≤ 10 * (D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d) := by
    have e1 : D.R.N D.R.m ≤ D.R.N D.R.m ^ 2 := Nat.le_self_pow (by norm_num) _
    have e2 : D.R.m * D.R.N D.R.m ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d := by
      calc D.R.m * D.R.N D.R.m = D.R.m * 1 * D.R.N D.R.m * 1 := by ring
        _ ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d := by gcongr
    have e3 : bigN D ≤ 10 * (D.R.m * D.R.N D.R.m) := by
      have hk := D.R.m_add_three_le_k
      have s1 : bigN D ≤ D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 6) + 1) := by
        simp only [bigN, sLen, Ranks.r]; gcongr; omega
      have a1 : D.R.k ≤ D.R.m * D.R.k := Nat.le_mul_of_pos_left _ (by omega)
      have a2 : D.R.m * D.R.t ≤ D.R.m * (D.R.m * D.R.t) := Nat.le_mul_of_pos_left _ (by omega)
      have a3 : D.R.m ≤ D.R.m * D.R.m := Nat.le_mul_of_pos_left _ (by omega)
      refine s1.trans ?_
      simp only [Ranks.N]
      nlinarith
    omega
  have : (bigN D : ℝ) ≤ 10 * ((D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at this
  linarith

theorem log_prod_le {ι : Type} [Fintype ι] (a : ι → ℝ) (c : ℝ) (h0 : ∀ i, 0 ≤ a i) (hc : 0 ≤ c)
    (h : ∀ i, Real.log (a i) ≤ c) : Real.log (∏ i, a i) ≤ Fintype.card ι * c := by
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, Real.log_zero]
    positivity
  · push_neg at hz
    rw [Real.log_prod (fun i _ => hz i)]
    calc ∑ i, Real.log (a i) ≤ ∑ _i : ι, c := Finset.sum_le_sum fun i _ => h i
      _ = Fintype.card ι * c := by simp

end GlobalTheory.InfSize


open GlobalTheory.InfSize in
theorem GlobalTheory.InfSize.main : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ Real.log (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
          (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ K0 * D.R.f * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
  obtain ⟨K1, hK1⟩ := _root_.GlobalTheory.InfSize.WtSize.wt_top_abs_le
  set c : ℝ := |K1| + 10 with hc
  set c2 : ℝ := Real.log (6 * c) + 1 with hc2
  refine ⟨0, fun CF _ => ⟨5 * c * c2, fun ε => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hAt => ?_⟩⟩⟩
  have hc10 : 10 ≤ c := by rw [hc]; linarith [abs_nonneg K1]
  have hc2p : 1 ≤ c2 := by
    rw [hc2]; have : 0 ≤ Real.log (6 * c) := Real.log_nonneg (by linarith)
    linarith

  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hlb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  refine ⟨hb1, ?_⟩
  have hlog1 : 1 ≤ Real.log large₂.sc.b := hlb ▸ hL

  have hcg : ch.sc.cGap = 1 := by rw [hAt]
  have hw := hK1 D large₂ hS.size ch.G hcg
  have hNb := bigN_le hS.size
  have hrk : (ch.G.V (.top D.R.m)).rank ≤ bigN D := GlobalTheory.DefRank.rank_le_bigN ch.G (.top D.R.m) (le_refl D.R.m)
  have hrkR : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ bigN D := by exact_mod_cast hrk
  set B : ℝ := c * large₂.sc.b with hB
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  have hlogB : Real.log (6 * B) ≤ c2 * Real.log large₂.sc.b := by
    rw [hB, ← mul_assoc, Real.log_mul (by positivity) (by positivity), hc2]
    have : 0 ≤ Real.log (6 * c) := Real.log_nonneg (by linarith)
    nlinarith
  have hNB : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ B := by
    rw [hB]; nlinarith
  have hwB : ∀ τ i, |(((wt ch.G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ B := fun τ i => by
    refine (hw τ i).trans ?_
    rw [hB]; exact mul_le_mul_of_nonneg_right (by rw [hc]; linarith [le_abs_self K1]) (by linarith)
  have hτ : ∀ τ, Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
      (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
    intro τ
    refine (_root_.GlobalTheory.BranchBound.log_brBd_sq_le _ _ _ B hB1 hNB (hwB τ)).trans ?_
    have hl6 : 0 ≤ Real.log (6 * B) := Real.log_nonneg (by linarith)
    calc 5 * ((ch.G.V (.top D.R.m)).rank : ℝ) * B * Real.log (6 * B) ≤ 5 * (bigN D : ℝ) * B * Real.log (6 * B) := by
          gcongr
      _ ≤ 5 * (bigN D : ℝ) * B * (c2 * Real.log large₂.sc.b) := by gcongr
      _ = 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by rw [hB]; ring
  have h0 : 0 ≤ 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine (log_prod_le _ _ (fun τ => sq_nonneg _) h0 hτ).trans (le_of_eq ?_)
  rw [D.what₂.card_Tau]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundSemiPosNefOnFibres
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LowerNef

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), NefFib L → L.SemiPos D → L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (a / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
  intro hAr hHS k _ X _ p D hX L N a hNef hSP hSI ε hε
  obtain ⟨P, b, s, t, c, hPL, hG, hGen, hReg, hLe⟩ := _root_.GlobalTheory.HSNef.exists_good_pair_twist hAr hHS k X p D hX L N
  subst hPL
  have hlow := _root_.GlobalTheory.HSLowerTwist.main hAr hHS k X p D hX P b s t hG c hGen hReg hNef hSP a hSI ε hε
  filter_upwards [hlow] with m hm
  obtain ⟨h1, h2, -⟩ := Pair.rep_base k X p P
  have hRep : P.Rep (m : ℤ) (-(c : ℤ)) ((P.L.pow m).tens ((P.A.pow c).dual)) := by
    have := Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_pow k X p P _ _ _ m h1)
      (Pair.rep_dual k X p P _ _ _ (Pair.rep_pow k X p P _ _ _ c h2))
    simpa using this
  have hE := SmallBall.encard_eq_Bl P hRep ((P.L.pow m).tens ((P.A.pow c).dual)).smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have hle := _root_.GlobalTheory.HSNef.LeCard.encard_smallSec_le k X p _ _ ((_root_.GlobalTheory.HSNef.le_tens_isometric_trans_shift k X p _ _ (P.L.pow m)).1 hLe)
  have hfin := _root_.GlobalTheory.SmallFin.smallSec_finite k X p D hX ((P.L.pow m).tens N)
  have hBle : (P.Bl m (-c) 1).encard ≤ ((P.L.pow m).tens N).smallSec.encard := hE ▸ hle
  have hBfin : (P.Bl m (-c) 1).Finite :=
    Set.finite_of_encard_le_coe (hBle.trans_eq hfin.cast_ncard_eq.symm)
  have hone : (1 : ℕ∞) ≤ (P.Bl m (-c) 1).encard :=
    hE ▸ Set.one_le_encard_iff_nonempty.2 ⟨_, ((P.L.pow m).tens ((P.A.pow c).dual)).zero_mem_smallSec⟩
  have hc1 : 1 ≤ (P.Bl m (-c) 1).ncard := by
    have := hBfin.cast_ncard_eq ▸ hone
    exact_mod_cast this
  have hc2 : (P.Bl m (-c) 1).ncard ≤ ((P.L.pow m).tens N).smallSec.ncard := by
    have := hBfin.cast_ncard_eq ▸ hfin.cast_ncard_eq ▸ hBle
    exact_mod_cast this
  refine hm.trans ?_
  unfold Pair.lc
  exact Real.log_le_log (by exact_mod_cast hc1) (by exact_mod_cast hc2)

end GlobalTheory.HSNef.LowerNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.KleimanNef

theorem htNef_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D := by
  intro hA hAmp hSP
  suffices H : ∀ D : ℕ, ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
      IsArithVar p D → ∀ C : HermLB p, C.IsNef D → HtNef C D by
    intro k _ X _ p D hX C hC
    exact H D k X p hX C hC
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro k _ X _ p hX C hC
  have hng : ∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h →
      ∀ z, z ≠ genericPoint X → 0 ≤ h z := by
    intro C h hC hh z hz
    by_cases hcz : CharZero (X.residueField z)
    swap
    · exact _root_.GlobalTheory.VertHeight.height_nonneg_of_vertical k X p D hX C h (nefFib_of_isNef hC) hh z hcz
    obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
    rcases hX.vertical_or_horizontal i with ⟨ℓ, hℓ, ⟨alg⟩⟩ | ⟨hc, e, he⟩
    · exfalso
      have hcz' : CharZero (Z.residueField (genericPoint Z)) :=
        (RingHom.charZero_iff (i.residueFieldMap (genericPoint Z)).hom.injective).1 hcz
      let f : ZMod ℓ →+* Z.residueField (genericPoint Z) :=
        (Z.evaluation ⊤ (genericPoint Z) trivial).hom.comp (algebraMap (ZMod ℓ) Γ(Z, ⊤))
      have h2 := congrArg f (ZMod.natCast_self ℓ)
      rw [map_natCast, map_zero] at h2
      exact hℓ.out.ne_zero (by exact_mod_cast h2)
    · have hZ : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc he
      have hamb := GlobalTheory.MixHt.isAmb_of_isArithVar hX
      obtain ⟨-, -, -, -, hcl, hgd⟩ := GlobalTheory.MixHt.hasDim_basic k X p hamb
      have hd : GlobalTheory.MixHt.HasDim (i (genericPoint Z)) (e + 1) := (hcl Z i _ _).2 ((hgd Z _).2 he)
      have hco := GlobalTheory.DimCoheight.coheight_add_eq k X p hamb (D + 1) hX.dim_eq _ _ hd
      have hne : Order.coheight (i (genericPoint Z)) ≠ 0 := by
        intro h0
        rw [Order.coheight_eq_zero] at h0
        apply hz
        have h1 : i (genericPoint Z) ≤ genericPoint X := genericPoint_specializes _
        exact (Specializes.antisymm (h0 h1) (genericPoint_specializes _)).eq
      have heD : e < D := by
        by_contra hle
        push_neg at hle
        obtain ⟨c, hc'⟩ : ∃ c : ℕ, Order.coheight (i (genericPoint Z)) = c := by
          refine ⟨(Order.coheight (i (genericPoint Z))).toNat, (ENat.coe_toNat fun ht => ?_).symm⟩
          rw [ht, top_add] at hco
          exact ENat.top_ne_coe _ hco
        rw [hc'] at hco hne
        have : c + (e + 1) = D + 1 := by exact_mod_cast hco
        have : c ≠ 0 := by exact_mod_cast hne
        omega
      have hnef : (C.pull i rfl).IsNef e := _root_.GlobalTheory.HSNef.isNef_pull hA hSP k X Z p (i ≫ p) D e hX hZ i rfl C hC
      exact (ih e heD k Z (i ≫ p) hZ _ hnef).2 _ (hh.restrict hX i rfl) (genericPoint Z)
  refine ⟨hC.semiPos, fun h hh x => ?_⟩
  by_cases hx : x = genericPoint X
  · subst hx
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have := ((hh.isNef_iff hX).1 hC).2 X (𝟙 X) (by simpa using hX.dim_eq)
      simpa using this
    · exact _root_.GlobalTheory.KleimanStep.selfInter_nonneg hA hAmp k X p D hX hD hng C _ hC ⟨h, hh, rfl⟩
  · exact hng C h hC hh x hx

end GlobalTheory.KleimanNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransport
section
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open scoped nonZeroDivisors

namespace GlobalTheory.BetaArchPf

theorem host_d_mod' (D : Formalism.BasicNotions.D7) : D.host.d % 4 = 3 := by
  have := D.host.hyp.2.2.2.1; omega

theorem toric_eq_L {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E} {Λ : ℂ → ℂ} (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s)
    (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ) (hΛ : IsHeckeL χ Λ) : IsToricSum φ s κ (condQ 𝔣 ∅) χ (Λ s) := by
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 ∅ χ
    (fun _ => P₀) Λ hU hs hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rwa [Finset.filter_empty, Finset.prod_empty, mul_one] at t1

theorem condQ_empty {E : Type} [Field E] [NumberField E] (𝔣 : Ideal (OF E)) : condQ 𝔣 ∅ = 𝔣 := by
  simp [condQ]

end GlobalTheory.BetaArchPf

namespace GlobalTheory.SqTop


open GlobalTheory.BetaArchPf in
theorem betaArch_of_transport : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LBound → TorEx → BetaArch := by
  intro hTr hFD hLB hTE
  obtain ⟨CF1, hF1⟩ := hFD
  obtain ⟨CF2, hL2⟩ := hLB
  obtain ⟨CF3, hT3⟩ := hTE
  refine ⟨max CF1 (max CF2 CF3), fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, hF⟩ := hF1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, hL⟩ := hL2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C3, x3, hT⟩ := hT3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  obtain ⟨Cx, x4, hS⟩ := _root_.GlobalTheory.SizesArch.sizes ε
  refine ⟨C2 + Cx, max (max x1 x2) (max x3 x4), fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => ?_⟩
  have hx1 : x1 ≤ large₂.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ large₂.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : x3 ≤ large₂.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : x4 ≤ large₂.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  intro i j s hs1 hs2 c y Λ hy hΛ
  obtain ⟨iCM, iAb, hFD, hbase, -⟩ := hF C1 le_rfl D large₂ hε hx1 hR T Lc μ₀ hμ G
  have TE := hT C3 le_rfl D large₂ hε hx3 hR T Lc μ₀ hμ G i j s hs1 hs2 c
  have LB := hL (C - Cx) (by linarith) D large₂ hε hx2 hR T Lc μ₀ hμ G i j s hs1 hs2
  have SZ := hS D large₂ hε hx4 hR i j s hs1 hs2

  obtain ⟨x, hxT, hx0, -, hxalg⟩ := TE
  have hyx : y = x := hy.2.unique hxT.2
  subst hyx
  have hd4 : 4 < D.host.d := hFD.2.1
  obtain ⟨K, hK2, hKd, φK, hφK, hc, hLat⟩ := _root_.GlobalTheory.QuadInHost.exists_quadField D.host.d (cmPhi D) hFD (host_d_mod' D) Λ hΛ
  obtain ⟨tt, 𝔞, Λσ, hσ, hEq, hAll⟩ := hTr K D.host.d hd4 hK2 hKd φK Λ hLat
  haveI := iCM
  haveI : IsGalois ℚ D.host.E := inferInstance
  have hU : UnramFin D.host.E := hFD.2.2.1
  have hCM : IsCMType (cmPhi D) := hFD.2.2.2.2.2.2.1
  have hcard : 2 ≤ Fintype.card D.what₂.Tau := hFD.2.2.2.2.2.1
  have hκ : ∀ τ, 1 ≤ kap D 1 i j s τ := fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D 1 i j τ hs2).2
  have hTF := hAll D.host.E hU D.what₂.Tau (cmPhi D) hcard hCM hφK s (kap D 1 i j s) (condF G.pl) hs1 hκ hbase
  have hVS : IsValSum (cmPhi D) s (kap D 1 i j s) (condF G.pl) ∅ (fam G μ₀ i j c) y :=
    ⟨fun _ h => absurd h (Finset.notMem_empty _), hy.1, (condQ_empty (condF G.pl)).symm ▸ hy.2⟩
  obtain ⟨halg, hconj⟩ := hTF.1 ∅ _ y hVS
  set M : ℕ := 2 * s * Fintype.card D.what₂.Tau + 2 * ∑ τ, kap D 1 i j s τ with hM
  set β := beta D.host.E D.host.d s (kap D 1 i j s) Λ y with hβ
  have hC0 : 0 < C0 D.host.E D.host.d (2 * s) (kap D 1 i j s) := cmValueConst_pos _ (by omega) (by omega) _
  have hβ0 : β ≠ 0 := by
    rw [hβ, beta_eq]
    exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (by exact_mod_cast hC0.ne') hx0)) (pow_ne_zero _ (latDisc_ne_zero _))
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by omega)
  let Fσ : (ℂ ≃+* ℂ) → ℝ := fun σ => 12 * Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) +
    12 * bTH D (C - Cx) large₂.sc.x large₂.sc.b -
      (M : ℝ) * Real.log (nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (Λσ σ)‖)
  have hFcl : ∀ σ σ', Fixes φK σ → Fixes φK σ' → ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') → Fσ σ = Fσ σ' := by
    intro σ σ' h h' hcl
    simp only [Fσ]
    rw [GlobalTheory.T.fractionalIdealNorm_pow_six_mul_discriminant_class_invariant φK hK2 hc (𝔞 σ) (𝔞 σ') (Λσ σ) (Λσ σ') (hσ σ h).2.1 (hσ σ' h').2.1 hcl]
  have hB : ∀ σ, Fixes φK σ → Real.log ‖σ β‖ ≤ Fσ σ := by
    intro σ hσf
    obtain ⟨π, χ', hw, hcc, hv'⟩ := _root_.GlobalTheory.ConjValChar.exists_conj_valChar φK (cmPhi D) s (kap D 1 i j s) (condF G.pl) (fam G μ₀ i j c) σ
      hCM hφK hc hσf hy.1
    obtain ⟨Λ', hΛ'⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf D.host.E D.what₂.Tau (cmPhi D) _ χ' hCM hv'.1
      hv'.2.2.1 ⟨τ0, by have := hκ (π τ0); simp only [Function.comp]; omega⟩
    have hT' := toric_eq_L hU hCM hs1 hbase hv' hΛ'
    have hlog : Real.log ‖Λ' s‖ ≤ bTH D (C - Cx) large₂.sc.x large₂.sc.b := LB π χ' Λ' hv' hΛ'
    have h3 := ((hconj σ hσf (kap D 1 i j s ∘ π) hw χ' (Λ' s) ⟨hcc, hT'⟩).2)
    have hσβ : 0 < ‖σ β‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hβ0)
    have hn0 : 0 ≤ nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) := by
      unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
    have hN : 0 < nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc (Λσ σ)‖ :=
      mul_pos (pow_pos (lt_of_le_of_ne hn0 (nrm_ne_zero _).symm) 6) (norm_pos_iff.2 (latDisc_ne_zero _))
    rw [h3] at hσβ ⊢
    have hA : 0 < C0 D.host.E D.host.d (2 * s) (kap D 1 i j s) * ‖Λ' s‖ := by
      rcases (mul_nonneg hC0.le (norm_nonneg (Λ' s))).lt_or_eq with h | h
      · exact h
      · rw [← h] at hσβ; simp at hσβ
    have hL0 : 0 < ‖Λ' s‖ := pos_of_mul_pos_right hA hC0.le
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv, Real.log_pow,
      Real.log_mul hC0.ne' hL0.ne']
    simp only [Fσ, hM]
    push_cast
    linarith
  obtain ⟨rep, hrep, hmain⟩ := _root_.GlobalTheory.GalMean.galmean φK (jLat Λ) 𝔞 β Fσ hK2 hc hEq halg hβ0 hFcl hB
  have hmean := _root_.GlobalTheory.ClassMeanDisc.classMean_log_norm_disc D φK hK2 hKd hd4 (fun c => 𝔞 (rep c)) (fun c => Λσ (rep c)) (fun c => (hrep c).2)
    (fun c => (hσ _ (hrep c).1).2.1)
  have hh : (0 : ℝ) < classNumber K := by
    rw [show (classNumber K : ℝ) = (Fintype.card (ClassGroup (𝓞 K)) : ℝ) from rfl]
    exact_mod_cast Fintype.card_pos
  have hsum : (∑ c, Fσ (rep c)) / classNumber K = 12 * Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) +
      12 * bTH D (C - Cx) large₂.sc.x large₂.sc.b - (M : ℝ) * ((∑ c, Real.log (nrm (𝔞 (rep c) : FractionalIdeal (𝓞 K)⁰ K) ^ 6 *
        ‖latDisc (Λσ (rep c))‖)) / classNumber K) := by
    simp only [Fσ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    rw [show (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = classNumber K from rfl]
    field_simp
  have hwt : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) = (M : ℝ) := by
    simp [hM, Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK]
  have hX : (∑ c, Fσ (rep c)) / classNumber K ≤ 12 * bTH D C large₂.sc.x large₂.sc.b := by
    rw [hsum, hmean, ← large₂.logDerivative_at_one_eq]
    have h2π : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
    have hγ : 0 ≤ Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
    have hMnn : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hdl : large₂.logDerivativeAtOne ≤ |large₂.logDerivativeAtOne| := le_abs_self _
    have hbt : bTH D C large₂.sc.x large₂.sc.b = bTH D (C - Cx) large₂.sc.x large₂.sc.b + bTH D Cx large₂.sc.x large₂.sc.b := by
      unfold bTH; ring
    rw [hwt] at SZ
    nlinarith [mul_nonneg hMnn h2π.le, mul_nonneg hMnn hγ, mul_le_mul_of_nonneg_left hdl hMnn]
  calc _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg _)

end GlobalTheory.SqTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRanksArithmeticLargeGrids
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRankSize

theorem bot_arith (D : D7) (i j : ℕ) :
    Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧
      1 < SqNum.botSmall D i j := by
  have hk := D.R.k_even
  have hm := D.R.m_even
  have ht := D.R.t_odd
  have h3 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  rw [Nat.even_iff] at hk hm
  rw [Nat.odd_iff] at ht
  simp only [SqNum.botBig, SqNum.botSmall, rankV, sLen, Formalism.BasicNotions.Ranks.r]
  have e1 : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
  have e2 : (i + 1) * (D.R.k + D.R.m - 1 + 6) = i * (D.R.k + D.R.m - 1 + 6) + (D.R.k + D.R.m - 1 + 6) := by ring
  rw [e1, e2]
  generalize j * D.R.t = A
  generalize i * (D.R.k + D.R.m - 1 + 6) = B
  rw [Nat.even_iff]
  omega

theorem bottom_ranks : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro i j
  exact bot_arith D i j

end GlobalTheory.BotRankSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfPullbackNmulCoboundaryStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coboundary_of_pullback_nmul_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ → cob1 μ B = pull2 (nmul μ p) κ → c.ev 1 B = 0 → ∃ s, κ = cob1 μ s := by
  first | exact @GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | exact GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' | (intros; apply GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' <;> assumption)
end

