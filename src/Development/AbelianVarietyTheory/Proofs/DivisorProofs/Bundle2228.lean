module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerTriangularTwoBlockMulWeylTwoBlockEqTransvec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumEqZeroOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0108
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp.VanishingBound

theorem keySec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) : Nonempty (GlobalTheory.ShFam.KeySec Y.d.Xo₂ Y.d.c₂) := by
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf σ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact GlobalTheory.KeyCover.nonempty_keySec_of_family _ _ _ _ _ _ σ hσ ee F (by omega) hY.geo

theorem isSec (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (la : AllWt.Weight (T.Q.Dw j)) (f : Rul Y.d.Xo₂ Y.d.c₂)
    (hf : f ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k) :
    ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k) := by
  have hU := hY.unf σ hσ
  by_cases hdec : ∀ (τ : D.host.E →+* ℂ) (i j' : ℕ), i ≤ j' → j' < (T.Q.Dw j).mult τ →
      (wtOf (T.Q.Dw j) la 0).1 (τ, j') ≤ (wtOf (T.Q.Dw j) la 0).1 (τ, i)
  · by_cases hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q
    · exact _root_.GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU _ _ _ _ _ _ σ _ (Y.U σ) (keySec D T j Y e o hY σ hσ) hσ hU hpq _
        (AllWt.even_wtOf la 0) hdec f hf k
    · have hp : (T.Q.Dw j).p = 0 := by omega
      have hq : (T.Q.Dw j).q = 0 := by omega
      have hG : wtOf (T.Q.Dw j) la 0 = wtZ (fun _ => 0) 0 := by
        refine Prod.ext (funext fun x => ?_) ?_
        · simp only [wtOf, wtZ, hp, hq]
          split_ifs <;> first | (exfalso; omega) | simp
        · simp [wtOf, wtZ]
      rw [hG, AllWt.modelWt_wtZ]
      have hf' : f ∈ sec Y.d.Xo₂ Y.d.c₂ (fun _ => 0) 0 := by
        rw [← AllWt.secZ_nat, ← AllWt.exZ_wtZ, ← hG]
        exact hf
      exact hU.2.2.2.2.1 _ _ ⟨fun τ => fun a b _ => le_refl _, ⟨0, rfl⟩⟩ f hf' k
  · have hex : ∃ (τ : D.host.E →+* ℂ) (m : ℕ) (hm : m + 1 < (T.Q.Dw j).mult τ),
        (wtOf (T.Q.Dw j) la 0).1 (τ, m) < (wtOf (T.Q.Dw j) la 0).1 (τ, m + 1) := by
      by_contra hne
      push_neg at hne
      apply hdec
      intro τ i j' hij hj'
      revert hj'
      induction j', hij using Nat.le_induction with
      | base => intro _; exact le_refl _
      | succ n hn ih => intro hj'; exact (hne τ n hj').trans (ih (by omega))
    obtain ⟨τ, m, hm, hlt⟩ := hex
    have h0 : f = 0 := GlobalTheory.NonDomVanish.eq_zero_of_lt hf τ ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl hlt
    subst h0
    rw [map_zero]
    exact ⟨differentiableOn_const 0, fun x _ b _ => by simp, fun γ _ x _ => by simp⟩


open scoped LaurentSeries in
theorem fjZero (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂)
    (la : AllWt.Weight (T.Q.Dw j)) (s) (hs : s ∈ vanBd TF.X Z la)
    (f : GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0))
    (hfs : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ GlobalTheory.AllWt.suppOn Z) (hfsec : sec₀ TF.X Z _ f = H0.restr le_top s)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k)
    (hsec : ((Y.U σ).X k).IsSec (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) (rdU (Y.U σ) f k))
    (ξ) (hξ : ((Y.U σ).X k).IsIso ξ) (x) (hx : x ∈ ((Y.U σ).X k).dom) :
    ((Y.U σ).X k).fj (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k) ξ 0 (rdU (Y.U σ) f k) x = 0 := by
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hU := hG.unf σ hσ
  letI : Algebra Y.d.c₂.F ℂ⸨X⸩ := (GlobalTheory.ArcId.cstL.comp σ).toAlgebra
  have halg : ∀ x : Y.d.c₂.F, algebraMap Y.d.c₂.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)) :=
    fun _ => rfl
  obtain ⟨y, T₀, s', d, hbd, hd, hw⟩ :=
    GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) halg hσ hU k ξ hξ x hx _ _ TF.Y
  have hc : (algebraMap (PowerSeries ℂ) ℂ⸨X⸩).comp ((PowerSeries.C (R := ℂ)).comp σ) = algebraMap Y.d.c₂.F ℂ⸨X⸩ :=
    RingHom.ext fun t => (halg t).symm
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 none = 0 := rfl
  have hcoef : ∀ m ≤ (0:ℤ), (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff m = 0 := by
    intro m hm
    by_cases hZ : GlobalTheory.AllWt.LiesOn Z y
    · obtain ⟨v, hv, hval⟩ :=
        GlobalTheory.CuspOnTor.evR_mem_maximalIdeal _ _ _ _ _ _ TF.Y TF.X Z la s hs f hfsec (PowerSeries ℂ) ℂ⸨X⸩ _ y hc hZ hbd
      rw [hval]; exact GlobalTheory.CuspFrom.coeff_eq_zero hv hm
    · rw [hfs ℂ⸨X⸩ y ((GlobalTheory.AllWt.liesOff_iff Z y).2 hZ)]; rfl
  exact _root_.GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line _ _ _ _ _ ξ x s' d T₀ (fun j => (evR Y.d.Xo₂ Y.d.c₂ f.1 y).coeff j) hsec
    (GlobalTheory.CuspFrom.freqNonneg _ hf1 hsec) hξ hx hd hcoef fun w hw' => ⟨(hw w hw').1, (hw w hw').2 _ hex _ f.2⟩

end GlobalTheory.HSApp.VanishingBound

namespace GlobalTheory.HSApp


open GlobalTheory.HSApp.VanishingBound in
theorem vanBd_le_space : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), vanBd TF.X Z la ≤ space TF.X Z Y.U la := by
  intro D T j Y e o hG hf Z TF la s hs
  obtain ⟨f, hfZ, hfs⟩ := _root_.GlobalTheory.CompHS.exists_suppOn_sec₀_eq _ _ _ _ _ _ _ TF.X Z (GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) (H0.restr le_top s)
  have hsec := isSec D T j Y e o hG la f.1 f.2
  have hf1 : 1 < Module.finrank ℚ D.host.E / 2 := by omega
  have hcusp : (f : Rul Y.d.Xo₂ Y.d.c₂) ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0) := by
    refine ⟨GlobalTheory.AllWt.mem_cuspW.2 ⟨f.2, fun σ hσ => holCusp_mem_holSub _ _ fun k => ?_⟩, hfZ⟩
    have h0 := fjZero D T j Y e o hG hf Z TF la s hs f hfZ hfs σ hσ k (hsec σ hσ k)
    have h3 := (GlobalTheory.FJZero.mem_SS_of_isModerate _ _ _ (hsec σ hσ k) (GlobalTheory.CuspFrom.isModerate _ hf1 (hsec σ hσ k)) h0).1.2
    exact ⟨⟨hsec σ hσ k, h3⟩, fun ξ hξ x hx => h0 ξ hξ x hx⟩
  exact ⟨⟨f.1, hcusp⟩, hfs⟩

end GlobalTheory.HSApp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.HodgeGapBounds

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}

theorem bar_lt (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega

theorem one_le_gap_uMinus (P : WtPar Dw) (τ : Psi H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q)
    (hs : StrictAnti (P.u₁ τ)) : 1 ≤ gap (P.uMinus τ) (Dw.p - 1) := by
  have hk := bar_lt hp hq
  have h1 := P.gap_u₁ τ hk
  have hT : 0 < P.T₁ := by unfold WtPar.T₁; positivity
  have hg : 1 ≤ gap (P.u₁ τ) (Dw.p - 1) := by
    rw [gap, dif_pos hk]
    have := hs (show (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p - 1 + 1, hk⟩ from by
      rw [Fin.mk_lt_mk]; omega)
    omega
  rw [h1, Int.le_ediv_iff_mul_le hT, one_mul] at hg
  have hkap : gap (FlagTan.kap Dw τ) (Dw.p - 1) = 2 * ((Dw.p : ℤ) + Dw.q) - 2 := by
    simp only [gap, dif_pos hk, FlagTan.kap, Fin.val_mk]
    have := Nat.cast_sub (R := ℤ) hp
    split_ifs <;> push_cast at * <;> omega
  have hsub : gap ((P.uMinus - FlagTan.kap Dw) τ) (Dw.p - 1) =
      gap (P.uMinus τ) (Dw.p - 1) - gap (FlagTan.kap Dw τ) (Dw.p - 1) := by
    simp only [gap, dif_pos hk, Pi.sub_apply]; ring
  have hT1 : 1 ≤ P.T₁ := hT
  omega

theorem laOf_add_smul (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (c0 s : ℤ) :
    laOf Dw a n + s • hodgeWt Dw =
      uMinus Dw a n kc c0 + (s + c0) • hodgeWt Dw + FlatLine.parWt Dw (anchor Dw a n kc) := by
  rw [← uWt_add_anchor Dw a n kc]
  simp only [uMinus, add_smul]
  abel

theorem gap_add_smul_hodge (v : AllWt.Weight Dw) (x : ℤ) (w : Psi H → ℤ) (τ : Psi H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) :
    gap ((v + x • hodgeWt Dw + FlatLine.parWt Dw w) τ) (Dw.p - 1) = gap (v τ) (Dw.p - 1) + x := by
  have hk := bar_lt hp hq
  simp only [gap, dif_pos hk, Pi.add_apply, Pi.smul_apply, hodgeWt, CompHt.barWt, FlatLine.parWt, Fin.val_mk, smul_eq_mul]
  split_ifs <;> first | omega | ring

theorem antitone_add_par (v : AllWt.Weight Dw) (w : Psi H → ℤ) (τ : Psi H) (h : Antitone (v τ)) :
    Antitone ((v + FlatLine.parWt Dw w) τ) :=
  fun _ _ hab => add_le_add (h hab) le_rfl

end Weights

end GlobalTheory.CovTop.HodgeGapBounds

namespace GlobalTheory.CovTop.HodgeGapBounds

end GlobalTheory.CovTop.HodgeGapBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterSizeBounds
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.ZedSz

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem bar_gap (p : PtAt ex Csz) (i : Fin D.R.m) (P : ParameterChoice' D L) (hi : (i : ℕ) + 1 < D.R.m) (τ : Psi p.T.Q.H)
    (a b : Fin ((dat p i).p + (dat p i).q)) (hab : (b : ℕ) = a + 1) (hb : (b : ℕ) = (dat p i).p) :
    LevelStarExponents.h0 L ≤ ((uW p i τ a - uW p i τ b : ℤ) : ℝ) := by
  obtain ⟨t, ht⟩ := WtShape.exists_tau p τ
  have e1 := WtShape.dat_p p i
  have hd : ((uW p i τ a - uW p i τ b : ℤ) : ℝ) = WtShape.sgR D t a - WtShape.sgR D t (a + 1) - 1 +
      if (a : ℕ) + 1 = D.R.k + i then (D.R.r : ℝ) else 0 := by
    rw [Int.cast_sub, WtShape.uW_real p i τ t ht, WtShape.uW_real p i τ t ht, hab, ← WtShape.entR_step]; ring
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have h1 := WtShape.sgR_step_low D L P t a (by omega) (by omega)
  rw [if_pos (by omega)] at hd
  have c6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast WtShape.six_le_r D.R
  linarith

abbrev wp (p : PtAt ex Csz) (i : Fin D.R.m) (PP : ℝ) : WtPar (dat p i) :=
  ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩

theorem zed_at (p : PtAt ex Csz) (i : Fin D.R.m) (P : ParameterChoice' D L) (T : ParamsT D L P) (A M C1 : ℝ)
    (hS : SizeAt p i T.PP C1) (hq : ∀ u1, Quo p i T.PP u1 → u1 = (wp p i T.PP).u₁)
    (hsa : ∀ τ, StrictAnti ((wp p i T.PP).u₁ τ)) (hH : HostNum D L T.PP A M) (hW : WtNum p i T.PP)
    (hi : (i : ℕ) + 1 < D.R.m) :
    zed p i T.PP (wp p i T.PP).u₁ * (T.PP * kap p i) ≤ L.sc.b / 2 := by
  obtain ⟨hb1, -, -, -, -, hbk, hquo⟩ := hS
  obtain ⟨u0, hu0⟩ := (hquo hi).1
  have hQ : Quo p i T.PP (wp p i T.PP).u₁ := hq u0 hu0 ▸ hu0
  obtain ⟨h0', S, eta, -, -, -, -, -, hHyp⟩ := hW.hyp hi
  have hDv : (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).IsDiv := (quo_iff p i T.PP h0' S eta _).1 hQ
  have hY : (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).Hyp := hHyp _
  have hDp : GlobalTheory.CompHt.dimFlag (dat p i) = T.Dp := hW.dim.trans T.Dp_eq.symm
  have hlen : lenT p i T.PP ≤ T.TO := by
    unfold lenT; rw [hDp]; exact Nat.ceil_le.2 (WtShape.len_le D L P T)
  obtain ⟨s1, s2, -⟩ := WtShape.spacing_ge T ((i : ℕ) + 1) _ hlen
  have eN : ((((dat p i).p + (dat p i).q : ℕ)) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  have hb0 : 0 < L.sc.b := by linarith
  have hsb : 0 < Real.sqrt L.sc.b := Real.sqrt_pos.2 hb0
  have hw : ∀ τ, Real.sqrt L.sc.b / 2 ≤ (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) := fun τ => by
    have := hW.low τ; have := hH.low; linarith
  have hrho := _root_.GlobalTheory.MeanTop.rho_div_le _ _ (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁) (LevelStarExponents.h0 L) hY hDv hsa
    (fun τ => lt_of_lt_of_le (by positivity) (hw τ))
    (by
      show 4 * (((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) + (lenT p i T.PP : ℝ) + (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) + 1) ≤ LevelStarExponents.h0 L
      rw [eN, hDp]; simpa [cZero] using s1)
    (by
      show 24 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i T.PP : ℝ) ≤ LevelStarExponents.h0 L
      rw [eN]; exact s2)
    (fun τ a b hab hb => bar_gap p i P hi τ a b hab hb)
  have hrB : GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁ = GlobalTheory.CompHt.rhoOf (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).u'
      (wtsAt p i T.PP h0' S eta (wp p i T.PP).u₁).u1 := by
    unfold GlobalTheory.CompHt.rhoB; congr 1; funext τ j; rw [GlobalTheory.CompHt.uPrime_apply]; rfl
  have hcard : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by rw [← Nat.card_eq_fintype_card, hW.card]
  have hrho' : GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁ ≤ 3 * (D.R.r : ℝ) * ((D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r *
      (2 * ((lenT p i T.PP : ℝ) + T.Dp + 1)) / LevelStarExponents.h0 L + 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) * (2 / Real.sqrt L.sc.b))) := by
    rw [hrB]
    refine hrho.trans ((mul_le_mul_of_nonneg_left (Finset.sum_le_card_nsmul _ _ ((D.R.r : ℝ) * D.R.r *
      (2 * ((lenT p i T.PP : ℝ) + T.Dp + 1)) / LevelStarExponents.h0 L + 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) *
      (2 / Real.sqrt L.sc.b)) fun τ _ => ?_) (by rw [eN]; positivity)).trans_eq ?_)
    · show (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (((dat p i).p + (dat p i).q : ℕ) : ℝ) *
          (2 * ((lenT p i T.PP : ℝ) + (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) + 1)) / LevelStarExponents.h0 L +
          2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i T.PP : ℝ) /
          (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ _
      rw [eN, hDp]
      have hwp : 0 < (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) :=
        lt_of_lt_of_le (by positivity) (hw τ)
      have h2 : 1 / (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℝ) ≤ 2 / Real.sqrt L.sc.b := by
        rw [div_le_div_iff₀ hwp hsb]; linarith [hw τ]
      have h3 : 0 ≤ 2 * (D.R.r : ℝ) * D.R.r * (lenT p i T.PP : ℝ) := by positivity
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      rw [mul_one_div] at h4
      linarith
    · rw [Finset.card_univ, nsmul_eq_mul, hcard, eN]
  have hk : kap p i ≤ 4 * (D.R.f : ℝ) * D.R.r * L.sc.b := by
    show ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)| ≤ _
    calc ∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|
        ≤ ∑ τ : Psi p.T.Q.H, ∑ k : Fin ((dat p i).p + (dat p i).q), 4 * L.sc.b := by
          gcongr with τ _ k _; exact hW.up τ k
      _ = 4 * (D.R.f : ℝ) * D.R.r * L.sc.b := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hcard, eN]; ring
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have h8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
    linarith
  have hD1 : (1 : ℝ) ≤ T.Dp := by exact_mod_cast WtShape.one_le_Dp T
  have hTl : T.PP ^ 2 * (T.Dp : ℝ) ^ 2 * D.R.k / D.R.m ≤ (lenT p i T.PP : ℝ) := by
    unfold lenT; rw [hDp]; exact Nat.le_ceil _
  have hTO : (lenT p i T.PP : ℝ) ≤ T.TO := by exact_mod_cast hlen
  have hT4 : 4 * (T.Dp : ℝ) + 4 ≤ lenT p i T.PP := by
    have := hY.h1
    have h : 4 * T.Dp + 4 ≤ lenT p i T.PP := by rw [← hDp]; exact this
    exact_mod_cast h
  have hH0 : (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp * T.PP ≤ LevelStarExponents.h0 L := by
    refine le_trans ?_ T.heightBound_ge_order_product
    have hP : 0 ≤ T.PP := by linarith [WtShape.forty_le_PP T]
    have : 0 ≤ (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * T.Dp * T.PP := by positivity
    nlinarith [T.ChT_ge]
  have hn0 : 2500 * (D.R.r : ℝ) * ((T.Dp : ℝ) + 1) ≤ T.TO := by
    have h := T.order_ge_rank_bound
    have h' : 2500 * D.R.r * (T.Dp + 1) ≤ T.TO := le_trans (by
      rw [show 2500 * D.R.r * (T.Dp + 1) = 2 * (2 * 5 ^ 4 * D.R.r) * (T.Dp + 1) by ring]; exact Nat.le_add_left _ _) h
    exact_mod_cast h'
  have hnW : (D.R.f : ℝ) * D.R.r * ((D.R.r : ℝ) + 1) ≤ T.nWn := by exact_mod_cast T.nW_lo.1
  have hP3 : T.PP ^ 3 * (T.TO : ℝ) ^ 2 ≤ Real.sqrt L.sc.b := by
    rw [Real.sqrt_eq_rpow]; exact T.precision_cube_order_sq_le_sqrt
  have hsp : (T.TO : ℝ) * T.nWn ≤ D.R.r + D.R.t := by
    have h := T.split
    have h' : T.TO * T.nWn ≤ D.R.r + D.R.t := by omega
    exact_mod_cast h'
  have hNb : (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ D.R.N D.R.m := by
    have h' : D.R.m * (D.R.t + 1) ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast h'
  have key := _root_.GlobalTheory.seven_mul_height_bound_le_half (T.Dp : ℝ) (lenT p i T.PP : ℝ) (GlobalTheory.CompHt.rhoB (dat p i) (wp p i T.PP).u₁) T.PP (kap p i) L.sc.b
    D.R.f D.R.r D.R.m D.R.k (LevelStarExponents.h0 L) T.TO (D.R.N D.R.m) T.nWn D.R.t hD1 hb0 hf1 hm2 hmk (WtShape.r_cast D.R)
    (Nat.cast_nonneg _) (sizeK_nonneg _ _ _) hk hTl hTO hT4 hrho' hH0 hn0 hnW T.PP_nW hP3 hsp hNb
  unfold zed
  rw [hDp]
  exact key

end GlobalTheory.CovTop.ZedSz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsPullbackAffineClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchLift

theorem whiskerLeft_isPullback_affine_closed (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X)
    (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (hc : i' ≫ p = p' ≫ i) (hpb : IsPullback i'.left p'.left p.left i.left)
    [IsAffineHom p.left] [IsClosedImmersion i.left] :
    IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧
      IsClosedImmersion (E ◁ i).left := by
  have hP := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p
  have hI := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E i
  have hP' := GlobalTheory.DualCon.isPullback_whiskerLeft_snd_left E p'
  refine ⟨?_, MorphismProperty.of_isPullback hP.flip ‹_›, MorphismProperty.of_isPullback hI.flip ‹_›⟩
  have hout := hP'.flip.paste_horiz hpb
  refine IsPullback.of_right ?_ ?_ hP.flip
  · have h1 : (E ◁ i').left ≫ (snd E X').left = (snd E Z').left ≫ i'.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    have h2 : (E ◁ i).left ≫ (snd E X).left = (snd E Z).left ≫ i.left := by
      rw [← Over.comp_left, ← Over.comp_left]; simp
    rw [h1, h2]; exact hout
  · rw [← Over.comp_left, ← Over.comp_left, ← whiskerLeft_comp, ← whiskerLeft_comp, hc]

theorem glues_whiskerLeft : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → IsPullback (E ◁ i').left (E ◁ p').left (E ◁ p).left (E ◁ i).left ∧ IsAffineHom (E ◁ p).left ∧ IsClosedImmersion (E ◁ i).left ∧ GlobalTheory.PinchLift.Glues (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left := by
  intro S E X X' Z Z' p i i' p' hE hc hpb hp hi hg
  obtain ⟨h1, h2, h3⟩ := whiskerLeft_isPullback_affine_closed S E X X' Z Z' p i i' p' hc hpb
  refine ⟨h1, h2, h3, ?_⟩
  refine _root_.GlobalTheory.PinchLift.glues_of_basis (E ◁ p).left (E ◁ i).left (E ◁ i').left (E ◁ p').left
    {W | IsAffineOpen W ∧ ∃ V : X.left.Opens, IsAffineOpen V ∧ W ≤ (snd E X).left ⁻¹ᵁ V} ?_ ?_
  · intro W x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((snd E X).left x)) isOpen_univ
    obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hle⟩ := (E ⊗ X).left.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((W ⊓ (snd E X).left ⁻¹ᵁ V : (E ⊗ X).left.Opens) : Set (E ⊗ X).left) from ⟨hx, hxV⟩)
      (W ⊓ (snd E X).left ⁻¹ᵁ V).isOpen
    exact ⟨W', ⟨hW', V, hV, fun y hy => (hle hy).2⟩, hxW', fun y hy => (hle hy).1⟩
  · rintro W ⟨hW, V, hV, hWV⟩
    exact _root_.GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange S E X X' Z Z' p i i' p' hE hc hpb hp hi hg V W hV hW hWV

end GlobalTheory.PinchLift
end

