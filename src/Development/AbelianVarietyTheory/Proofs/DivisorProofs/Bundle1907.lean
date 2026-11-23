module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrExtension
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsNonzeroOfGenerator
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0147
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDimSuccGeneratingSectionsInfiniteField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.GenCut

theorem isEmpty_of_topologicalKrullDim_lt_zero (T : Type) [TopologicalSpace T]
    (h : topologicalKrullDim T < ((0 : ℕ) : WithBot ℕ∞)) : IsEmpty T := by
  by_contra hT
  rw [not_isEmpty_iff] at hT
  obtain ⟨x⟩ := hT
  haveI : Nonempty (IrreducibleCloseds T) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim T := Order.krullDim_nonneg
  exact absurd h (not_lt.mpr (by simpa using h0))

theorem exists_sections_cover_closed (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X) (hL : L.IsLB)
    (n : ℕ) (u : Fin n → L.Sec) (hu : ⨆ i, nonzeroLocus (u i) = ⊤) (e : ℕ) :
    ∀ Z : Set X, IsClosed Z → topologicalKrullDim Z < (e : ℕ) →
      ∃ s : Fin e → L.Sec, ∀ x ∈ Z, ∃ i, x ∈ nonzeroLocus (s i) := by
  induction e with
  | zero =>
    intro Z _ h
    have := isEmpty_of_topologicalKrullDim_lt_zero Z h
    exact ⟨Fin.elim0, fun x hx => (this.false ⟨x, hx⟩).elim⟩
  | succ e ih =>
    intro Z hZ h
    obtain ⟨S, hS, hdim⟩ := _root_.GlobalTheory.Div.exists_finite_topologicalKrullDim_diff_lt X Z hZ
    obtain ⟨t, ht⟩ := _root_.GlobalTheory.exists_sec_nonzero_on_finite_of_generated k X p L hL n u hu S hS
    have hU : IsOpen ((nonzeroLocus t : X.Opens) : Set X) := (nonzeroLocus t).isOpen
    obtain ⟨s, hs⟩ := ih (Z \ ((nonzeroLocus t : X.Opens) : Set X)) (hZ.sdiff hU)
      (hdim _ hU (fun x hx => ht x hx) e h)
    refine ⟨Fin.cons t s, fun x hx => ?_⟩
    by_cases hxt : x ∈ nonzeroLocus t
    · exact ⟨0, by simpa using hxt⟩
    · obtain ⟨i, hi⟩ := hs x ⟨hx, hxt⟩
      exact ⟨i.succ, by simpa using hi⟩

theorem exists_generating_sections_of_dim_le :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (p : X ⟶ Sp k) (L : LB X), L.IsLB → ∀ d : ℕ, topologicalKrullDim X ≤ d → ∀ (n : ℕ) (u : Fin n → L.Sec), ⨆ i, nonzeroLocus (u i) = ⊤ → ∃ s : Fin (d + 1) → L.Sec, ⨆ i, nonzeroLocus (s i) = ⊤ := by
  intro k _ _ X _ p L hL d hd n u hu
  have h1 : topologicalKrullDim (Set.univ : Set X) ≤ topologicalKrullDim X :=
    topologicalKrullDim_subspace_le X _
  have h2 : ((d : ℕ) : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self d
  obtain ⟨s, hs⟩ := exists_sections_cover_closed k X p L hL n u hu (d + 1) Set.univ isClosed_univ
    (lt_of_le_of_lt (h1.trans hd) h2)
  refine ⟨s, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨i, hi⟩ := hs x (Set.mem_univ x)
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end GlobalTheory.GenCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEvenUnimodularCharZero
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.PowEightField

open GlobalTheory.EighthPowerFactor GlobalTheory.CechPic

theorem exists_eighthPower_evenUnimodular_charZero : ∃ d : ℕ, 1 ≤ d ∧ ∀ (K : Type) [Field K] [CharZero K] (P : PolAV (Sp K)), ∃ (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ P.A)) (inc : P.A ⟶ Q.A), Q.g = 8 * P.g ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) ∧ IsPow8 P Q d pr inc := by
  obtain ⟨W, hW, hbas⟩ := ZM.exists_isE8_isSharpBasis
  have hW0 : 0 < W 0 0 := by
    have h := hW.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h
    have : (0 : ℝ) < (W 0 0 : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨(2 * W 0 0).toNat, by omega, ?_⟩
  intro K _ _ P
  have := P.isAb.comm
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  obtain ⟨bas, hb⟩ := hbas P.g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  let b : ZM.TBase K 1 := ⟨1, by simp, fun K _ β => by simp⟩
  have hc : (siegOne L₁.globalFns P.isAb P.isLB P.g).Principal :=
    ⟨relAmple_diag_lam P.isAb P.isLB (Moduli.cube_of_isLB _ P P.L P.isLB) P.ample,
      fun T x hx => SiegelOfPolarised.eq_one_of_lam P.isLB P.ktriv x hx⟩
  obtain ⟨t, ⟨pr, hpr, hu, hL, -⟩, h₁, h₂, h₃⟩ := exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB P.g _ W _ a w w'
    bas hW hb hw hw' hs 1 K b _ (𝟙 _) (siegOne L₁.globalFns P.isAb P.isLB P.g) (one_pow _) odd_one hc P.smoothDim
  obtain ⟨inc, hinc, -⟩ := hu P.A fun u => if u = 0 then 𝟙 P.A else 1
  refine ⟨t.pol, pr, inc, rfl, ⟨t.act w, t.act w', t.hom w, t.hom w', h₁, h₃, h₂⟩, hpr, ?_, hu, hinc, ?_⟩
  · refine isMonHom_of_coord hpr hu fun u => ?_
    rw [hinc u]
    by_cases h : u = 0
    · subst h; simp only [↓reduceIte]; exact inferInstanceAs (IsMonHom (𝟙 P.A))
    · simp only [h, ↓reduceIte]; exact inferInstanceAs (IsMonHom (toUnit P.A ≫ η[P.A]))
  ·
    have hP : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
    have hQ : t.pol.L.IsLB := t.pol.isLB
    have hlam : cls _ hP = lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A) := cls_cube_two P.isLB _ _ hP
    have hdiag := (cls_eq_iff (LB.isLB_linComb P.isLB _ _) (pull_isLB hP _)).2 (SiegelOfPolarised.lbIso_diag L₁ P)
    rw [cls_lbPow P.isLB, cls_pull hP, hlam, pull_lam, lift_fst, lift_snd] at hdiag
    have e1 := ((cls_eq_iff hQ (LB.isLB_linComb hP _ _)).2 hL).trans (cls_linComb hP _ _ _)
    refine (cls_eq_iff (pull_isLB hQ _) (LB.isLB_linComb P.isLB _ _)).1 ?_
    refine ((congrArg (pull inc.left) e1).trans ?_).trans (cls_lbPow P.isLB _ _).symm
    rw [hlam]
    erw [map_sum]
    rw [Fintype.sum_eq_single ((0 : Fin 8), (0 : Fin 8))]
    · erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      erw [hinc]
      simp only [↓reduceIte]
      rw [← hdiag, ← natCast_zsmul, ← natCast_zsmul, smul_smul, Int.toNat_of_nonneg (by omega)]
      congr 1
      push_cast
      ring
    · rintro ⟨u, v⟩ huv
      erw [map_zsmul]
      erw [CechPic.pull_lam, CechPic.pull_lam]
      erw [lift_fst, lift_snd]
      dsimp only
      have hi1 : ∀ u : Fin 8, u ≠ 0 → inc ≫ pr u = 1 := fun u h => (hinc u).trans (if_neg h)
      by_cases hu0 : u = 0
      · subst hu0
        have hv0 : v ≠ 0 := fun h => huv (by rw [h])
        erw [hi1 v hv0, lam_one_right, smul_zero]
      · erw [hi1 u hu0, lam_one_left, smul_zero]

end GlobalTheory.MBLow.PowEightField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionDvrFlagLift
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifTrait

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}


set_option maxHeartbeats 1000000 in
theorem exists_intFr_frBor (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : Model Xo c β) (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c)
    (hz : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt) (hzs : z ≫ pullback.snd _ _ = spMap io) :
    letI := io.toAlgebra
    ∀ y₀ : FrPt Xo c T.Fr, y₀.x = z ≫ pullback.fst _ _ →
      ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀ y.1 := by
  let _ := io.toAlgebra
  intro y₀ hy0
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T io O β Y yt z hz hzs _ m
  have hx : (z ≫ pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨x₀, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ := y₀
  change x₀ = z ≫ pullback.fst _ _ at hy0
  subst hy0
  obtain ⟨ub, u, hub, htan, heig, hbas, htri⟩ := lieFree Xo c T io _ t' _ m1 m2 hx u₀ htan₀ heig₀ hbas₀
  obtain ⟨θ, s, hθ, hmatch, hgen, a, ha⟩ :=
    GlobalTheory.DepthSum.thetaFrame_trait Xo c T io O β Y yt z hz hzs _ m t' m1 m2 s₀ hgen₀
  let y : FrPt Xo c T.Fr := ⟨z ≫ pullback.fst _ _, hx, u, htan, heig, hbas, s, hgen⟩
  choose cf hcf using htri
  let tt : Ix Dw → T.Frˣ := fun o => match o with
    | none => a
    | some p => (hcf p.1 p.2).1.unit
  have hFB : FrBor tt ⟨z ≫ pullback.fst _ _, hx₀, u₀, htan₀, heig₀, hbas₀, s₀, hgen₀⟩ y := by
    refine ⟨rfl, fun τ i => ⟨cf τ i, (hcf τ i).1.unit_spec.symm, (hcf τ i).2.1, (hcf τ i).2.2⟩, 𝟙 _,
      Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
    change (Scheme.Hom.appLE (𝟙 (Gx (z ≫ pullback.fst _ _))) _ _ h).hom
      (scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i) = s.f i
    rw [ha i, Scheme.Hom.appLE, Scheme.Hom.id_app]
    erw [Category.id_comp, show (homOfLE h).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  exact ⟨⟨y, GlobalTheory.Frames.framedPoint_field_fromTest GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c T.Fr y, _, t', m1, m2, ⟨ub, hub⟩, θ, hθ, hmatch⟩, tt, hFB⟩

end Frames

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

section Split

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem charZero_residue_of_map {K : Type} [Field K] [CharZero K] (V : Type) [CommRing V] [IsLocalRing V]
    (f : Sp V ⟶ Sp K) : CharZero (ResidueField V) :=
  charZero_of_injective_ringHom ((residue V).comp (Spec.preimage f).hom).injective

theorem exists_split_baseChange (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] [CharZero (ResidueField W)] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) :
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (maximalIdeal W') W') (_ : Algebra W W'),
      Module.Finite W W' ∧ Function.Injective (algebraMap W W') ∧
      ∃ S : SplitExt (Sp (ResidueField W')), S.IsGt ((Over.pullback (spMap (residue W'))).obj
        ((Over.pullback (spMap (algebraMap W W'))).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨k', _, _, hk, Sx, ⟨d⟩⟩ := GlobalTheory.UnifAfterExt.exists_finite_split _ h₀
  have : Algebra.IsSeparable (ResidueField W) k' := inferInstance
  obtain ⟨W', i1, i2, i3, i4, i5, hf, hi, -, -, e, he⟩ := GlobalTheory.unramExt W k'
  refine ⟨W', i1, i2, i3, i4, i5, hf, hi, ?_⟩
  have key : (e.symm.toRingHom.comp (algebraMap (ResidueField W) k')).comp (residue W) =
      (residue W').comp (algebraMap W W') :=
    RingHom.ext fun v => e.symm_apply_eq.2 (he v).symm
  obtain ⟨j, hj, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback _ (spMap e.symm.toRingHom)).comp
      ((isGrpPullback_pullback _ (spMap (algebraMap (ResidueField W) k'))).comp
        (isGrpPullback_pullback G (spMap (residue W))))).congr
      (f' := spMap (residue W') ≫ spMap (algebraMap W W'))
      (by rw [← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, key]) rfl)
    ((isGrpPullback_pullback _ (spMap (residue W'))).comp (isGrpPullback_pullback G (spMap (algebraMap W W'))))
  exact ⟨_, isGt_of_iso j (GtBaseChange.isGt_extBC (spMap e.symm.toRingHom) Sx _ d)⟩

end Split

end GlobalTheory.UnifTrait

namespace GlobalTheory.UnifTrait

open IsLocalRing


end GlobalTheory.UnifTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfArcVanishingSmoothChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
open GlobalTheory.ShFam.BdArc GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.CompHS

theorem evalPt_spMap_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R]
    (ψ : Γ(X, U) →+* R) (h : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) ⁻¹ᵁ U) :
    GlobalTheory.TangentOrigin.evalPt (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) U h = ψ := by
  have := GlobalTheory.TangentOrigin.eq_spec_fromSpec hU _ h
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem exists_extension_of_arcZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ) (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)), ArcZero X Z la σ m → ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι) (p : Γ(Y₀ X Z, W)) (hi : W ≤ (L₀ X Z la).U i), IsDomain Γ(Y₀ X Z, W) → RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom → p ≠ 0 → (∀ y' ∈ W, (y' ∈ bd₀ X Z ↔ y' ∉ (Y₀ X Z).basicOpen p)) → ∃ b : Γ(Y₀ X Z, W), (∀ y' (h : y' ∈ W) (h' : y' ∈ U₀ X Z), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∈ bd₀ X Z → ger y' h b ∈ IsLocalRing.maximalIdeal ((Y₀ X Z).presheaf.stalk y') := by
  intro E _ _ _ H Dw l Xo c Y X Z la σ m hm W hW i p hi hdom hsm hp hbd
  have hPW : (Y₀ X Z).basicOpen p ≤ W := (Y₀ X Z).basicOpen_le p
  have hPU : (Y₀ X Z).basicOpen p ≤ U₀ X Z := fun y hy => by
    by_contra h
    exact (hbd y (hPW hy)).1 h hy
  have hPL : (Y₀ X Z).basicOpen p ≤ U₀ X Z ⊓ (L₀ X Z la).U i := le_inf hPU (hPW.trans hi)
  have := hW.isLocalization_basicOpen p
  obtain ⟨⟨a, _, M, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers p) (resG _ hPL (m.loc i))
  have e' : resG _ hPL (m.loc i) * resG _ hPW (p ^ M) = resG _ hPW a := e
  have hφ : Spec.map (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)) =
      (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z := Spec.map_preimage _
  letI : Algebra c.F Γ(Y₀ X Z, W) :=
    (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom.toAlgebra
  obtain ⟨b, hab, hb⟩ := exists_eq_mul_pow_of_tendsto_zero c.F Γ(Y₀ X Z, W) hsm σ p a M hp
    fun ψ r hψ hσ h0 h1 => by
      have hlim := hm W hW i hi ψ r hψ
        (fun u hu => by
          rw [← hσ u hu]
          exact (congrArg (spMap (ψ u) ≫ ·) hφ.symm).trans (Spec.map_comp _ _).symm)
        (fun s => (hbd _ (spMap_fromSpec_mem hW _ s)).2 fun h =>
          (spMap_fromSpec_mem_basicOpen hW _ p s).1 h h0)
        (fun u hu hu0 s _ => hPU ((spMap_fromSpec_mem_basicOpen hW _ p s).2 (h1 u hu hu0)))
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hψ.1
      filter_upwards [hlim ε hε, mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hub hu0
      have hWx : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ W :=
        fun s _ => spMap_fromSpec_mem hW _ s
      have hPx : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (Y₀ X Z).basicOpen p :=
        fun s _ => (spMap_fromSpec_mem_basicOpen hW _ p s).2 (h1 u hub hu0)
      have hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z :=
        fun s hs => hPU (hPx hs)
      have hiu : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ X Z la).U i :=
        fun s hs => hi (hWx hs)
      have hev := evalPt_spMap_fromSpec hW (ψ u) hWx
      have hpu : ψ u (p ^ M) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (h1 u hub hu0)
      have hmul : H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) i hO hiu m * ψ u (p ^ M) =
          ψ u a := by
        have e₁ := congrArg (GlobalTheory.TangentOrigin.evalPt _ _ hPx) e'
        rw [map_mul, GlobalTheory.TangentOrigin.evalPt_res _ hPL (GlobalTheory.TopForm.le_preimage_inf hO hiu) hPx,
          GlobalTheory.TangentOrigin.evalPt_res _ hPW hWx hPx, GlobalTheory.TangentOrigin.evalPt_res _ hPW hWx hPx, hev] at e₁
        exact e₁
      rw [dist_zero_right, ← hmul, mul_div_cancel_right₀ _ hpu]
      exact hu hO hiu
  refine ⟨b, fun y' h h' => ?_, fun y' h hy => ?_⟩
  · have hyP : y' ∈ (Y₀ X Z).basicOpen p := by
      by_contra hn
      exact (hbd y' h).2 hn h'
    have hunit : IsUnit (ger y' h p) := ((Y₀ X Z).mem_basicOpen p y' h).1 hyP
    have hunit' : IsUnit (ger y' h (p ^ M)) := by
      rw [map_pow]
      exact hunit.pow M
    have e₁ := congrArg (ger y' hyP) e'
    rw [map_mul, ger_resG, ger_resG, ger_resG, hab, map_mul] at e₁
    exact (hunit'.mul_right_cancel e₁).symm
  · have hyP : y' ∉ (Y₀ X Z).basicOpen p := (hbd y' h).1 hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨n, hn⟩ := hb
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hn
    refine hyP (((Y₀ X Z).mem_basicOpen p y' h).2 ?_)
    have h₂ := hu.pow n
    rw [← map_pow, ← hd, map_mul] at h₂
    exact isUnit_of_mul_isUnit_right h₂

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOrderLevelMoveUniversalSemiAbelian
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.MoveOrder

theorem finite_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) («γ» : LevelAut Dw l) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsIso ρ → IsLevMove ρ ν (liftLa «γ») LinearMap.id → ∃ n : ℕ, 0 < n ∧ (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[n] (𝟙 _) = 𝟙 _ := by
  intro E _ _ _ H Dw l Xo c γ ρ ν hpq hl hρ hm
  have hA : l.A.Coprime l.M := by rw [hl]; exact Nat.coprime_one_left _
  obtain ⟨⟨ι, hι, -⟩, hmul, -⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
  have h₀ : IsLevMove (𝟙 Xo.X) ι (liftLa (1 : LevelAut Dw l)) LinearMap.id := by
    refine ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  have key : ∀ k : ℕ, ∃ (ρk : Xo.X ⟶ Xo.X) (μ : SABMap Xo.univ.t Xo.univ.t ρk), IsIso ρk ∧
      IsLevMove ρk μ (liftLa («γ» ^ k)) LinearMap.id ∧
      μ.φ = (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[k] (𝟙 _) := by
    intro k
    induction k with
    | zero => exact ⟨𝟙 _, ι, inferInstance, by rw [pow_zero]; exact h₀, by rw [hι]; rfl⟩
    | succ k ih =>
      obtain ⟨ρk, μ, ik, hk, hφ⟩ := ih
      obtain ⟨κ, hκ, -⟩ := hmul ρk ρ μ ν
      refine ⟨ρk ≫ ρ, κ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, ?_⟩
      · rw [Category.assoc, hm.1, hk.1]
      · rw [pow_succ, GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub («γ» ^ k) «γ» a), hκ,
          ← Category.assoc, hk.2.1, Category.assoc, hm.2.1, Category.assoc]
      · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a =
            (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
        rw [e, hκ, ← Category.assoc, hk.2.2, Category.assoc, hm.2.2, Category.assoc]
      · rw [hκ, hφ, Function.iterate_succ_apply']
  refine ⟨orderOf «γ», orderOf_pos «γ», ?_⟩
  obtain ⟨ρn, μ, i, h, hφ⟩ := key (orderOf «γ»)
  rw [pow_orderOf_eq_one] at h
  rw [← hφ, (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c 1 i inferInstance h h₀).2, hι]

end GlobalTheory.MoveOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveFieldStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_liesOn_component_cmCurve_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (hle : c.F ≤ K), GlobalTheory.CompRat.CurveOver H K l.M' → ∀ Z : Comp Xo c, (letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra; ∃ y : FrPt Xo c K, LiesOn Z y) := by
  first | exact @GlobalTheory.FixedPoint.exists_frPt_liesOn | exact GlobalTheory.FixedPoint.exists_frPt_liesOn | (intros; apply GlobalTheory.FixedPoint.exists_frPt_liesOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointOfCompactFlagSpaceOpenPart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS

theorem exists_frPt_of_flagOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] (z : Sp K ⟶ X.YY), ⊤ ≤ z ⁻¹ᵁ flagOpen X → ∃ io : c.F →+* K, letI := io.toAlgebra; ∃ P : FrPt Xo c K, X.ptY P = z := by
  intro E _ _ _ H Dw l Xo c Y X K _ z hO
  obtain ⟨a, h⟩ := GlobalTheory.CompHS.exists_chartFr z hO
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover z
  obtain ⟨Q, hQ⟩ := h k hz
  refine ⟨algebraMap c.F K, ?_⟩
  have e : (algebraMap c.F K).toAlgebra = a := Algebra.algebra_ext _ _ fun _ => rfl
  rw [e]
  exact ⟨Q, (FlagCover.eq_ptY hQ.lies).symm⟩

end GlobalTheory.CompHS
end

