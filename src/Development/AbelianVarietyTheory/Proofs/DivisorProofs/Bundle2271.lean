module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsRelAcyclicPolAVBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfSymplecticLevelPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegelLevelPull

theorem exists_siegPre_of_points : ∀ (n : ℕ) (hn : 3 ≤ n) (V V₁ : Type) [CommRing V] [CommRing V₁] [IsLocalRing V₁] [IsNoetherianRing V₁] (f₁ : V →+* V₁) (b : cycAway n →+* V) (PB : PolAV (Sp V)) (lev : (Fin PB.g ⊕ Fin PB.g → ℤ) → (Over.mk (spMap f₁) ⟶ PB.A)) (r : ℕ) (d₀ : Fin r → (Over.mk (spMap f₁) ⟶ PB.A)) (c : Fin r → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ n = 1) → (∀ x y, Out.WeilIs PB.A PB.L n (lev x) (lev y) (unitOn (Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit ^ omegaStd x y))) → (∀ i, d₀ i ^ n = toUnit _ ≫ c i) → ∃ (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c i).left := by
  set_option backward.isDefEq.respectTransparency false in
    intro n hn V V₁ _ _ _ _ f₁ b PB lev r d₀ c hadd htors hweil hd
    have hn0 : n ≠ 0 := by omega
    haveI := PB.isAb.comm
    let P₁ : PolAV (Sp V₁) := GlobalTheory.StrictPull.polPull PB (spMap f₁)
    haveI : IsCommMonObj P₁.A := P₁.isAb.comm
    have hpb : IsGrpPullback P₁.A PB.A (spMap f₁) (pullback.fst PB.A.hom (spMap f₁)) :=
      isGrpPullback_pullback PB.A (spMap f₁)
    obtain ⟨κ, hκ⟩ := GlobalTheory.UnifPoint.exists_pointEquiv hpb
    have hk : ∀ x, (κ.symm x).left ≫ pullback.fst PB.A.hom (spMap f₁) = x.left := fun x => by
      rw [← hκ, κ.apply_symm_apply]
    let ze : V₁ˣ := Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit
    let lev₁ : (Fin PB.g ⊕ Fin PB.g → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ P₁.A) := fun x => κ.symm (lev x)
    have hL₁ : LBIso P₁.L (PB.L.pull (pullback.fst PB.A.hom (spMap f₁))) :=
      GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB PB.isLB _)
    have hw : ∀ x y, WeilIs P₁.A P₁.L n (lev₁ x) (lev₁ y) (unitOn (ze ^ omegaStd x y)) := fun x y =>
      (GlobalTheory.weilIs_grpPullback_of_comm _ _ PB.A P₁.A (spMap f₁) _ PB.L P₁.L PB.isLB P₁.isLB hpb hL₁ _ n _ _
        (pushPt hpb.1.w (lev₁ x)) (pushPt hpb.1.w (lev₁ y)) _ rfl rfl).2
        (GlobalTheory.UnifPoint.weilIs_congr (Category.id_comp _).symm (hk _).symm (hk _).symm (hweil x y))
    have hadd₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y := fun x y => by
      simp only [lev₁, hadd, map_mul]
    have htors₁ : ∀ x, lev₁ x ^ n = 1 := fun x => by
      simp only [lev₁, ← map_pow, htors, map_one]
    have hu : IsUnit (n : V₁) := by simpa using (GlobalTheory.SiegelTor.isUnit_natCast hn0).map (f₁.comp b)
    have hze : (ze : V₁) = (f₁.comp b) (zetaAway n) := by simp [ze]
    have hprim : ∀ (k : Type) [Field k] (gk : V₁ →+* k), IsPrimitiveRoot (gk ze) n := fun k _ gk => by
      rw [hze]; exact GlobalTheory.SiegelTor.isPrimitiveRoot_map hn0 (gk.comp (f₁.comp b))
    haveI : IsMonHom (Iso.refl P₁.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    have hid : IsGrpPullback P₁.A P₁.A (spMap (RingHom.id V₁)) (𝟙 _) :=
      (isGrpPullback_of_iso (Iso.refl P₁.A)).congr (by simp [spMap]) rfl
    obtain ⟨s, ψ, hψ, hs, hsP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre V₁ V₁ P₁ (RingHom.id V₁) P₁ (𝟙 _) hid
      (GlobalTheory.lbIso_pull_id P₁.isLB).symm rfl (cycAway n) (f₁.comp b) PB.g n (zetaAway n) ze lev₁ rfl hu hze hprim
      hadd₁ htors₁ hw

    haveI := hψ
    have hLamB : (abelian₂ PB.A PB.L).IsLB := DVR.linComb_isLB _ PB.isLB _ _
    have hLam₁ : (abelian₂ P₁.A P₁.L).IsLB := DVR.linComb_isLB _ P₁.isLB _ _
    obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (spMap f₁) PB.A P₁.A _ hpb
    have e₁ : LBIso (abelian₂ P₁.A P₁.L) ((abelian₂ PB.A PB.L).pull (β₂ ≫ 𝟙 _)) :=
      hlam PB.L P₁.L _ (abelian₂ PB.A PB.L) (𝟙 _) PB.isLB P₁.isLB hLamB hL₁ (GlobalTheory.lbIso_pull_id hLamB).symm
    rw [Category.comp_id] at e₁
    let κ₂ := (lift (fst s.A s.A ≫ ψ.hom) (snd s.A s.A ≫ ψ.hom)).left
    have e₂ : LBIso ((abelian₂ P₁.A P₁.L).pull κ₂) ((abelian₂ PB.A PB.L).pull (κ₂ ≫ β₂)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl) (chartPullSame (abelian₂ PB.A PB.L) _ (fun _ => β₂) _ κ₂ fun _ => rfl) e₁
    let d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A) := fun i => κ.symm (d₀ i) ≫ ψ.inv
    have hpow : ∀ (x : 𝟙_ (Over (Sp V₁)) ⟶ P₁.A) (m : ℕ), ((x ≫ ψ.inv) ^ m) ≫ ψ.hom = x ^ m := fun x m => by
      induction m with
      | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
      | succ m ih => rw [pow_succ, MonObj.mul_comp, ih, Category.assoc, Iso.inv_hom_id, Category.comp_id, pow_succ]
    refine ⟨s, ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁), κ₂ ≫ β₂, d, hs,
      ((isGrpPullback_of_iso ψ).comp hpb).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩,
      LBIso.trans s.isLB (pull_isLB hLam₁ _) (pull_isLB hLamB _) hsP e₂, fun i => ?_⟩
    · rw [Category.assoc, hsq.1]
      have e : κ₂ ≫ (fst P₁.A P₁.A).left = (fst s.A s.A).left ≫ ψ.hom.left := by
        simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_fst]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
    · rw [Category.assoc, hsq.2]
      have e : κ₂ ≫ (snd P₁.A P₁.A).left = (snd s.A s.A).left ≫ ψ.hom.left := by
        simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_snd]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
    · have h1 : (d i ^ n).left ≫ ψ.hom.left = (κ.symm (d₀ i) ^ n).left := by
        rw [← Over.comp_left, hpow]
      have hT : (toUnit (Over.mk (spMap f₁))).left = spMap f₁ := by
        simpa using Over.w (toUnit (Over.mk (spMap f₁)))
      calc (d i ^ n).left ≫ ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁)
          = ((d i ^ n).left ≫ ψ.hom.left) ≫ pullback.fst PB.A.hom (spMap f₁) := (Category.assoc _ _ _).symm
        _ = (κ.symm (d₀ i) ^ n).left ≫ pullback.fst PB.A.hom (spMap f₁) := by rw [h1]
        _ = (d₀ i ^ n).left := by rw [← map_pow, hk]
        _ = spMap f₁ ≫ (c i).left := by rw [hd, Over.comp_left, hT]

end GlobalTheory.SiegelLevelPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningFamilyMulTwistingSection
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SpanShortProd

theorem eLpNorm_homN_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (x : ℝ)
    {D : D7} {W : HSp D} (dict : GA D W → Σ k, Frame (V.X k).Ψ r) (μ : MeasureTheory.Measure (AutQ W))
    (hμ : μ Set.univ ≤ 1) (G : WTZ E) (f : Rul Xo c) (hf : rdU V f ∈ holSub V.X (GlobalTheory.AllWt.modelWt V G)) :
    MeasureTheory.eLpNorm' (fun q : AutQ W => GlobalTheory.AllWt.homN V x G f (dict q.out)) 2 μ ≠ ⊤ := by
  have hb : ∀ q : AutQ W, ‖GlobalTheory.AllWt.homN V x G f (dict q.out)‖ₑ ≤
      ENNReal.ofReal (GlobalTheory.AllWt.lieFacZ Dw x G) * supE V.X (GlobalTheory.AllWt.modelWt V G) (rdU V f) := by
    intro q
    rw [Real.enorm_eq_ofReal (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _), GlobalTheory.AllWt.homN,
      ENNReal.ofReal_mul (GlobalTheory.AllWt.lieFacZ_pos _ _).le]
    gcongr
    by_cases h : (dict q.out).2 ∈ (V.X (dict q.out).1).dom
    · exact le_iSup (fun p : FPt V.X => ENNReal.ofReal ((V.X p.1).pnorm (GlobalTheory.AllWt.modelWt V G p.1) (rdU V f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, h⟩⟩
    · have h0 : rdU V f (dict q.out).1 (dict q.out).2 = 0 := by simp [rdU, h]
      have h1 : GlobalTheory.AllWt.ptN (GlobalTheory.AllWt.modelWt V G) (rdU V f) (dict q.out) = 0 := by
        show ‖rdU V f (dict q.out).1 (dict q.out).2‖ * _ = 0
        rw [h0, norm_zero, zero_mul]
      rw [h1, ENNReal.ofReal_zero]; exact bot_le
  have hbound := MeasureTheory.eLpNorm'_mono_eNorm_ae (μ := μ) (q := 2)
    (f := fun q : AutQ W => GlobalTheory.AllWt.homN V x G f (dict q.out))
    (g := fun _ : AutQ W => ENNReal.ofReal (GlobalTheory.AllWt.lieFacZ Dw x G) *
      supE V.X (GlobalTheory.AllWt.modelWt V G) (rdU V f)) (by norm_num)
    (Filter.Eventually.of_forall (fun q => by simpa using hb q))
  rw [MeasureTheory.eLpNorm'_const _ (by norm_num)] at hbound
  apply ne_top_of_le_ne_top _ hbound
  simp only [enorm_eq_self]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (supE_ne_top _ _ hf))
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_top_of_le_ne_top ENNReal.one_ne_top hμ))

theorem petOn_mul_sig_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) {Z : Comp Xo c} {G G₀ : WTZ D.host.E}
    (t : GlobalTheory.FlatTw.TwSec U x Z G₀) (hG : Even G.2) {F : Rul Xo c} (hF : F ∈ cuspW Xo c U G) (σ : c.F →+* ℂ) :
    petOn U x V dict Z (G + G₀) σ (F * t.sig) ≤ t.cInf σ * petOn U x V dict Z G σ F := by
  unfold petOn
  rw [GlobalTheory.AllWt.petAt_eq, GlobalTheory.AllWt.petAt_eq]
  have hpt : ∀ q : AutQ (V (goodOf c σ)),
      ‖GlobalTheory.AllWt.homN (U (goodOf c σ)) x (G + G₀) (F * t.sig) (dict (goodOf c σ) q.out)‖ ≤
        (t.cInf σ • fun q : AutQ (V (goodOf c σ)) => GlobalTheory.AllWt.homN (U (goodOf c σ)) x G F (dict (goodOf c σ) q.out)) q := by
    intro q
    rw [Real.norm_of_nonneg (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _), Pi.smul_apply, smul_eq_mul]
    by_cases hz : dict (goodOf c σ) q.out ∈ GlobalTheory.AllWt.framesOn (U (goodOf c σ)) Z
    · rw [t.homN_mul_sig hG F hz, mul_comm]
    · have h0 : rdU (U (goodOf c σ)) (F * t.sig) (dict (goodOf c σ) q.out).1 (dict (goodOf c σ) q.out).2 = 0 :=
        GlobalTheory.AllWt.rdU_eq_zero _ (GlobalTheory.AllWt.mul_mem_suppOn F t.sig_mem_suppOn) hz
      have h1 : GlobalTheory.AllWt.homN (U (goodOf c σ)) x (G + G₀) (F * t.sig) (dict (goodOf c σ) q.out) = 0 := by
        show _ * (‖rdU (U (goodOf c σ)) (F * t.sig) (dict (goodOf c σ) q.out).1 (dict (goodOf c σ) q.out).2‖ * _) = 0
        rw [h0, norm_zero, zero_mul, mul_zero]
      rw [h1]
      exact mul_nonneg (t.cInf_pos σ).le (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _)
  have h1 := MeasureTheory.eLpNorm'_mono_ae (q := 2) (μ := GlobalTheory.AllWt.muOn (U (goodOf c σ)) (V (goodOf c σ))
    (dict (goodOf c σ)) Z) (by norm_num) (Filter.Eventually.of_forall (fun q =>
      (hpt q).trans (le_abs_self _ |>.trans_eq (Real.norm_eq_abs _).symm)))
  rw [MeasureTheory.eLpNorm'_const_smul _ (by norm_num), Real.enorm_eq_ofReal (t.cInf_pos σ).le] at h1
  have hfin := eLpNorm_homN_ne_top (U (goodOf c σ)) x (dict (goodOf c σ))
    (GlobalTheory.AllWt.muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z) (GlobalTheory.AllWt.muPart_univ_le _ _ _) G F
    ((GlobalTheory.AllWt.mem_cuspW.1 hF).2 _ (goodEmb_goodOf c σ))
  calc _ ≤ (ENNReal.ofReal (t.cInf σ) * MeasureTheory.eLpNorm' (fun q : AutQ (V (goodOf c σ)) =>
        GlobalTheory.AllWt.homN (U (goodOf c σ)) x G F (dict (goodOf c σ) q.out)) 2
          (GlobalTheory.AllWt.muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (t.cInf_pos σ).le]

theorem exists_span_mul_twSec : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G G₀ : WTZ D.host.E) (t : GlobalTheory.FlatTw.TwSec U x Z G₀), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ w, 0 ≤ t.lo w) → ∀ s₀ : Set (Rul Xo c), s₀ ⊆ (cuspW Xo c U G : Set (Rul Xo c)) → (∀ f ∈ s₀, ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) → cuspW Xo c U G ≤ Submodule.span c.F s₀ → ∃ s : Set (cuspOn U Z (G + G₀)), s ⊆ (latOn U Z (G + G₀) : Set (cuspOn U Z (G + G₀))) ∧ Submodule.span c.F s = ⊤ ∧ ∀ y ∈ s, ∃ f ∈ s₀, ∀ σ, normOn U x V dict Z (G + G₀) σ y ≤ t.cInf σ * petOn U x V dict Z G σ f := by
  intro D H Dw l Xo c r U x V dict Z G G₀ t hU hG hlo s₀ hsub hval hspan
  let Q : cuspW Xo c U G →ₗ[c.F] cuspOn U Z G :=
    LinearMap.codRestrict (cuspOn U Z G) ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype)
      (fun F => GlobalTheory.CuspSplit.idem_mul_mem_cuspOn hU Z F)
  let ψ : cuspW Xo c U G →ₗ[c.F] cuspOn U Z (G + G₀) := (GlobalTheory.FlatTw.Mul.mulEquiv t G hG).toLinearMap ∘ₗ Q
  let s₁ : Set (cuspW Xo c U G) := {F | (F : Rul Xo c) ∈ s₀}
  have hQ : Function.Surjective Q := fun g =>
    ⟨⟨g, GlobalTheory.AllWt.cuspOn_le U Z G g.2⟩, Subtype.ext (GlobalTheory.CuspSplit.idem_mul_of_mem_cuspOn g.2)⟩
  have hψ : Function.Surjective ψ := (GlobalTheory.FlatTw.Mul.mulEquiv t G hG).surjective.comp hQ
  have hs₁ : Submodule.span c.F s₁ = ⊤ := by
    apply Submodule.map_injective_of_injective (cuspW Xo c U G).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    have e : (cuspW Xo c U G).subtype '' s₁ = s₀ := by
      ext f
      constructor
      · rintro ⟨F, hF, rfl⟩; exact hF
      · intro hf; exact ⟨⟨f, hsub hf⟩, hf, rfl⟩
    rw [e]
    exact le_antisymm (Submodule.span_le.2 hsub) hspan
  refine ⟨ψ '' s₁, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    have hFl : F ∈ GlobalTheory.AllWt.latW U G := hval F hF
    have hQF : Q F ∈ latOn U Z G := GlobalTheory.CuspSplit.mem_latOn_part hU F hFl Z
    exact GlobalTheory.FlatTw.Mul.mem_latOn_of_mul t 1 one_ne_zero (fun w => by
      have h1 : vAdd w (1 : c.F) = 0 := by simp [vAdd]
      rw [h1, Int.cast_zero, zero_add]; exact hlo w)
      (Q F) hQF (ψ F) (by rw [one_smul]; rfl)
  · rw [Submodule.span_image, hs₁, Submodule.map_top, LinearMap.range_eq_top]
    exact hψ
  · rintro _ ⟨F, hF, rfl⟩
    refine ⟨F, hF, fun σ => ?_⟩
    have e : ((ψ F : cuspOn U Z (G + G₀)) : Rul Xo c) = (F : Rul Xo c) * t.sig := by
      show idem Z * (F : Rul Xo c) * t.sig = _
      rw [mul_comm (idem Z), mul_assoc, t.idem_sig]
    show petOn U x V dict Z (G + G₀) σ _ ≤ _
    rw [e]
    exact petOn_mul_sig_le U x V dict t hG F.2 σ

end GlobalTheory.SpanShortProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializationClosedInAffineNeighbourhood
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ClosedPt

lemma exists_max_specializes {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (x : Y)
    (hx : x ∈ V) : ∃ N : PrimeSpectrum Γ(Y, V), N.asIdeal.IsMaximal ∧
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≤ N.asIdeal ∧ x ⤳ hV.fromSpec N := by
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    (hV.primeIdealOf ⟨x, hx⟩).isPrime.ne_top
  refine ⟨⟨N, hN.isPrime⟩, hN, hle, ?_⟩
  have h1 : (hV.primeIdealOf ⟨x, hx⟩) ⤳ (⟨N, hN.isPrime⟩ : PrimeSpectrum Γ(Y, V)) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have h2 := Specializes.map (f := hV.fromSpec) h1 hV.fromSpec.continuous
  rwa [hV.fromSpec_primeIdealOf] at h2

lemma fromSpec_mem {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V)
    (N : PrimeSpectrum Γ(Y, V)) : hV.fromSpec N ∈ V := by
  have : hV.fromSpec N ∈ Set.range hV.fromSpec := ⟨N, rfl⟩
  rwa [hV.range_fromSpec] at this

theorem exists_closed_point : ∀ (Y : Scheme.{0}) (x : Y), ∃ V : Y.Opens, IsAffineOpen V ∧ ∃ y ∈ V, x ⤳ y ∧ ∀ V₂ : Y.Opens, V₂ ≤ V → IsAffineOpen V₂ → y ∈ V₂ → (∀ y₁ ∈ V₂, y ⤳ y₁ → y₁ = y) ∧ ∃ M : Ideal Γ(Y, V₂), M.IsMaximal ∧ ∀ a : Γ(Y, V₂), a ∈ M ↔ y ∉ Y.basicOpen a := by
  intro Y x
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤) trivial
  obtain ⟨N, hN, -, hxN⟩ := exists_max_specializes hV x hx
  refine ⟨V, hV, hV.fromSpec N, fromSpec_mem hV N, hxN, ?_⟩
  intro V₂ hle hV₂ hy
  have hcl : ∀ y₁ ∈ V₂, hV.fromSpec N ⤳ y₁ → y₁ = hV.fromSpec N := by
    intro y₁ hy₁ hs
    have e := hV.fromSpec_primeIdealOf ⟨y₁, hle hy₁⟩
    have hs' : hV.fromSpec N ⤳ hV.fromSpec (hV.primeIdealOf ⟨y₁, hle hy₁⟩) := by
      rw [e]; exact hs
    have h3 : N ⤳ hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp hs'
    have h4 : N ≤ hV.primeIdealOf ⟨y₁, hle hy₁⟩ := (PrimeSpectrum.le_iff_specializes _ _).mpr h3
    have h5 : N = hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      PrimeSpectrum.ext (hN.eq_of_le (hV.primeIdealOf ⟨y₁, hle hy₁⟩).isPrime.ne_top h4)
    rw [h5]; exact e.symm
  refine ⟨hcl, (hV₂.primeIdealOf ⟨_, hy⟩).asIdeal, ?_, ?_⟩
  · obtain ⟨N₂, hN₂, -, hs⟩ := exists_max_specializes hV₂ _ hy
    have e := hcl _ (fromSpec_mem hV₂ N₂) hs
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have : N₂ = hV₂.primeIdealOf ⟨_, hy⟩ :=
      hV₂.fromSpec.isOpenEmbedding.injective (e.trans e2.symm)
    rw [← this]; exact hN₂
  · intro a
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have h := hV₂.fromSpec_preimage_basicOpen a
    have h' : hV₂.fromSpec (hV₂.primeIdealOf ⟨_, hy⟩) ∈ Y.basicOpen a ↔
        hV₂.primeIdealOf ⟨_, hy⟩ ∈ PrimeSpectrum.basicOpen a := by
      rw [← h]; rfl
    rw [e2, PrimeSpectrum.mem_basicOpen] at h'
    exact (not_iff_comm.mp h'.symm).symm

end GlobalTheory.ClosedPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadPolarisedAbelianVarietyFinitelyManyP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SpreadPolAV

theorem exists_spread : ∀ (F Ω : Type) [Field F] [Field Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (I : Type) [Finite I] (y : I → (baseOver (Sp Ω) ⟶ A.A)), ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : Algebra F T) (jT : T →+* Ω) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left) (y₀ : I → (baseOver (Sp T) ⟶ P.A)), Algebra.FiniteType F T ∧ Function.Injective jT ∧ jT.comp (algebraMap F T) = em ∧ IsGrpPullback A.A P.A (spMap jT) φ ∧ LBIso A.L (P.L.pull φ) ∧ ∀ i, (y i).left ≫ φ = spMap jT ≫ (y₀ i).left := by
  classical
  intro F Ω _ _ em A I _ y
  obtain ⟨R, P₀, φ₀, ftR, -, H₀, iso₀⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring Ω A
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have := P₀.smoothDim
  have : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g _
  have : LocallyOfFinitePresentation P₀.A.hom := inferInstance

  have hx : ∀ i, ((y i).left ≫ φ₀) ≫ P₀.A.hom = spMap (algebraMap R Ω) := by
    intro i
    rw [Category.assoc, H₀.1.w, ← Category.assoc, Over.w (y i)]
    exact Category.id_comp _
  obtain ⟨R', y', hR', -, hy'⟩ :=
    GlobalTheory.Spread.exists_fg_points P₀.A.hom (fun i => (y i).left ≫ φ₀) hx ⊥ Subalgebra.fg_bot
  have ftR' : Algebra.FiniteType ℤ R' :=
    Algebra.FiniteType.trans ftR ((Subalgebra.fg_iff_finiteType R').1 hR')
  obtain ⟨s₀, hs₀⟩ := ftR'.out

  letI : Algebra F Ω := em.toAlgebra
  let f₀ : R' →ₐ[ℤ] Ω := R'.val.restrictScalars ℤ
  let T : Subalgebra F Ω := Algebra.adjoin F (f₀ '' (s₀ : Set R'))
  have hTfg : T.FG := ⟨s₀.image f₀, by rw [Finset.coe_image]⟩
  have hR'T : ∀ z ∈ R', z ∈ T := by
    intro z hz
    have h₁ : (⟨z, hz⟩ : R') ∈ Algebra.adjoin ℤ (s₀ : Set R') := by rw [hs₀]; trivial
    have h₂ : f₀ ⟨z, hz⟩ ∈ Algebra.adjoin ℤ (f₀ '' (s₀ : Set R')) := by
      rw [← AlgHom.map_adjoin]
      exact Subalgebra.mem_map.2 ⟨_, h₁, rfl⟩
    have key : Algebra.adjoin ℤ (f₀ '' (s₀ : Set R')) ≤ T.restrictScalars ℤ :=
      Algebra.adjoin_le (Algebra.subset_adjoin (R := F))
    exact key h₂
  have hRT : ∀ r ∈ R, r ∈ T := fun r hr => hR'T r (R'.algebraMap_mem (⟨r, hr⟩ : R))
  let g : R →+* T := R.subtype.codRestrict T fun r => hRT r r.2
  let incl : R' →+* T := R'.val.toRingHom.codRestrict T fun z => hR'T z z.2
  let jT : T →+* Ω := T.val.toRingHom
  have e₁ : spMap jT ≫ spMap g = spMap R.subtype := by
    rw [← Spec.map_comp]; rfl
  have e₂ : spMap jT ≫ spMap incl = spMap R'.val.toRingHom := by
    rw [← Spec.map_comp]; rfl
  have e₃ : spMap incl ≫ spMap (algebraMap R R') = spMap g := by
    rw [← Spec.map_comp]; rfl

  let P : PolAV (Sp T) := GlobalTheory.AmpleSymModel.polPull P₀ (spMap g)
  have Gp : IsGrpPullback P.A P₀.A (spMap g) (pullback.fst P₀.A.hom (spMap g)) :=
    isGrpPullback_pullback P₀.A (spMap g)
  have w : φ₀ ≫ P₀.A.hom = (A.A.hom ≫ spMap jT) ≫ spMap g := by
    rw [Category.assoc, e₁]; exact H₀.1.w
  let φ : A.A.left ⟶ P.A.left := Gp.1.lift _ _ w
  have hφ : φ ≫ pullback.fst P₀.A.hom (spMap g) = φ₀ := Gp.1.lift_fst _ _ w
  have hφ' : φ ≫ P.A.hom = A.A.hom ≫ spMap jT := Gp.1.lift_snd _ _ w
  have hu : ∀ i, (spMap incl ≫ y' i) ≫ P₀.A.hom = 𝟙 (Sp T) ≫ spMap g := by
    intro i
    rw [Category.assoc, (hy' i).1, e₃, Category.id_comp]
  let y₀ : I → (baseOver (Sp T) ⟶ P.A) := fun i =>
    Over.homMk (Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i)) (Gp.1.lift_snd _ _ (hu i))
  refine ⟨T, inferInstance, inferInstance, inferInstance, jT, P, φ, y₀,
    (Subalgebra.fg_iff_finiteType T).1 hTfg, Subtype.val_injective, RingHom.ext fun _ => rfl,
    Gp.cancel (H₀.congr e₁.symm hφ.symm) hφ',
    GlobalTheory.KeyTf.lbIso_pull_pull_of_comp A.isLB P₀.isLB hφ iso₀, fun i => ?_⟩
  apply Gp.1.hom_ext
  · change (y i).left ≫ φ ≫ pullback.fst P₀.A.hom (spMap g) =
      spMap jT ≫ Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i) ≫ pullback.fst P₀.A.hom (spMap g)
    rw [hφ, Gp.1.lift_fst, ← Category.assoc, e₂, (hy' i).2]
  · change (y i).left ≫ φ ≫ P.A.hom = spMap jT ≫ Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i) ≫ P.A.hom
    rw [hφ', Gp.1.lift_snd, ← Category.assoc, Over.w (y i)]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
end GlobalTheory.SpreadPolAV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftSystemHomOfFiltrationEq
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem sysHom_of_K_eq : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Good s₀ → RhoBC hI hk s₀ → ∀ S S' : Sys I π s₀, S.Full hI → S.K hI = S'.K hI → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hG hρ S S' hF hK
  obtain ⟨Φ⟩ := _root_.GlobalTheory.LiftSys.locIso_nonempty R R₀ I hI π hπ hk X₀ s₀ S S'
  obtain ⟨θ, v, hθ, hv, hvI, hvs⟩ := _root_.GlobalTheory.LiftSys.exists_defect_cocycle R R₀ I hI π hπ hk X₀ s₀ S S' Φ

  have hcl : ∀ w, H1.mk _ (v w) = 0 := by
    intro w
    obtain ⟨f, hf⟩ := hG.surj w
    obtain ⟨c', hc'⟩ := hρ.1 (Form.cl s₀ f)
    have hmem : c' ∈ S.K hI ⊔ I • (⊤ : Submodule R (Cr hI π s₀)) :=
      (_root_.GlobalTheory.LiftSys.Sys.mem_K_sup_iff R R₀ I hI π hπ hk X₀ s₀ S hρ hF c').2 (by rw [hc', hodgeFiltration_eq_range]; exact ⟨f, rfl⟩)
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hmem
    have hρz : rho hI hk s₀ z = 0 := (hρ.2 z).2 hz
    have hfo : FormOf hI hk y w := ⟨f, by rw [← hc', map_add (f := _), hρz, add_zero], hf⟩
    have hm := _root_.GlobalTheory.LiftSys.r_eq_neg_defect R R₀ I hI π hπ hk X₀ s₀ hG.const S S' Φ θ hθ y hy w hfo (v w) (hv w)
    have hy' : y ∈ S'.K hI := hK ▸ hy
    have h0 : S'.r hI y = 0 := hy'
    rw [h0] at hm
    exact neg_eq_zero.1 hm.symm

  let W : Submodule R (C0 S'.F) :=
    { carrier := {g | S'.IsIdealValuedLiftSystemCochain g}
      add_mem' := fun {g g'} hg hg' U ↦ Ideal.add_mem _ (hg U) (hg' U)
      zero_mem' := fun U ↦ Ideal.zero_mem _
      smul_mem' := fun r g hg U ↦ by
        show r • g U ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hg U) }
  have hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0 := by
    intro r hr m hm
    funext U
    show r • m U = 0
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    have h2 := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (S'.F.obj U)) hrI) (hm U)
    rw [← sq, map_sq hI] at h2
    rw [Algebra.smul_def]
    simpa using h2
  have hq : ∀ w, ∃ m ∈ W, d0 S'.F m = ((Z1 S'.F).subtype.toAddMonoidHom.comp v) w := by
    intro w
    obtain ⟨g, hgI, hg⟩ := _root_.GlobalTheory.LiftSys.cobound_I R R₀ I hI π hπ hk X₀ s₀ hG.const S' (v w) (hvI w) (hcl w)
    exact ⟨g, hgI, hg⟩
  have hv' : ∀ (r : R) w, ((Z1 S'.F).subtype.toAddMonoidHom.comp v) (π r • w) =
      r • ((Z1 S'.F).subtype.toAddMonoidHom.comp v) w := by
    intro r w
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype, hvs]
    rfl
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hG.proj
    (C0 S'.F) (C1 S'.F) W hW (d0 S'.F) _ hv' hq
  exact _root_.GlobalTheory.LiftSys.exists_corr_of_defect R R₀ I hI π hπ hk X₀ s₀ hG.par S S' Φ θ hθ u hu2 hu1 (fun w U V a ↦
    (hv w U V a).symm.trans (congrFun (congrFun (congrFun (hu3 w) U) V) a).symm)

end GlobalTheory.LiftSys
end

