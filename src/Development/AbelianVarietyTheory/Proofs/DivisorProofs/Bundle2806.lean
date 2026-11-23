module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSupNormBallLeGramDet
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDatumStandardLatticeTensorUnimodula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesVacuumInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

open scoped GlobalTheory.VacAny

namespace GlobalTheory.InertSpan

theorem span_translates_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
      Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s hs
  obtain ⟨-, -, -, -, -, -, -, -, -, hAt, hSurj, -⟩ := hC
  have hunr : PsiUnr B.ψ v := (hT.base.inert v w hw).2.2
  have hvac := hT.geo.hM'.vac v
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have key : ∀ x, ((ρ x s : SB _) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (κ x)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    fun x => GlobalTheory.InertAvg.tens_inj v R hR0 (hR _ s.2).1
      ((hρ x s R (hR _ s.2)).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo _ _ v _ (hAt x) _ R (hR _ s.2)))
  have hsurj : ∀ p : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v),
      ∃ x, GlobalTheory.LatVac.locCo G.M'.co v (κ x) = p := by
    intro p
    obtain ⟨x, hx⟩ := hSurj (G.M'.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)))
      (by
        intro u hu
        rw [← LinearEquiv.map_smul]
        convert G.M'.co.e.symm.map_zero using 2
        ext k
        · exact GlobalTheory.LatVac.at_liftV v (p.1 k) u hu
        · exact GlobalTheory.LatVac.at_liftV v (p.2 k) u hu)
    refine ⟨x, ?_⟩
    rw [hx]
    ext k
    · simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]
    · simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]
  have hs0 : (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ≠ 0 := hs ▸ hvac.2.1
  have hcond : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
      x ∈ v.adicCompletionIntegers F := hunr
  have hrange : Set.range (fun p => schr (GlobalTheory.LatVac.psiAt B.ψ v) p (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) =
      (SB (Fin a' × Fin (a + a') → Fv F v)).subtype '' Set.range (fun x => ρ x s) := by
    ext f
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx⟩ := hsurj p
      exact ⟨ρ x s, ⟨x, rfl⟩, by rw [Submodule.subtype_apply, key, hx]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, (key x).symm⟩
  rw [eq_top_iff]
  rintro m -
  have hm := GlobalTheory.SchrSpan.mem_span_schr_of_mem_SB F v (GlobalTheory.LatVac.psiAt B.ψ v) _ hcond _ s.2 hs0 _ m.2
  rw [hrange, Submodule.span_image] at hm
  obtain ⟨n, hn, hnm⟩ := hm
  rwa [← Subtype.ext hnm]

end GlobalTheory.InertSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberMovedDatumSplittingScale
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem stdFst_actO {D : D7} {A WW : HSp D} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E))
    (βA βA' : GL (Fin A.rank) (Lev.EAf D)) (βW βW' : GL (Fin WW.rank) (Lev.EAf D)) (g : GA D A) (h : GA D WW)
    (hfr : ∀ u : WO A WW, IsHalf e u → frMapO A WW βA' βW' (actO A WW g h u) = frMapO A WW βA βW u) (u : WO A WW) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA' βW' (actO A WW g h u) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW u := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  by_cases hu : IsHalf e u
  · rw [hfr u hu]
    have hu' : IsHalf e (actO A WW g h u) := (GlobalTheory.SchrMove.isHalf_actO_iff g h u).2 hu
    by_cases hr : IsIntM (frMapO A WW βA βW u) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW u i j)
    · rw [if_pos ⟨hu', hr⟩, if_pos ⟨hu, hr⟩]
    · rw [if_neg fun hh => hr hh.2, if_neg fun hh => hr hh.2]
  · rw [if_neg fun hh => hu ((GlobalTheory.SchrMove.isHalf_actO_iff g h u).1 hh.1), if_neg fun hh => hu hh.1]

theorem move_fst : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  intro D T L sc G W i j A A' WW X Y hX hY t g h x y hsg hstg hdg hsh hsth hdh hfr
  classical
  have hI := hY.is
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BotFrames.botBeta G i j)
      (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) ((Y.ω t).toSgn true) := hI.weil t
  have hSA : IsSelfDualC (GlobalTheory.Grid.neg A) Y.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1
  have hSW : IsSelfDualC WW Y.rW.Λ := hI.rigW.1
  let g' : GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm g
  have hL : ∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔
      actO (GlobalTheory.Grid.neg A) WW g' h u ∈ (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) :=
    GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ Y.rA.β Y.rW.β hSA hSW hI.rigA.2.1 hI.rigW.2.1
      g' h hstg hsth
  have hvθ := hI.isVac.2.theta
  have hvL := hI.isVac.2.lat
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hec := (hI.idem t).2
  have h0 : (Y.ω t).toSgn true (g', h) Y.vac =
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) • Y.vac := by
    obtain ⟨ι, P, es, h1, h2, he⟩ := ho
    rw [he] at hec hsg hsh hdg hdh
    have h3 : ∀ a ∈ P, ∀ b ∈ P, es a * cA D (es b) = 0 := fun a ha b hb => by
      rw [← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 ha, ← GlobalTheory.PlaceModelSum.mul_sum_orth h1 h2 hb, RingHom.map_mul,
        mul_mul_mul_comm, hec, mul_zero]
    exact GlobalTheory.WeilSplit.om_latVac_sum hW hSA hSW hvθ hvL es P h1 h2 h3 g' h hsg hsh hL x y hdg hdh
  rw [← isStd_lat_eq hY.std hX.std, ← isStd_lat_eq hY.stdW hX.stdW]
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hI.fst t
  refine ⟨⟨T₀, hT₀⟩, fun T' hT' => ?_⟩
  have hth := GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hW.std (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ hSA hSW (Y.e t) ho.idem
    ho.infPart_eq Y.vac hvθ T' hT'
  have hc : ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have pm := GlobalTheory.SchrMove.isPlaceModel_move hW hL hT' hth hc h0
  have hf := hall _ pm
  have hΦ : (fun u => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW Y.rA.β Y.rW.β (actO (GlobalTheory.Grid.neg A) WW g' h u)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β :=
    funext fun u => stdFst_actO _ _ _ X.rA.β Y.rA.β X.rW.β Y.rW.β g h hfr u
  have e1 : Y.ω t (g⁻¹, h⁻¹) = (Y.ω t).toSgn true (g'⁻¹, h⁻¹) := rfl
  have hf' : Y.f t = ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)⁻¹ •
      (Y.ω t).toSgn true (g', h) (T' (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t)
      (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β)) := by
    rw [hf, ← hΦ]; rfl
  rw [e1, hf', map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel,
    Prod.mk_one_one, map_one, Module.End.one_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.BotFrames

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupNormBallCountAsymptoticGramDeterminant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem eventually_poly_mul_pow_le_exp (c C t : ℝ) (n : ℕ) (hC : 1 ≤ C) (ht : Real.log C < t) :
    ∀ᶠ m : ℕ in atTop, c * (m : ℝ) ^ n * C ^ m ≤ Real.exp (t * m) := by
  have hδ : 0 < t - Real.log C := sub_pos.2 ht
  have hc1 : 0 < |c| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop n hδ).bound (c := 1 / (|c| + 1)) (by positivity)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  have hCpos : 0 < C := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hm
  have hexp : Real.exp (t * m) = Real.exp ((t - Real.log C) * m) * C ^ m := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCpos, ← Real.exp_add]; ring_nf
  rw [hexp]
  have hmn : (0 : ℝ) ≤ (m : ℝ) ^ n := by positivity
  have hle : c * (m : ℝ) ^ n ≤ Real.exp ((t - Real.log C) * m) := by
    calc c * (m : ℝ) ^ n ≤ (|c| + 1) * (m : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hmn
      _ ≤ (|c| + 1) * (1 / (|c| + 1) * Real.exp ((t - Real.log C) * m)) :=
          mul_le_mul_of_nonneg_left hm hc1.le
      _ = _ := by field_simp
  exact mul_le_mul_of_nonneg_right hle (by positivity)

theorem count_ball_asymp : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → ∀ g : ℝ, Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g) → ∀ C : ℝ, 1 ≤ C → (∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m))) → ∀ t : ℝ, Real.log C < t → Tendsto (fun m : ℕ => (Real.log ((ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (Real.exp (t * m))).ncard : ℝ) - (r m * (t * m) - Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re / 2 + Real.log (volume {x : Fin (r m) → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
  intro k _ X _ p D hX hS P hP ω r f hf hli g hg C hC hball t ht
  haveI := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hρ := fun σ => _root_.GlobalTheory.HSAmp.exists_isRatio_chernInt k X p D hX hS P.L hP σ (ω σ)
  choose ρ hρr hρ0 _ using hρ
  have hbd : ∀ σ, ∃ b : ℝ, ∀ y, ρ σ y ≤ b := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨b, hb⟩ := (isCompact_range (hρr σ).1).bddAbove
    exact ⟨b, fun y => hb ⟨y, rfl⟩⟩
  choose b hb using hbd
  set B : ℝ := ∑ σ, |b σ| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hρB : ∀ σ y, ρ σ y ≤ B := fun σ y => (hb σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |b σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set K : ℝ := B / D.factorial + 1 with hKdef
  have hK : 1 ≤ K := by
    have : 0 ≤ B / D.factorial := by positivity
    linarith
  set V : ℝ := max 1 (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) with hVdef
  have hV : 1 ≤ V := le_max_left _ _
  have hmorse := _root_.GlobalTheory.HSAmp.Morse.cmb_le k X p D hX hS P hP ω ρ hρr 1 one_pos
  have hr : ∀ᶠ m : ℕ in atTop, (r m : ℝ) ≤ (g + 1) * (m : ℝ) ^ D := by
    filter_upwards [hg.eventually (gt_mem_nhds (lt_add_one g)), eventually_ge_atTop 1] with m hm h1
    have h0 : (0 : ℝ) < (m : ℝ) ^ D := pow_pos (by exact_mod_cast h1) D
    exact ((div_lt_iff₀ h0).1 hm).le
  have hexp := eventually_poly_mul_pow_le_exp (2 * (g + 1) * K * V) C t (2 * D) hC ht
  refine squeeze_zero_norm' (a := fun m : ℕ =>
    2 * ((r m : ℝ) / (m : ℝ) ^ D) * ((Real.log (2 * K * V) + D * Real.log m) / m)) ?_ ?_
  · filter_upwards [hmorse, hr, hexp, eventually_ge_atTop 1] with m hm hrm hem h1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have hm0 : (0 : ℝ) < m := by linarith
    have hmD : (0 : ℝ) < (m : ℝ) ^ D := pow_pos hm0 D
    have hM : 1 ≤ K * (m : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hm1)
    have hcmb : ∀ (c : Fin (r m) → ℂ) σ y, cmb (vals P m 1 (f m)) c σ y ≤
        K * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c := by
      intro c σ y
      have h := hm (Fin (r m)) (f m) (hf m) c σ y
      have hl2 : 0 ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c :=
        finsum_nonneg fun σ => integral_nonneg fun y => by unfold cmb; positivity
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hmD.le) hl2)
      have : ρ σ y / D.factorial ≤ B / D.factorial :=
        div_le_div_of_nonneg_right (hρB σ y) (by positivity)
      linarith
    have hR : 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V) ≤ Real.exp (t * m) := by
      calc 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V)
          ≤ 2 * ((g + 1) * (m : ℝ) ^ D) * C ^ m * (K * (m : ℝ) ^ D * V) := by
            have : 0 ≤ C ^ m * (K * (m : ℝ) ^ D * V) := by
              have : 0 ≤ C := by linarith
              positivity
            nlinarith
        _ = 2 * (g + 1) * K * V * (m : ℝ) ^ (2 * D) * C ^ m := by ring
        _ ≤ _ := hem
    have key := _root_.GlobalTheory.BallGram.count_ball_gram k X p D hX hS P ω (m : ℤ) 1 (r m) (f m) (hf m) (hli m) (K * (m : ℝ) ^ D) V (C ^ m)
      (Real.exp (t * m)) hM hV (le_max_right _ _) (by positivity) (Real.exp_pos _) hcmb (hball m h1) hR
    rw [Real.log_exp] at key
    have hlog : Real.log (2 * (K * (m : ℝ) ^ D * V)) = Real.log (2 * K * V) + D * Real.log m := by
      have e : 2 * (K * (m : ℝ) ^ D * V) = (2 * K * V) * (m : ℝ) ^ D := by ring
      rw [e, Real.log_mul (by positivity) hmD.ne', Real.log_pow]
    have hmD1 : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hmD1, div_le_iff₀ hmD1]
    refine key.trans (le_of_eq ?_)
    rw [hlog, pow_succ]
    field_simp
  · have h1 : Tendsto (fun m : ℕ => 2 * ((r m : ℝ) / (m : ℝ) ^ D)) atTop (𝓝 (2 * g)) := hg.const_mul 2
    have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun m : ℕ => (Real.log (2 * K * V) + D * Real.log m) / m) atTop (𝓝 0) := by
      have := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log (2 * K * V))).add
        ((hl.comp tendsto_natCast_atTop_atTop).const_mul (D : ℝ))
      simp only [mul_zero, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply]
      ring
    simpa using h1.mul h2

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataUnitaryType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.tens_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → Nontrivial D.toPre.X → 1 ≤ r → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∃ Dm : Datum H, PelOK Dm D'.toPre o := by
  have hA := _root_.GlobalTheory.finrank_dvd_of_ringOfIntegers_to_matrix
  have hB := GlobalTheory.T.tensorDegenerationData_torsion_isometry_onto
  intro R _ _ _ hR E _ _ _ H D D' r W hpos hdet T ρ hadj hw0 hX hr _ o hact hpsi
  obtain ⟨s, hs⟩ := hA E ρ
  obtain ⟨Dm, e, hp, hq, he, hEF⟩ := _root_.GlobalTheory.UnitaryStd.exists_datum E H W hpos hdet ρ hadj hw0
    (D.toPre.P.g + Module.finrank ℤ D.toPre.X) s hs
  obtain ⟨hrk, hlie⟩ := GlobalTheory.T.lieMultiplicity_and_rank_tensorData_lattice R hR E H D D' W hpos hdet T ρ o hact s hs
  have hs0 : s ≠ 0 := by rintro rfl; omega
  have hX0 : 0 < Module.finrank ℤ D.toPre.X := Module.finrank_pos
  refine ⟨Dm, hp.trans hq.symm, ?_, hpsi, fun F _ _ _ => ⟨fun τ => ⟨s * D.toPre.P.g, hlie F τ, ?_⟩, fun ζ hζ hζ' => ?_⟩⟩
  · rw [hp]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hs0 (by omega))
  · rw [hrk, hp]; ring
  · obtain ⟨ev, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.SympQ.compatible_symplectic_bases R hR D F ζ hζ hζ' _ rfl
    exact hB R hR E H D D' W hpos hdet T ρ hadj hw0 o hact hpsi Dm _ e rfl he hEF F ζ hζ hζ' ev h1 h2 h3 h4 h5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCoordinatesSectionExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (f : Γ(X, U)) :
    resG X h₂ (resG X h₁ f) = resG X (h₂.trans h₁) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem chart_sec (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k]
    [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ)
    (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (θ : SecAt t.G t.PP.L M.pt) (pt : Fin (n + 1) → (Over.mk M.pt ⟶ t.G))
    (hn : Geo.Tor.IsNormalScheme M.Z) (ho : Odd m) (h3 : 3 ≤ m) (hu : IsUnit (m : k)) (hp : PolFib t.G t.PP.L g M.pt)
    (hg : IsGenSec t.G t.PP.L _ θ) (hl : ThList t.G t.PP.L t.PP.rig m M.pt θ pt c) (hc : PCrd (M.pt ≫ h) c)
    (a : Fin (n + 1)) : ∃ s : LocSec t.G t.PP.L (h ⁻¹ᵁ chart k n a), IsLocSec s ∧
      ((((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt s ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • SecM.ofSec t.G θ)) ∧
      FibNz s (h ⁻¹ᵁ chart k n a)) := by
  by_cases hne : ((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty
  · have hloc := _root_.GlobalTheory.UMin.ThBdl.exists_locSec_theta_chart E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc a
    choose N hzN hNle s hs hgs hfs using hloc
    let κ := {z : M.Z // z ∈ h ⁻¹ᵁ chart k n a}
    have hsup : (⨆ z : κ, N z.1 z.2) = h ⁻¹ᵁ chart k n a :=
      le_antisymm (iSup_le fun z => hNle z.1 z.2) fun z hz =>
        TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzN z hz⟩
    obtain ⟨s', hs', hres⟩ := _root_.GlobalTheory.UMin.ThBdl.locSec_glue M.Z t.G t.PP.L (h ⁻¹ᵁ chart k n a) κ (fun z => N z.1 z.2) (fun z => s z.1 z.2)
      (fun z => hNle z.1 z.2) hsup (fun z => hs z.1 z.2) (fun z z' i =>
        _root_.GlobalTheory.UMin.ThBdl.locSec_eq_of_genIs M.Z t.G t.semi t.PP.L Ω M.pt M.gen _ _ _ _ _ (hgs z.1 z.2) (hgs z'.1 z'.2) i)
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.UMin.ThBdl.Glued.glued M.Z t.G t.PP.L Ω M.pt _ κ (fun z => N z.1 z.2) (fun z => s z.1 z.2) s' _
      (fun z => hNle z.1 z.2) hsup hres (fun z => hgs z.1 z.2) (fun z => hfs z.1 z.2)
    exact ⟨s', hs', fun _ => h1 ⟨⟨hne.some, hne.some_mem⟩⟩, h2⟩
  · refine ⟨0, isLocSec_zero, fun h' => absurd h' hne, fun K _ _ x hx => absurd ?_ hne⟩
    exact ⟨_, hx ⟨IsLocalRing.closedPoint K, rfl⟩⟩

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace

theorem app_resG {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (e : V ≤ U) (x : Γ(X, U)) :
    (f.app V).hom (resG X e x) = resG Y (fun _ hy => e hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) ((f.app U).hom x) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, f.naturality]
  rfl

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (hV : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)) : valF y V (resG X e f) = valF y U f := by
  unfold valF
  rw [dite_eq_left hV, dite_eq_left (hV.trans fun x hx => show y x ∈ U from e (show y x ∈ V from hx))]
  congr 1
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl

theorem val_res' {X : Scheme.{0}} {U V : X.Opens} (e : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res e u : Γ(X, V)ˣ) : Γ(X, V)) = resG X e (u : Γ(X, U)) := rfl

theorem val_pullU' {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    ((pullU f U u : Γ(Y, f ⁻¹ᵁ U)ˣ) : Γ(Y, f ⁻¹ᵁ U)) = (f.app U).hom (u : Γ(X, U)) := rfl
end GlobalTheory.UMin.ThBdl

namespace GlobalTheory.UMin.ThBdl
open ProjSpace


set_option maxHeartbeats 2000000 in
theorem pull_theta_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (t : SAB H M.Z) (g m n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n), Geo.Tor.IsNormalScheme M.Z → Odd m → 3 ≤ m → IsUnit (m : k) → PolFib t.G t.PP.L g M.pt → HasTh t.G t.PP.L t.PP.rig m M.pt c → PCrd (M.pt ≫ h) c → ∃ σ : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).Sec, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M.Z), ∃ (y : Sp K ⟶ t.G.left) (j : _), y ≫ t.G.hom = x ∧ Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U j ∧ valF y _ (σ.f j) ≠ 0 := by
  intro E _ _ _ H k Ω _ _ _ _ _ M t g m n c h hn ho h3 hu hp hth hc
  obtain ⟨θ, pt, hg, hl⟩ := hth
  choose s hs hgs hfs using chart_sec E H k Ω M t g m n c h θ pt hn ho h3 hu hp hg hl hc
  have hcross := _root_.GlobalTheory.UMin.ThBdl.cross_ratio_sections k Ω M t.G t.PP.L n c h (SecM.ofSec t.G θ) hc (_root_.GlobalTheory.UMin.ThBdl.locSec_eq_of_genIs M.Z t.G t.semi t.PP.L Ω M.pt M.gen)
  have hle : ∀ p : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).ι,
      (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U p ≤
        t.PP.L.U p.1 ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (p.2 PUnit.unit PUnit.unit)) := fun p y hy =>
    ⟨hy.1, Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩
  refine ⟨⟨fun p => resG _ (hle p) (s _ p.1), fun p q => ?_⟩, fun K _ _ x => ?_⟩
  · obtain ⟨i, pj⟩ := p
    obtain ⟨i', qj⟩ := q
    have eB : ∀ (Y : Scheme.{0}) (φ : Y ⟶ M.Z) (u v : PUnit → PUnit → Fin (n + 1)),
        ((((ProjSpace.O1 k n).pull h).pull φ).g u v : Γ(Y, _)) =
          resG Y (fun y hy => ⟨Set.mem_iInter.1 (Set.mem_iInter.1 hy.1 PUnit.unit) PUnit.unit,
              Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit⟩ :
            (((ProjSpace.O1 k n).pull h).pull φ).U u ⊓ (((ProjSpace.O1 k n).pull h).pull φ).U v ≤
              φ ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (u PUnit.unit PUnit.unit) ⊓ chart k n (v PUnit.unit PUnit.unit))))
            ((φ.app _).hom ((h.app _).hom (ratioOn (chart k n (u PUnit.unit PUnit.unit) ⊓
              chart k n (v PUnit.unit PUnit.unit)) _ inf_le_left (v PUnit.unit PUnit.unit)))) := by
      intro Y φ u v
      have e1 := ProjSpace.linComb_punit_g ((ProjSpace.O1 k n).pull h) φ 1 u v
      have e2 := ProjSpace.linComb_punit_g (ProjSpace.O1 k n) h 1 (u PUnit.unit) (v PUnit.unit)
      rw [zpow_one] at e1 e2
      erw [e1]
      erw [e2]
      erw [val_res', val_pullU', val_res', val_pullU']
      rw [O1_g_eq_ratioUnit_chart_inf, val_ratioUnit]
      erw [app_resG, resG_resG']
      rfl
    have hW1 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n (pj PUnit.unit PUnit.unit) ⊓ chart k n (qj PUnit.unit PUnit.unit))) :=
      fun y hy => ⟨hy.1.1, (hle _ hy.1).2, (hle _ hy.2).2⟩
    have hW2 : (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i, pj) ⊓
        (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U (i', qj) ≤
        t.PP.L.U i ⊓ t.PP.L.U i' ⊓ t.G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n (qj PUnit.unit PUnit.unit)) :=
      fun y hy => ⟨⟨hy.1.1, hy.2.1⟩, (hle _ hy.2).2⟩
    have e1 := congrArg (resG t.G.left hW1) (hcross _ _ (s _) (s _) (hgs _) (hgs _) i)
    have e2 := congrArg (resG t.G.left hW2) (hs (qj PUnit.unit PUnit.unit) i i')
    rw [map_mul] at e1 e2
    erw [resG_resG', resG_resG', resG_resG'] at e1
    erw [resG_resG', resG_resG', resG_resG'] at e2
    show resG _ _ (resG _ (hle (i, pj)) (s (pj PUnit.unit PUnit.unit) i)) = _ *
      resG _ _ (resG _ (hle (i', qj)) (s (qj PUnit.unit PUnit.unit) i'))
    rw [resG_resG', resG_resG']
    erw [Units.val_mul, val_res', val_res', eB, resG_resG']
    rw [e1, e2, mul_left_comm, ← _root_.mul_assoc]
    rfl
  · obtain ⟨a, ha⟩ := exists_mem_chart k n (h (x (IsLocalRing.closedPoint K)))
    have hx : Set.range x ⊆ h ⁻¹ᵁ chart k n a := by
      rintro _ ⟨w, rfl⟩
      rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
      exact ha
    obtain ⟨y, i, hyx, hyr, hv⟩ := hfs a K x hx
    have hyr' : Set.range y ⊆ (CechPic.tens t.PP.L (((ProjSpace.O1 k n).pull h).pull t.G.hom)).U
        (i, fun _ _ => a) := fun _ hw =>
      ⟨(hyr hw).1, Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => (hyr hw).2⟩
    refine ⟨y, (i, fun _ _ => a), hyx, hyr', ?_⟩
    show valF y _ (resG _ (hle (i, fun _ _ => a)) (s a i)) ≠ 0
    rwa [valF_resG y _ ((GlobalTheory.ZH.top_le_preimage_iff y _).2 hyr')]

end GlobalTheory.UMin.ThBdl
end
end

