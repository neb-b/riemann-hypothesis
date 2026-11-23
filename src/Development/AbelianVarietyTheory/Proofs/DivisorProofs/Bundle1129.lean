module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.LayerLeGeneratedTensorFock
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bridge
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalModelRegularUnitValues
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem model_regAt_unitAt_values : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → (∀ (y : Y) (f : X.functionField), RegAt (π y) f → RegAt y (φ f)) ∧ (∀ (y : Y) (f : X.functionField), UnitAt (π y) f → UnitAt y (φ f)) ∧ (∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)), φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a)) ∧ ∀ (σ : k →+* ℂ) (z : CxPts q σ) (f : X.functionField), RegAt (π (under z)) f → ratVal (φ f) z = ratVal f (GlobalTheory.Points.PtsOver.map π hπ _ z) := by
  intro k _ X Y _ _ p q π hπ φ hM
  have h3 : ∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)),
      φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a) := by
    intro U h h' a
    have e1 := algebraMap_germ (X := X) (show π (genericPoint Y) ∈ U from h') a
    have e2 := algebraMap_germ (X := Y) h' (π.app U a)
    rw [← e1, hM.compat, ← e2]
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply π U (genericPoint Y) h' a
  refine ⟨?_, ?_, h3, ?_⟩
  · rintro y f ⟨a, rfl⟩
    exact ⟨π.stalkMap y a, (hM.compat y a).symm⟩
  · rintro y f ⟨a, ha, rfl⟩
    exact ⟨π.stalkMap y a, ha.map _, (hM.compat y a).symm⟩
  · intro σ z f hf
    obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
    have hz : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := mem_ptsIn.2 hU
    have hz' : GlobalTheory.Points.PtsOver.map π hπ _ z ∈ ptsIn p σ U := mem_ptsIn.2 (by first | exact hU | simpa [Function.comp_apply] using hU)
    rw [h3 U _ (gen_mem (show under z ∈ π ⁻¹ᵁ U from hU)) a, ratVal_fnOf hz, ratVal_fnOf hz',
      ev_app π hπ]

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramifiedStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockLevels_eq_integralGL_of_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ), (∀ u ∈ GlobalTheory.LFun.KGL w (n := 1), μ (GeneralLinearGroup.det u) = 1) →
    lev₁ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := a) ∧ lev₂ h w (GlobalTheory.LFun.KGL w (n := n)) μ = GlobalTheory.LFun.KGL w (n := b) := by
  first | exact @GlobalTheory.BCT.CtLevel.lev_KGL_of_unram | exact GlobalTheory.BCT.CtLevel.lev_KGL_of_unram | (intros; apply GlobalTheory.BCT.CtLevel.lev_KGL_of_unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsoLocalUnitsCompOfPullbackSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem gs_comp_stalkMap {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U)
    (a : Γ(X, U)) :
    gs (r ≫ F) z U a = (Scheme.Hom.stalkMap r z).hom (gs F (r z) U a) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem gm_val_stalkMap {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : r z ∈ V) (u : Γ(Y, V)ˣ) :
    ((gm r z V u : (Z.presheaf.stalk z)ˣ) : Z.presheaf.stalk z) =
      (Scheme.Hom.stalkMap r z).hom ((gm (𝟙 Y) (r z) V u : (Y.presheaf.stalk (r z))ˣ) : Y.presheaf.stalk (r z)) := by
  rw [← gs_unit r z V h, ← gs_unit (𝟙 Y) (r z) V h, gs_stalkMap r z V h]

theorem gw_comp_of_rel : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  intro X Y' Y b' β b hb A H' H w' v w ι s s' s'' h₁ h₂ h₃ hc z k k' k'' hk hk' hk''
  subst hb

  have hz : z ∈ ⨆ j, nonzeroLocus (s'' j) := by rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  obtain ⟨k₀, hk₀, hu₀⟩ := (mem_nonzeroLocus (s'' j) z).1 hj
  have hu : IsUnit (gs (𝟙 Y) z (H.U k'') ((s'' j).f k'')) := by
    rw [gs_compat (s'' j) (𝟙 Y) z hk'' hk₀]
    exact (Units.isUnit _).mul hu₀
  have hkb : b' (β z) ∈ A.U k := hk
  have e₁ := h₁ j (β z) k k' hkb hk'
  have e₂ := h₂ j z k' k'' hk' hk''
  have e₃ := h₃ j z k k'' hk hk''
  have hV : β z ∈ (A.pull b').U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hkb, hk'⟩
  have e₁' := congrArg (Scheme.Hom.stalkMap β z).hom e₁
  rw [map_mul, ← gs_comp_stalkMap β b' z _ hkb, ← gs_stalkMap β z _ hk'] at e₁'
  have hw' : ((Geo.Tor.gw w' β z k k' : (Y.presheaf.stalk z)ˣ) : Y.presheaf.stalk z) =
      (Scheme.Hom.stalkMap β z).hom ((Geo.Tor.gw w' (𝟙 _) (β z) k k' : (Y'.presheaf.stalk (β z))ˣ) :
        Y'.presheaf.stalk (β z)) :=
    gm_val_stalkMap β z _ hV _
  rw [← hw', e₂] at e₁'
  rw [e₃, ← _root_.mul_assoc, ← Units.val_mul] at e₁'
  exact Units.ext (hu.mul_left_inj.1 e₁')

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelPowersOfCechLineBundles
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.CancelPow

variable {X Y : Scheme.{0}}

theorem pw_tw (M H : LB X) (t a : ℤ) : AbLaw.pw (tw M H t) a = tw (AbLaw.pw M a) H (t * a) := by
  have : (AbLaw.pw (tw M H t) a).g = (tw (AbLaw.pw M a) H (t * a)).g := by
    funext p q
    change (res _ (M.g p.1 q.1) * (res _ (H.g p.2 q.2 ^ (-t)))⁻¹) ^ a =
      res _ (M.g p.1 q.1 ^ a) * (res _ (H.g p.2 q.2 ^ (-(t * a))))⁻¹
    simp only [map_zpow, map_inv, zpow_neg, inv_inv, zpow_mul]
    exact mul_zpow _ _ _
  exact congrArg (fun g => (⟨(tw M H t).ι, (tw M H t).U, g⟩ : LB X)) this

theorem lbIso_tw_congr_right {A H H' : LB X} (hA : A.IsLB) (t : ℤ) (h : LBIso H H') :
    LBIso (tw A H t) (tw A H' t) := by
  obtain ⟨w, hw⟩ := h
  have l₁ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ A.U p.1.1 ⊓ A.U p.2.1 :=
    fun p x hx => ⟨hx.1.1, hx.2.1⟩
  have l₂ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ H'.U p.1.2 ⊓ H.U p.2.2 :=
    fun p x hx => ⟨hx.1.2, hx.2.2⟩
  have v : ∀ (x : X) (p : (A.ι × H'.ι) × (A.ι × H.ι)), x ∈ (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t) =
        gm (𝟙 X) x _ (A.g p.1.1 p.2.1) * gm (𝟙 X) x (H'.U p.1.2 ⊓ H.U p.2.2) (w.s (p.1.2, p.2.2)) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t)
    ?_
  intro x p q h₁ h₂ h₃ h₄
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (GlobalTheory.LBAlg.gm_tw A H' t (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩) (congrArg (·⁻¹) (GlobalTheory.LBAlg.gm_tw A H t (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩)))
    (v x q ⟨h₃, h₄⟩)).symm)
  rw [GlobalTheory.LBAlg.germs_of_isGen hw x (p.1.2, p.2.2) (q.1.2, q.2.2) h₁.2 h₂.2 h₃.2 h₄.2,
    ← gm_cocycle hA (𝟙 X) x h₁.1 h₂.1 h₃.1, ← gm_cocycle hA (𝟙 X) x h₂.1 h₃.1 h₄.1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem cancel_pw : (∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (H M : LB X) (N : LB Y) (a : ℤ), H.IsLB → M.IsLB → N.IsLB → LBIso (GlobalTheory.AbLaw.pw N a) (H.pull b) → LBIso (GlobalTheory.AbLaw.pw N (a + 1)) (M.pull b) → LBIso N ((GlobalTheory.AbLaw.tw M H (-1)).pull b)) ∧ ∀ (X : Scheme.{0}) (H M : LB X) (a : ℤ), H.IsLB → M.IsLB → LBIso (GlobalTheory.AbLaw.pw H (a + 1)) (GlobalTheory.AbLaw.pw M a) → LBIso H (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M H (-1)) a) := by
  refine ⟨fun X Y b H M N a hH hM hN e₁ e₂ => ?_, fun X H M a hH hM e => ?_⟩
  · have hP : (M.pull b).IsLB := pull_isLB hM b
    have hQ : (H.pull b).IsLB := pull_isLB hH b
    have k₁ : LBIso N (tw (tw N (H.pull b) 1) (H.pull b) (-1)) := GlobalTheory.LBAlg.lbIso_tw_tw hN hQ 1
    have k₂ : LBIso (tw N (H.pull b) 1) (tw N (AbLaw.pw N a) 1) := lbIso_tw_congr_right hN 1 e₁.symm
    have k₃ : tw N (AbLaw.pw N a) 1 = tw N N a := by
      simp only [tw, GlobalTheory.Algebraise.pw_pw]
      congr 2
      ring
    have k₄ : LBIso (tw N N a) (M.pull b) :=
      LBIso.trans (isLB_tw hN hN a) (isLB_pw hN (a + 1)) hP (GlobalTheory.Algebraise.lbIso_tw hN a).symm e₂
    have k₅ : LBIso (tw N (H.pull b) 1) (M.pull b) :=
      LBIso.trans (isLB_tw hN hQ 1) (isLB_tw hN (isLB_pw hN a) 1) hP k₂ (k₃ ▸ k₄)
    have k₆ : LBIso (tw (tw N (H.pull b) 1) (H.pull b) (-1)) (tw (M.pull b) (H.pull b) (-1)) :=
      GlobalTheory.LBAlg.lbIso_tw_congr hQ (-1) k₅
    have k₇ : LBIso (tw (M.pull b) (H.pull b) (-1)) ((tw M H (-1)).pull b) :=
      LBIso.chartPull (GlobalTheory.LBAlg.chartPullTw (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M b b rfl)
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull H b b rfl) (-1))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (tw M H (-1)) b b rfl) (GlobalTheory.LBAlg.lbIso_self (isLB_tw hM hH (-1)))
    exact LBIso.trans hN (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₁
      (LBIso.trans (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (isLB_tw hP hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₆ k₇)
  · have h₁ : LBIso (tw H H a) (AbLaw.pw M a) :=
      LBIso.trans (isLB_tw hH hH a) (isLB_pw hH (a + 1)) (isLB_pw hM a) (GlobalTheory.Algebraise.lbIso_tw hH a).symm e
    have h₂ : LBIso (tw (tw H H a) H (-a)) (tw (AbLaw.pw M a) H (-a)) := GlobalTheory.LBAlg.lbIso_tw_congr hH (-a) h₁
    have h₃ : AbLaw.pw (tw M H (-1)) a = tw (AbLaw.pw M a) H (-a) := by
      rw [pw_tw]
      congr 1
      ring
    rw [h₃]
    exact LBIso.trans hH (isLB_tw (isLB_tw hH hH a) hH (-a)) (isLB_tw (isLB_pw hM a) hH (-a))
      (GlobalTheory.LBAlg.lbIso_tw_tw hH hH a) h₂

end GlobalTheory.CancelPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultiple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PairStep

theorem eff_divOfSec_of_sec {X : Scheme.{0}} [IsIntegral X] {L : LB X} (hL : L.IsLB) (s : L.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) : (divOfSec hL s hs).Eff := by
  refine CartierDiv.eff_iff.2 fun y g hg => ?_
  obtain ⟨i, hi⟩ := exists_chart hL y
  have h1 := (presents_divOfRatSec hL (isRatSec_ratOfSec s hs)).isEqn i y hi
  have hu := h1.iff_unitAt.1 hg
  have hr : RegAt y (ratOfSec s hs i : X.functionField) := by
    rw [val_ratOfSec (gen_mem hi)]
    exact regAt_fnOf hi (gen_mem hi) _
  have := hu.regAt.mul hr
  rwa [div_mul_cancel₀ _ (Units.ne_zero _)] at this

theorem qNum_divOfSec : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (hN : N.IsLB) (l m : ℕ) (s : (lbPow N l).Sec) (hs : genericPoint X ∈ nonzeroLocus s), 0 < m → (divOfSec (isLB_lbPow hN l) s hs).Eff ∧ QNum p N ((l : ℚ) / m) (qWeil (divOfSec (isLB_lbPow hN l) s hs) m) := by
  intro X _ _ p hp N hN l m s hs hm
  have hE := eff_divOfSec_of_sec (isLB_lbPow hN l) s hs
  refine ⟨hE, m, _, hm, hE, rfl, fun C hC => ?_⟩
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  letI := algebraΓOfHom p
  have hcls : toPic (divOfSec (isLB_lbPow hN l) s hs) = cls _ (isLB_lbPow hN l) :=
    (presents_divOfRatSec (isLB_lbPow hN l) (isRatSec_ratOfSec s hs)).toPic_eq
  rw [interNumRed_one_congr (isLB_toLB _) (isLB_lbPow hN l) hcls, hC.interNumRed_lbPow hH hN l]
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirScalarStableSumSpace
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem casimirScalar_stableSumSpace : BuildY := by
  intro n ε H _ _ σ D E hσ hD c hc L hLf hLK
  have hE : IsGlRep E := hD.glRep
  have hLk : IsKStableSub ε E L :=
    isKStableSub_of_kStable hσ hD L hLf fun k hk v hv => ⟨sigD hD hk v, hLK k hk v hv, rfl⟩
  set Dop := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDop
  let Y0 : Submodule ℂ (TensorProduct ℂ D (Fock n)) := tensFock L ⊓ physicalSubspace ε
  have hA : ∀ a b, ε a = ε b → ∀ x ∈ Y0, diagE ε (eT E) cpT cmT a b x ∈ Y0 :=
    fun a b hab x hx => ⟨tensorFock_diagAction_stable ε hLk hab hx.1, (physSub_stable ε E).2.1 a b x hx.2⟩
  have hD2 : ∀ y ∈ Y0, Dop (Dop y) ∈ Y0 := by
    intro y hy
    have h2 := LinearMap.congr_fun (two_D_sq (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε) y
    rw [LinearMap.smul_apply, Module.End.mul_apply] at h2
    have hcas : casimir (eT (n := n) E) y = c • y := by
      rw [TRGap.casimir_eT]
      exact map_eq_smul_of_tensFock (fun v _ => hc v) hy.1
    have hmem : (2 : ℂ) • Dop (Dop y) ∈ Y0 := by
      rw [hDop, h2]
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
        LinearMap.sum_apply]
      rw [hcas]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)) ?_)
        (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hA a a rfl y hy)))
      simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb =>
        hA a b (Finset.mem_filter.1 hb).2.symm _ (hA b a (Finset.mem_filter.1 hb).2 y hy)
    have := Submodule.smul_mem _ (1 / 2 : ℂ) hmem
    rwa [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at this
  have hG0 : ∀ z ∈ Y0, gradT z ∈ Y0 := fun z hz =>
    ⟨tensFock_lTensor_stable _ hz.1, (physSub_stable ε E).2.2.2.2 z hz.2⟩
  have hW0 : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y0, wK hD hk y ∈ Y0 :=
    fun k hk y hy => ⟨wK_tensFock hD hk (fun x hx => hLK k hk x hx) hy.1, wK_physSub hD hk hy.2⟩
  have hfd0 : FiniteDimensional ℂ Y0 := by
    haveI := tensorFock_finiteDimensional (n := n) hLf
    exact Submodule.finiteDimensional_of_le inf_le_left
  refine ⟨Y0 ⊔ Y0.map Dop, inferInstance, le_sup_left, sup_le inf_le_right ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact dD_physSub E hy.2
  · intro y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    show Dop (y0 + Dop x) ∈ _
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨y0, hy0, rfl⟩) (Submodule.mem_sup_left (hD2 x hx))
  · intro y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _), hDop, gradT_D]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hG0 y0 hy0))
      (Submodule.mem_sup_right ⟨-gradT x, Submodule.neg_mem _ (hG0 x hx), by rw [map_neg]⟩)
  · intro k hk y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _), hDop, wK_D hσ hD hk]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hW0 k hk y0 hy0))
      (Submodule.mem_sup_right ⟨_, hW0 k hk x hx, rfl⟩)

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirValueHighestWeightCoordinates
section
noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem casimirValue_highestWeightCoordinates : CasCoord := by
  intro n ε lam M _ _ E hE z hz hD s
  have hE' := eT_isGlRep (n := n) hE
  have h2 := LinearMap.congr_fun (two_D_sq hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) z
  have hK := casimirK_khwVec_compact ε (diagE_compact hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) hz
  have hs : ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε (eT E) cpT cmT a a z =
      ((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z := by
    simp only [dot, Complex.ofReal_sum, Complex.ofReal_mul, sum_smul, hz.1, smul_smul]
  have h0 : ((2 : ℂ) • ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) * (dOp ε (eT E) cpT + dOp' ε (eT E) cmT))) z = 0 := by
    rw [LinearMap.smul_apply, mul_apply_eq_comp]
    have : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0 := hD
    rw [this, map_zero, smul_zero]
  rw [h0] at h2
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hK, hs] at h2
  have hid := khw_real_identity ε (lam - rhoC ε)
  have hg : lam - rhoC ε + rhoHol ε = gaW ε lam := rfl
  have hl : lam - rhoC ε + rhoC ε = lam := sub_add_cancel _ _
  rw [hg, hl] at hid
  have hc : casimir (eT (n := n) E) z = ((casVal lam : ℝ) : ℂ) • z := by
    have e : casimir (eT (n := n) E) z =
        ((nsq (gaW ε lam + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • z -
          (2 : ℂ) • (((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z) := by
      linear_combination (norm := module) h2
    rw [e, casVal, ← hid]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_smul, smul_smul]
  have hcoord := congrArg (tco s) hc
  rw [TRGap.casimir_eT, tco_map_left] at hcoord
  simpa only [tco, map_smul] using hcoord

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundleOfCompatibleLocalFrames
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FramesBundle

theorem cg_cancel {G : Type} [CommGroup G] (a b c : G) : (a * b) * (a * c)⁻¹ = b * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_cocycle {G : Type} [CommGroup G] (a b c : G) : (b * a⁻¹) * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem cg_gen {G : Type} [CommGroup G] (a g c : G) : a⁻¹ = ((g * c) * a⁻¹ * g⁻¹) * c⁻¹ := by
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

theorem frames_bundle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (n : ℕ) (D : Fin (n + 1) → X.Opens), ⨆ i, D i = ⊤ → ∀ (τ : ∀ (i : Fin (n + 1)) (m : L.ι), Γ(X, D i ⊓ L.U m)ˣ), (∀ i x m m', x ∈ D i ⊓ L.U m → x ∈ D i ⊓ L.U m' → gm (𝟙 X) x _ (τ i m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ i m')) → ∃ g : ∀ i j, Γ(X, D i ⊓ D j)ˣ, (⟨Fin (n + 1), D, g⟩ : LB X).IsLB ∧ LBIso L ⟨Fin (n + 1), D, g⟩ ∧ ∀ i j m, res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) (g i j) = res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) * (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
  intro X L hL n D hD τ hτ
  have hg : ∀ i j, ∃ s : Γ(X, D i ⊓ D j)ˣ, ∀ m,
      res (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) s =
        res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D j ⊓ L.U m) (τ j m) *
          (res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j
    refine glue_unit (D i ⊓ D j) (fun m => D i ⊓ D j ⊓ L.U m) (fun m => inf_le_left) ?_ _ ?_
    · intro x hx
      obtain ⟨m, hm⟩ := exists_chart hL x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, ⟨hx, hm⟩⟩
    · intro m m' x hx
      rw [map_mul, map_mul, map_inv, map_inv, gm_res _ x _ hx.1, gm_res _ x _ hx.1, gm_res _ x _ hx.2,
        gm_res _ x _ hx.2, hτ j x m m' ⟨hx.1.1.2, hx.1.2⟩ ⟨hx.2.1.2, hx.2.2⟩,
        hτ i x m m' ⟨hx.1.1.1, hx.1.2⟩ ⟨hx.2.1.1, hx.2.2⟩, cg_cancel]
  choose g hg' using hg
  have key : ∀ i j m x, x ∈ D i ⊓ D j ⊓ L.U m →
      gm (𝟙 X) x (D i ⊓ D j) (g i j) = gm (𝟙 X) x (D j ⊓ L.U m) (τ j m) * (gm (𝟙 X) x (D i ⊓ L.U m) (τ i m))⁻¹ := by
    intro i j m x hx
    rw [← gm_res _ x (inf_le_left : D i ⊓ D j ⊓ L.U m ≤ D i ⊓ D j) hx, hg' i j m, map_mul, map_inv,
      gm_res _ x _ hx, gm_res _ x _ hx]
  refine ⟨g, ⟨hD, ?_, ?_⟩, ⟨⟨fun p => (τ p.1 p.2)⁻¹⟩, ?_⟩, hg'⟩
  · intro i
    apply unit_ext
    intro x hx
    rw [gm_res _ x _ hx, map_one]
    obtain ⟨m, hm⟩ := exists_chart hL x
    exact (key i i m x ⟨⟨hx, hx⟩, hm⟩).trans (mul_inv_cancel _)
  · intro i j k
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    obtain ⟨m, hm⟩ := exists_chart hL x
    have h1 := key i j m x ⟨⟨hx.1.1, hx.1.2⟩, hm⟩
    have h2 := key j k m x ⟨⟨hx.1.2, hx.2⟩, hm⟩
    have h3 := key i k m x ⟨⟨hx.1.1, hx.2⟩, hm⟩
    exact (congrArg₂ (· * ·) h1 h2).trans ((cg_cocycle _ _ _).trans h3.symm)
  · rintro ⟨i, m⟩ ⟨j, m'⟩
    apply unit_ext
    intro x hx
    have hx' : x ∈ D i ⊓ L.U m ⊓ (D j ⊓ L.U m') := hx
    have eL : ∀ h : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ L.U m,
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h (τ i m)⁻¹) = (gm (𝟙 X) x _ (τ i m))⁻¹ := by
      intro h
      rw [map_inv, map_inv, gm_res _ x _ hx']
    have eR : ∀ (h1 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D i ⊓ D j) (h2 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ L.U m ⊓ L.U m')
        (h3 : D i ⊓ L.U m ⊓ (D j ⊓ L.U m') ≤ D j ⊓ L.U m'),
        gm (𝟙 X) x (D i ⊓ L.U m ⊓ (D j ⊓ L.U m')) (res h1 (g i j) * (res h2 (L.g m m'))⁻¹ * res h3 (τ j m')⁻¹) =
          gm (𝟙 X) x _ (g i j) * (gm (𝟙 X) x _ (L.g m m'))⁻¹ * (gm (𝟙 X) x _ (τ j m'))⁻¹ := by
      intro h1 h2 h3
      rw [map_mul, map_mul, map_inv, map_inv, map_inv, gm_res _ x _ hx', gm_res _ x _ hx', gm_res _ x _ hx']
    have h1 := key i j m x ⟨⟨hx'.1.1, hx'.2.1⟩, hx'.1.2⟩
    have h2 := hτ j x m m' ⟨hx'.2.1, hx'.1.2⟩ ⟨hx'.2.1, hx'.2.2⟩
    refine (eL _).trans (Eq.trans ?_ (eR _ _ _).symm)
    rw [h1, h2]
    exact cg_gen _ _ _

end GlobalTheory.FramesBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellMulSimpleUIntegral
section
open GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.GKFactor.UnitaryInt

open GlobalTheory.GKFactor

variable {L : Type} [Field L] {n : ℕ}

theorem mem_GLint_iff_entries (O : Subring L) (g : GL (Fin n) L) :
    g ∈ GLint (Fin n) O ↔ (∀ i j, g.val i j ∈ O) ∧ ∀ i j, (g⁻¹).val i j ∈ O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.mul_inv
    · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact g.inv_mul

section Comb

variable {n : ℕ}

end Comb

section Hyps

variable {n : ℕ}

end Hyps

end GlobalTheory.GKFactor.UnitaryInt
end

