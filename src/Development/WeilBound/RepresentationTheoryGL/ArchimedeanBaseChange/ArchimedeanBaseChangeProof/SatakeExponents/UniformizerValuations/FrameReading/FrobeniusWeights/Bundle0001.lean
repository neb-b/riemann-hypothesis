module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.SaturationTransportPair
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.HcHecke
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PCtSat
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinusculeSetEqDoubleCoset
public import GroundTheory.AutomorphicForms.Bundle0024

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PConjFix
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FG

open JetMatrixAlgebra GlobalTheory.ThetaSatake in
theorem conjFix_holds : ConjFix := by
  intro E _ _ _ a b
  refine ⟨fun w u G _ hwu hG => ?_, fun S hS => ⟨fun u hu => ?_, fun X => ?_⟩⟩
  · obtain ⟨x, rfl⟩ : ∃ x, cw x = w := ⟨cw w, GlobalTheory.ThetaPull.conjSrc_conjSrc w⟩
    obtain rfl : u = x := (GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hwu).trans (GlobalTheory.ThetaPull.conjSrc_conjSrc x)
    rw [pairRtT_cw] at hG
    refine (mem_fixed_comp_symm _ (fun g => ?_)).1 hG
    show g ∈ (KGL u (n := a)).prod (KGL u (n := b)) ↔ ((fx u a).prodCongr (fx u b)) g ∈ (KGL (cw u) (n := a)).prod (KGL (cw u) (n := b))
    rw [Subgroup.mem_prod, Subgroup.mem_prod]
    exact and_congr (mem_fx_iff u a g.1) (mem_fx_iff u b g.2)
  · obtain ⟨w, ⟨hwS, hwu⟩, -⟩ := hS u
    by_cases h : w = u
    · exact Or.inl (h ▸ hwS)
    · exact Or.inr ⟨w, hwS, ⟨u, Ne.symm h, hwu.symm⟩, hwu.symm, Or.inl (Ne.symm h)⟩
  · refine (X.finite_toSet.image cw).subset fun u hu => ?_
    obtain ⟨w, hw, hwu⟩ := hu
    exact ⟨w, hw, (GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hwu).symm⟩

end PositivityTheory.Rg.BcB.F.FG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PCtHecke
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FG

theorem ctHecke_holds : CtHecke := by
  intro E _ _ _ n a b h w ν ϖ k hw hϖ hν
  have h0 : ϖ ≠ 0 := b_unif_ne_zero hϖ
  have hord : ordL ((Units.mk0 ϖ h0 : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [Units.val_mk0]; exact ordL_unif hϖ
  have hH := PositivityTheory.Rg.BcB.F.Fok.ctT_hecke E n a b h w ν (Units.mk0 ϖ h0) hw hord hν k
  rw [Units.val_mk0] at hH
  refine ⟨hH.1, fun y hy g => (hH.2 y hy g).2, ?_⟩
  have hm : ν (-1) = 1 := by
    apply hν
    have := ord_neg_one' (w := w)
    rwa [GlobalTheory.BCT.InertChar.ord_eq_ordL] at this
  rw [map_pow, hm, one_pow]

end PositivityTheory.Rg.BcB.F.FG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PGoodLOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem v_one_of_ordL {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} (u : (w.adicCompletion E)ˣ)
    (h : ordL (u : w.adicCompletion E) = 0) : Valued.v (u : w.adicCompletion E) = 1 := by
  have h0 : Valued.v (u : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 u.ne_zero
  unfold ordL at h
  rw [dite_eq_right h0, neg_eq_zero] at h
  have h1 : WithZero.unzero h0 = 1 := by simpa using congrArg Multiplicative.ofAdd h
  rw [← WithZero.coe_unzero h0, h1]
  rfl

theorem goodLOf_holds : GoodLOf := by
  intro hRS hFm hAct hLoc hCF hUS hCt E _ _ _ hE n a ha π hπ μ e hμ Sec hSec d hd hPS hdμ hϖ hunr σ hσ l₁ l₂ μ₁ μ₂ μa μb A s₁ s₂ Pa Pb D hC hL1 hL2
    I G hG0 hGs hGl hact
  obtain ⟨j, hj⟩ : ∃ j, G j ≠ 0 := by
    by_contra h
    push Not at h
    exact hG0 (funext h)
  have hab : a + (n - a) = n := Nat.add_sub_of_le ha
  have core : ∀ w ∈ Sec, IsSplitAt w → w ∉ d.T → w ∉ d.S₀ → w ∉ d.Bad →
      D.SplitAt π w ∧ ∀ u, ConjPl w u → D.SplitAt π u := by
    intro w hwS hw hT hS0 hBad
    have hun : μ.UnrAt w := hunr w hwS hS0 hBad
    have hgood : d.Good w := ⟨hw, hT, hS0, hBad, fun u hu => by rw [hdμ w]; exact hun u (v_one_of_ordL u hu)⟩
    have hlev : d.lev a w = K2 a (n - a) w := by simp [LocData.lev, hT, hS0, hBad]
    have hlev2 : d.lev₂ a w = K2 a (n - a) w := by simp [LocData.lev₂, hS0, hBad]
    have hKU : d.KU w = KL n w := by simp [LocData.KU, hT, hS0, hBad]
    obtain ⟨hfix1, hfix2⟩ := (hGl j).2 w hwS
    rw [hlev] at hfix1
    have hfix2' := hfix2 hw
    rw [hlev2] at hfix2'
    have hCtk := fun k => hCt E n a (n - a) hab w (d.μ w) (d.ϖ w) k hw (hϖ w) hgood.2.2.2.2
    have hsgn : d.sgn a w = 1 := by
      simp only [LocData.sgn]
      rw [(hCtk 0).2.2]
      simp
    have hhc : ∀ k, d.hc a ha w k = ctT hab w (d.μ w) (d.ϖ w) k := by
      intro k
      simp [LocData.hc, hsgn]
    have hOk : ∀ k intersection_update_fsHerm_neg_one, (d.hL a ha w k intersection_update_fsHerm_neg_one).Ok d.P := fun k intersection_update_fsHerm_neg_one =>
      (hLoc E n d hd a ha).2.2.2 _ (Or.inr ⟨w, k, intersection_update_fsHerm_neg_one, hgood, rfl⟩)
    have hDI : ∀ k intersection_update_fsHerm_neg_one, DiagIdem d.P (d.lev a) (d.hL a ha w k intersection_update_fsHerm_neg_one) := by
      intro k intersection_update_fsHerm_neg_one w' _ x y
      simp only [LocData.hL, LocData.eL, LocData.diag]
      split_ifs <;> rfl
    have hwP : w ∉ d.P := by simp [LocData.P, hT, hS0]
    have hP : ∀ k, actP w (ctT hab w (d.μ w) (d.ϖ w) k) (G j) =
        twTr (σ w).ρ (KL n w) (KL n w) (d.hU w k) LinearMap.id • G j := by
      intro k
      have h1 := (hFm E d.kap Sec d.P (A.blk _) (Equiv.refl _) hSec hPS (d.lev a) (d.lev₂ a) (d.hL a ha w k false) I G w
        hL1 hL2 (hOk k false) (hDI k false) hGl hwS).1 hwP
        (fun w' hw' => by simp only [LocData.hL, LocData.eL, Bool.false_eq_true, ite_false]; rw [Function.update_of_ne hw']; rfl)
        (fun w' => by simp only [LocData.hL, LocData.eL, Bool.false_eq_true, ite_false]; rfl) j
      have h2 := congrFun (hact w hwS hgood k false) j
      have h3 : (d.hL a ha w k false).s w = ctT hab w (d.μ w) (d.ϖ w) k := by
        simp [LocData.hL, hhc]
      rw [h3] at h1
      rw [← h1]
      exact h2
    have hT' : ∀ k, actT w (ctT hab w (d.μ w) (d.ϖ w) k) (G j) =
        twTr (σ w).ρ (KL n w) (KL n w) (d.hU w k) LinearMap.id • G j := by
      intro k
      have h1 := (hFm E d.kap Sec d.P (A.blk _) (Equiv.refl _) hSec hPS (d.lev a) (d.lev₂ a) (d.hL a ha w k true) I G w
        hL1 hL2 (hOk k true) (hDI k true) hGl hwS).2 hw
        (fun w' => by simp only [LocData.hL, LocData.eL, ite_true]; rfl)
        (fun w' hw' => by simp only [LocData.hL, LocData.eL, ite_true]; rw [Function.update_of_ne hw']; rfl) j
      have h2 := congrFun (hact w hwS hgood k true) j
      have h3 : (d.hL a ha w k true).t w = ctT hab w (d.μ w) (d.ϖ w) k := by
        simp [LocData.hL, hhc]
      rw [h3] at h1
      rw [← h1]
      exact h2
    obtain ⟨B, hB, hBe⟩ := hUS E n π w (σ w) hw (hσ w hwS).1 (by rw [← hKU]; exact (hσ w hwS).2)
    have hev : ∀ k ≤ n, twTr (σ w).ρ (KL n w) (KL n w) (d.hU w k) LinearMap.id = satEig (qV E w) n B k :=
      fun k hk => hBe _ (hϖ w) k hk
    have hR := hRS E hE n a (n - a) hab μ e π s₁ s₂ Pa Pb D (G j) w B (d.ϖ w) hμ hπ hC.g₁ hC.g₂ hC.u₁ hC.u₂ hC.t₁ hC.t₂
      hC.join (hGs j) hj hw hun hB (hϖ w)
    refine ⟨(hR.1 hfix1 fun k hk => ?_).2, fun u hu => (hR.2 u hu ((hCF E a (n - a)).1 w u (G j) hw hu hfix2') fun k hk => ?_).2⟩
    · rw [← hdμ w, ← (hAct E a (n - a) w _ (G j) (hCtk k).1 (hCtk k).2.1).1 hfix1, hP k, hev k hk]
    · rw [← hdμ w, ← (hAct E a (n - a) w _ (G j) (hCtk k).1 (hCtk k).2.1).2 hfix2', hT' k, hev k hk]
  have hfin := ((hCF E a (n - a)).2 Sec hSec).2 (d.T ∪ d.S₀ ∪ d.Bad)
  rw [Filter.eventually_cofinite]
  refine ((d.T ∪ d.S₀ ∪ d.Bad).finite_toSet.union hfin).subset ?_
  intro u hu
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hu
  obtain ⟨hsu, hnot⟩ := hu
  by_contra hcon
  simp only [Set.mem_union, Finset.mem_coe, Finset.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and] at hcon
  obtain ⟨⟨⟨hT, hS0⟩, hBad⟩, hCX⟩ := hcon
  rcases ((hCF E a (n - a)).2 Sec hSec).1 u hsu with huS | ⟨w, hwS, hw, hwu⟩
  · exact hnot (core u huS hsu hT hS0 hBad).1
  · have hwX : w ∉ d.T ∪ d.S₀ ∪ d.Bad := fun h => hCX w (Finset.mem_union.1 h |>.imp_left Finset.mem_union.1) hwu
    simp only [Finset.mem_union, not_or] at hwX
    exact hnot ((core w hwS hw hwX.1.1 hwX.1.2 hwX.2).2 u hwu)

end PositivityTheory.Rg.BcB.F.FG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PUSatOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcs_of_finDoset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {K : Subgroup G} (hK : IsCompact (K : Set G)) {f : G → ℂ} (hf : FinDosetSupp K f) : HasCompactSupport f := by
  obtain ⟨S, hS⟩ := hf
  refine HasCompactSupport.intro (K := ⋃ s ∈ S, (fun p : G × G => p.1 * s * p.2) '' ((K : Set G) ×ˢ (K : Set G)))
    (S.isCompact_biUnion fun s _ => (hK.prod hK).image (by fun_prop)) fun g hg => ?_
  by_contra h0
  obtain ⟨s, hs, a, b, rfl⟩ := hS g h0
  exact hg (Set.mem_biUnion hs ⟨((a : G), (b : G)), ⟨a.2, b.2⟩, rfl⟩)

theorem uSatOf_holds : USatOf := by
  intro hSD E _ _ _ n π w σ hw hcomp hfix
  obtain ⟨P, T, hT, hP, hlev⟩ := hSD E n w hw σ
  have hUL : UL n w = ⊤ := if_pos hw
  have hmemUL : ∀ g : GLw n w, g ∈ UL n w := fun g => hUL ▸ Subgroup.mem_top g
  have hKmap : (KL n w).map (UL n w).subtype = KGL w (n := n) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hx
    · intro hg
      exact ⟨⟨g, hmemUL g⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
  have hoc := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  have hKLopen : IsOpen (KL n w : Set (UL n w)) := by
    have : (KL n w : Set (UL n w)) = Subtype.val ⁻¹' (KGL w (n := n) : Set (GLw n w)) := by
      ext x
      exact Subgroup.mem_subgroupOf
    rw [this]
    exact hoc.1.preimage continuous_subtype_val
  have hLev : IsLevel (MonoidHom.id _) (KL n w) (KL n w) := ⟨hKLopen, le_rfl, fun k hk => hk⟩
  have hHk : ∀ ϖ : w.adicCompletion E, IsUnifV E w ϖ → ∀ k : ℕ,
      PositivityTheory.Rg.BcN.F2.IsHk ((KL n w).map (UL n w).subtype) (Tj ℂ n (Ov E w) ϖ k) := by
    intro ϖ hϖ k
    have hT' := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ k
    rw [hKmap]
    exact ⟨hoc.1, hoc.2, hcs_of_finDoset hoc.2 hT'.2, fun k₁ hk₁ k₂ hk₂ g => hT'.1 ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ g⟩
  obtain ⟨ϖ₀, hϖ₀⟩ := GlobalTheory.LFun.exists_isUnifV w

  have hTfix : ∀ y ∈ fixed σ.ρ (KL n w), T y ∈ fixed P.ρ (KGL w (n := n)) := fun y hy => by
    have := ((hlev (KL n w) hLev _ (hHk ϖ₀ hϖ₀ 0)).2 y hy).1
    rwa [hKmap] at this
  obtain ⟨y₀, hy₀, hy₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  have hsph : GlobalTheory.LGrp.IsSpherical P.ρ (KGL w (n := n)) := by
    intro h
    have h1 := hTfix y₀ hy₀
    rw [h, Submodule.mem_bot] at h1
    exact hy₀0 (T.injective (h1.trans T.map_zero.symm))
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible P.smooth P.irred hsph
  refine ⟨B, ⟨P, hP π hcomp, hB⟩, ?_⟩
  intro ϖ hϖ k hk

  have hff : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V) (H : Subgroup (GLw n w)),
      fixed ρ H = GroundTheory.Automorphic.fixedVectors ρ H := fun ρ H => by
    ext v
    simp [fixed, eig, GroundTheory.Automorphic.fixedVectors]
  have e1 := GlobalTheory.CompanionTheory.SatakeTyping.integralGL_eq_KGL w n
  have hP1 : Module.finrank ℂ (fixed P.ρ (KGL w (n := n))) = 1 := by
    have := P.irred
    have hne : GroundTheory.Automorphic.fixedVectors P.ρ (GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥ := by
      rw [e1, ← hff]
      exact hsph
    have h := GroundTheory.Automorphic.Spherical.finrank_fixedVectors_eq_one (fun v => P.smooth v) hne
    rwa [e1, ← hff] at h
  have : FiniteDimensional ℂ (fixed P.ρ (KGL w (n := n))) := Module.finite_of_finrank_pos (by omega)

  let Tf : fixed σ.ρ (KL n w) →ₗ[ℂ] fixed P.ρ (KGL w (n := n)) :=
    { toFun := fun y => ⟨T y, hTfix y.1 y.2⟩
      map_add' := fun a b => Subtype.ext (T.map_add a b)
      map_smul' := fun c a => Subtype.ext (T.map_smul c a) }
  have hTf : Function.Injective Tf := fun a b h => Subtype.ext (T.injective (congrArg Subtype.val h))
  have : FiniteDimensional ℂ (fixed σ.ρ (KL n w)) := Module.Finite.of_injective Tf hTf
  have hσ1 : Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1 := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hTf
    have h2 : 0 < Module.finrank ℂ (fixed σ.ρ (KL n w)) := Module.finrank_pos_iff.2
      ⟨⟨⟨y₀, hy₀⟩, 0, fun h => hy₀0 (congrArg Subtype.val h)⟩⟩
    omega

  set c := satEig (qV E w) n B k
  have heig : ∀ y ∈ fixed σ.ρ (KL n w),
      levOp σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id y = c • y := by
    intro y hy
    obtain ⟨-, hall⟩ := hlev (KL n w) hLev _ (hHk ϖ hϖ k)
    obtain ⟨-, h2⟩ := hall y hy
    simp only [Subgroup.relIndex_self, Nat.cast_one, one_mul] at h2
    apply T.injective
    rw [h2, T.map_smul]
    by_cases hy0 : y = 0
    · subst hy0
      simp only [T.map_zero, smul_zero]
      simp [PositivityTheory.Rg.BcN.F2.hk]
    · have hs := hB.2 (T y) (hTfix y hy) (fun h => hy0 (T.injective (h.trans T.map_zero.symm)))
      have := hs.2.2.2 ϖ hϖ k hk
      rw [← hKmap] at this
      exact this
  have hcond : ∀ v ∈ fixed σ.ρ (KL n w),
      levOp σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id v ∈ fixed σ.ρ (KL n w) :=
    fun v hv => by rw [heig v hv]; exact Submodule.smul_mem _ _ hv
  rw [twTr, dite_eq_left hcond]
  have hres : (levOp σ.ρ (KL n w) (KL n w) (fun u => Tj ℂ n (Ov E w) ϖ k u.1) LinearMap.id).restrict hcond =
      c • (1 : Module.End ℂ (fixed σ.ρ (KL n w))) := by
    ext v
    simp only [LinearMap.coe_restrict_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul]
    exact heig v.1 v.2
  rw [hres, map_smul, LinearMap.trace_one, hσ1]
  simp

end PositivityTheory.Rg.BcB.F.FG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FrobeniusWeights.PWeightLOf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

theorem mOf_infOf_embedding {E : Type} [Field E] [NumberField E] {n : ℕ} (l : InfinitePlace E → DomWeight n)
    (v : InfinitePlace E) :
    mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) v.embedding = infOfWeight (l v) := by
  unfold mOf infOfWeight PositivityTheory.RgBcC.infOf
  simp only [InfinitePlace.mk_embedding, decide_true, if_true, one_mul]
  congr 1
  funext k
  rw [add_sub_assoc]

theorem space_ne_bot_of_pair {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
    {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} (h : ∃ G ∈ pairSpace U₁ U₂, G ≠ 0) :
    U₁ ≠ ⊥ ∧ U₂ ≠ ⊥ := by
  obtain ⟨G, hG, hG0⟩ := h
  constructor
  · rintro rfl
    apply hG0
    have : pairSpace (⊥ : Submodule ℂ (Sm E a)) U₂ = ⊥ := by
      unfold pairSpace
      rw [Submodule.span_eq_bot]
      rintro F ⟨φ₁, hφ₁, φ₂, -, rfl⟩
      rw [Submodule.mem_bot] at hφ₁
      subst hφ₁
      funext x
      simp
    rw [this, Submodule.mem_bot] at hG
    exact hG
  · rintro rfl
    apply hG0
    have : pairSpace U₁ (⊥ : Submodule ℂ (Sm E b)) = ⊥ := by
      unfold pairSpace
      rw [Submodule.span_eq_bot]
      rintro F ⟨φ₁, -, φ₂, hφ₂, rfl⟩
      rw [Submodule.mem_bot] at hφ₂
      subst hφ₂
      funext x
      simp
    rw [this, Submodule.mem_bot] at hG
    exact hG

theorem weightLOf_holds : WeightLOf := by
  intro hIT hReg hJI hTI hWJ E _ _ _ hU n hn π hπ μ e hμ lam hw a b l₁ l₂ hsum s₁ s₂ Pa Pb D hC h₁ h₂ hex τ lam' hτ
  obtain ⟨hne₁, hne₂⟩ := space_ne_bot_of_pair hex
  rw [hJI E n a b (μ ^ b) (μ ^ a) Pa Pb D hC.join τ,
    hTI hIT E a s₁ Pa τ _ hC.g₁ hC.u₁ hC.t₁ hne₁ (h₁ τ),
    hTI hIT E b s₂ Pb τ _ hC.g₂ hC.u₂ hC.t₂ hne₂ (h₂ τ)]
  refine hWJ E hU n a b μ e π lam (mOf fun v => PositivityTheory.RgBcC.infOf (l₁ v).w)
    (mOf fun v => PositivityTheory.RgBcC.infOf (l₂ v).w) hn hμ hπ hw (hReg E a l₁).1 (hReg E b l₂).1 ?_ τ lam' hτ
  intro v
  rw [mOf_infOf_embedding, mOf_infOf_embedding]
  exact hsum v

end PositivityTheory.Rg.BcB.F.FG

end
end

