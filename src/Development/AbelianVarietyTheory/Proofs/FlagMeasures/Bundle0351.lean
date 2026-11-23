module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KHighestEqSmulOfMinusKilled
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ChainBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.SharpRestriction.CuspSpanNormBounds.RowsOneGenusOfLocalDiscriminant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.MultGap

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem proj_comm (hU : IsURepOn (Kset ε) σ) {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : IsKStableOn ε σ W) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : H) :
    W.starProjection (σ k x) = σ k (W.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW k hk _ (W.starProjection_apply_mem x))
    fun w hw => ?_
  rw [← map_sub, FormF.inner_rep_K hU hk]
  exact W.starProjection_inner_eq_zero x _ (hW _ (Kset_star ε hk) w hw)

theorem orth_of_ne (hU : IsURepOn (Kset ε) σ) {Λ μ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) (hT : IsKTypeOf ε σ μ T) (hne : μ ≠ Λ) :
    ∀ x ∈ S, ∀ y ∈ T, ⟪x, y⟫_ℂ = 0 := by
  haveI := hT.1
  let Q : S →L[ℂ] H := T.starProjection.comp S.subtypeL
  by_cases hQ : Q = 0
  · intro x hx y hy
    have h1 : T.starProjection x = 0 := congrArg (fun A : S →L[ℂ] H => A ⟨x, hx⟩) hQ
    have h2 := T.starProjection_inner_eq_zero x y hy
    rwa [h1, sub_zero] at h2
  exfalso
  have hR := FormF.rangeType n ε Λ H σ S H σ Q hS (fun k hk x y hxy => by
    change T.starProjection (y : H) = σ k (T.starProjection (x : H))
    rw [hxy, proj_comm hU hT.2.1 hk]) hQ
  have hle : LinearMap.range (Q : S →ₗ[ℂ] H) ≤ T := by
    rintro _ ⟨x, rfl⟩
    exact T.starProjection_apply_mem _
  obtain ⟨v, hv, hv0, hvw⟩ := hR.2.2.2.1
  rcases hT.2.2.1 _ hle hR.2.1 with h | h
  · rw [h] at hv
    exact hv0 hv
  · obtain ⟨w, hw, hw0, hww⟩ := hT.2.2.2.1
    refine hne (GlobalTheory.LowHW.cdom_antisymm (ε := ε) (hR.2.2.2.2 μ w (h ▸ hw) hw0 hww)
      (hT.2.2.2.2 Λ v (hle hv) hv0 hvw))

theorem exists_orth (hU : IsURepOn (Kset ε) σ) {Λ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) (hT : IsKTypeOf ε σ Λ T) (hne : S ≠ T) :
    ∃ R : Submodule ℂ H, IsKTypeOf ε σ Λ R ∧ ∀ x ∈ R, ∀ y ∈ T, ⟪x, y⟫_ℂ = 0 := by
  haveI := hT.1
  let Q : S →L[ℂ] H := S.subtypeL - T.starProjection.comp S.subtypeL
  have hQa : ∀ x : S, Q x = (x : H) - T.starProjection (x : H) := fun x => rfl
  have hQ : Q ≠ 0 := by
    intro hQ
    have hle : S ≤ T := by
      intro x hx
      have h1 := hQa ⟨x, hx⟩
      rw [hQ] at h1
      have h2 : x = T.starProjection x := sub_eq_zero.1 h1.symm
      rw [h2]
      exact T.starProjection_apply_mem _
    rcases hT.2.2.1 _ hle hS.2.1 with h | h
    · obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
      rw [h] at hv
      exact hv0 hv
    · exact hne h
  refine ⟨_, FormF.rangeType n ε Λ H σ S H σ Q hS (fun k hk x y hxy => by
    rw [hQa, hQa, hxy, proj_comm hU hT.2.1 hk, map_sub]) hQ, ?_⟩
  rintro _ ⟨x, rfl⟩ y hy
  exact T.starProjection_inner_eq_zero x y hy

theorem exists_gap {lam : Fin n → ℝ} (hl : StrictAnti lam)
    (h : ∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) :
    ∃ g : ℝ, (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) ∧ 2 * (n : ℝ) < g := by
  have key : ∀ᶠ g in nhdsWithin (2 * (n : ℝ)) (Set.Ioi (2 * (n : ℝ))),
      ∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b := by
    simp only [Filter.eventually_all]
    intro a b hab he
    have h1 := h a b he
    rw [abs_of_pos (sub_pos.2 (hl hab))] at h1
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds ((eventually_lt_nhds h1).mono fun g hg => hg.le)
  exact (key.and self_mem_nhdsWithin).exists

theorem kSpan_smul_le {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (c : ℂ)
    (u : V) : kSpan ε E (c • u) ≤ kSpan ε E u :=
  sInf_le_sInf fun S hS => ⟨S.smul_mem c hS.1, hS.2⟩

theorem cas_mem_cyc {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (u : V) : Cas E u ∈ cyc E u := by
  rw [cyc, Submodule.mem_sInf]
  intro W hW
  simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply]
  exact W.sum_mem fun a _ => W.sum_mem fun b _ => hW.2 _ _ _ (hW.2 _ _ _ hW.1)

theorem cas_kHighest {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u) : KHighest ε E μ (Cas E u) := by
  have hc : ∀ a b, E a b (Cas E u) = Cas E (E a b u) := fun a b =>
    (congrArg (fun A : Module.End ℂ V => A u) ((casCentral _ n ε E hE).1 a b)).symm
  exact ⟨fun a => by rw [hc, hu.1 a, map_smul], fun a b h1 h2 => by rw [hc, hu.2 a b h1 h2, map_zero]⟩

theorem cas_real {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) (hU : IsUnitary ε E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u) (hu0 : u ≠ 0) {c : ℂ}
    (hc : Cas E u = c • u) : ∃ r : ℝ, Cas E u = (r : ℂ) • u := by
  have h := wdCas V n ε E μ u hE hU hu
  rw [hc, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  generalize ((nsq (μ + rhoC ε) - nsq (rhoC ε)) * ‖u‖ ^ 2 -
      ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) : ℝ) = t at h
  refine ⟨t / ‖u‖ ^ 2, ?_⟩
  have hn : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by simpa using hu0
  rw [hc]
  congr 1
  push_cast
  rw [← h, eq_div_iff (pow_ne_zero 2 hn)]
  rfl

theorem isKTypeOf_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → (∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) := by
  intro n ε lam H _ _ σ hl hDS hgap
  obtain ⟨hc, -, hU, hirr, -, ⟨S0, hS0⟩, -⟩ := id hDS
  have hK := FormF.URep_K hU
  obtain ⟨V, E, S, hD, hS, hSV⟩ := GlobalTheory.SmoothKType.exists_isDer_kType n ε _ H σ S0 hU hS0
  obtain ⟨hk1, hk2⟩ := GlobalTheory.Jet.KType.kType_iff n ε H σ V E hU hD
  obtain ⟨v, hv, hv0, hvw⟩ := hS.2.2.2.1
  obtain ⟨u, rfl⟩ : ∃ u : V, (u : H) = v := ⟨⟨v, hSV hv⟩, rfl⟩
  have hu0 : u ≠ 0 := fun h => hv0 (by rw [h]; rfl)
  obtain ⟨huH, huS, hufd⟩ := hk2 _ S u hS hSV hv hu0 hvw
  obtain ⟨g, hg1, hg2⟩ := exists_gap hl.1 hgap
  have hm : ∀ x ∈ cyc E u, KHighest ε E (lowK ε lam) x → ∃ c : ℂ, x = c • u :=
    GlobalTheory.Jet.kHighest_eq_smul_of_minus_killed V n ε E lam g u hD.1 hD.2.1 huH hufd hg1 hg2
      (GlobalTheory.Jet.Schmid.mul_vminus_eq_zero n ε H σ V E lam u hl hDS hD huH hufd)
  obtain ⟨c, hcu⟩ := hm _ (cas_mem_cyc E u) (cas_kHighest hD.1 huH)
  obtain ⟨r, hr⟩ := cas_real hD.1 hD.2.1 huH hu0 hcu
  have hdense := GlobalTheory.CycDense.cyc_dense n ε H σ V E _ r u hU hD hirr hu0 huH hufd hr
  obtain ⟨-, -, hst, -, hpc, hcp, hfd⟩ := pfilFacts V n ε E u hD.1
  have huniq : ∀ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T → T = S := by
    intro T hT
    by_contra hne
    obtain ⟨R, hR, hRS⟩ := exists_orth hK hT hS hne
    obtain ⟨w, hw, hw0, -⟩ := hR.2.2.2.1
    refine hw0 (hdense.eq_zero_of_inner_left ℂ fun y hy => ?_)
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨j, hj⟩ := hcp z hz
    haveI := hfd hufd j
    obtain ⟨m, x, μ, hx, -, hsup⟩ := kDecomp V n ε E _ (hfd hufd j) (glRel_kRel ε E hD.1)
      (isUnitary_kUnit ε E hD.2.1) (hst j)
    have hle : pfil ε E u j ≤ LinearMap.ker ((innerSL ℂ w : H →L[ℂ] ℂ).toLinearMap ∘ₗ V.subtype) := by
      rw [← hsup]
      refine iSup_le fun i y hy => ?_
      change ⟪w, (y : H)⟫_ℂ = 0
      by_cases hμ : μ i = lowK ε lam
      · obtain ⟨d, hd⟩ := hm (x i) (hpc j (hx i).1) (hμ ▸ (hx i).2.2)
        rw [hd] at hy
        exact hRS w hw _ (huS ▸ ⟨y, kSpan_smul_le E d u hy, rfl⟩)
      · have hfi : FiniteDimensional ℂ (kSpan ε E (x i)) :=
          Submodule.finiteDimensional_of_le (S₂ := pfil ε E u j) (sInf_le ⟨(hx i).1, hst j⟩)
        exact orth_of_ne hK hR (hk1 _ _ (hx i).2.1 (hx i).2.2 hfi) hμ w hw _ ⟨y, hy, rfl⟩
    exact hle hj
  have : lowKSub ε lam σ = S := le_antisymm (sSup_le fun T hT => (huniq T hT).le) (le_sSup hS)
  rw [this]
  exact hS

end GlobalTheory.Jet.MultGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOnePairsBoundOfSplitFiniteRealRo
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowNG_of_cut2P (hc : NGCut2P) : RowNGP := by
  have hR : PN.RowNGJoint := Formalism.FourierDecayAlt.Final.pn_rowNGJoint
  have hC : PN.NGChain := Formalism.FourierDecayAlt.P.norm_chain
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, A, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨Cn, hCn, hK⟩ := Formalism.L2.SG.RowsOther.rowNG_of_cut hR hC C1 C0n A CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u u' hTi h0 hs hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hFin, hRe⟩ :=
    h C' Cl a b D large₂ X Y u u' hTi h0 hs hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u') _ _ _ _ (Y.tO u u') D.R.rS D.R.k (Set (TauC Y u u')) (NuC D)
    (NOf2 Y u u' νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ))
    cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hFin hRe
  rw [hdd] at r
  exact r

end GlobalTheory.NGRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticePropertiesTransportByIsometry
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatTransport

variable {D : D7}

theorem mem_gmap_inv (g : GV D) (Λ : LV D) (x : (VS D).V) : x ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ↔ g x ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g x, h, by simp⟩

variable {T : D.host.E} {F0 G' : FlagG (VS D) D.R.rS T} {g : GV D}

theorem e_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (a : Fin D.R.rS) : g (F0.e a) = G'.e a := by
  have h := hfr a.castSucc
  simpa [FlagG.fvec, Fin.snoc_castSucc] using h

theorem z_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) : g F0.z = G'.z := by
  have h := hfr (Fin.last _)
  simpa [FlagG.fvec, Fin.snoc_last] using h

theorem map_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) :
    F0.X.map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = G'.X := by
  unfold FlagG.X
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext a
  exact e_eq hfr a

theorem mem_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ F0.X ↔ g v ∈ G'.X := by
  rw [← map_X hfr]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

theorem mem_orth (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) :
    v ∈ orth (VS D) F0.X ↔ g v ∈ orth (VS D) G'.X := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ F0.X := by
      rw [mem_X hfr]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h x hx
    rw [← hiso]
    exact h _ ((mem_X hfr x).1 hx)

theorem mem_XS (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ XS D F0 ↔ g v ∈ XS D G' := by
  have hmap : (XS D F0).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) = XS D G' := by
    unfold XS
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
      refine ⟨a, x, hx, ?_⟩
      simp [e_eq hfr a]
    · rintro ⟨a, x, hx, rfl⟩
      refine ⟨x • F0.e a, ⟨a, x, hx, rfl⟩, ?_⟩
      simp [e_eq hfr a]
  rw [← hmap]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

theorem mem_dual (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (Λ : LV D) (x : (VS D).V) :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ↔ g x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ := by
      rw [mem_gmap_inv]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h y hy
    rw [← hiso]
    exact h _ ((mem_gmap_inv g Λ y).1 hy)

theorem isLattice_inv (g : GV D) {Λ : LV D} (hL : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  exact Submodule.IsLattice.of_fg D.host.E (hL.fg.map _)

theorem mem_Lsub (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (Λ : LV D)
    (v : (VS D).V) (hv : v ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0)) : g v ∈ Lsub Λ (lf D G') := by
  obtain ⟨hs, ho⟩ := hv
  refine ⟨?_, (mem_orth hg hfr v).1 ho⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hs
  obtain ⟨hyΛ, hyo⟩ := hy
  rw [map_add (f := _)]
  refine Submodule.add_mem_sup ⟨(mem_gmap_inv g Λ y).1 hyΛ, (mem_orth hg hfr y).1 hyo⟩ ?_
  exact (mem_X hfr w).1 hw

end GlobalTheory.RowLatTransport

namespace GlobalTheory.RowLatTransport

theorem rowLat_transport : ∀ (D : D7) (T : D.host.E) (F0 G' : FlagG (VS D) D.R.rS T) (g : GV D), g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, g (F0.fvec a) = G'.fvec a) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → G'.z ∈ Λ → XLam Λ (lf D G') = XS D G' → (∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 ∧ Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ F0.z ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∧ XLam (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) = XS D F0 ∧ (∀ c : D.host.E, c • F0.z ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) := by
  intro D T F0 G' g hg hfr Λ hL hU hz hX hprim
  have hL' := isLattice_inv g hL
  have hU' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular
    ext x
    rw [mem_dual hg, mem_gmap_inv]
    have hU0 : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
    rw [hU0]
  refine ⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D.sp.cm (VS D) _ hL' hU',
    hL', hU', ?_, ?_, ?_⟩
  · rw [mem_gmap_inv, z_eq hfr]
    exact hz
  · ext v
    change v ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ⊓ toO (VS D) F0.X ↔ v ∈ XS D F0
    rw [mem_XS hfr, ← hX]
    change _ ↔ g v ∈ Λ ⊓ toO (VS D) G'.X
    simp only [Submodule.mem_inf, toO, Submodule.restrictScalars_mem]
    rw [mem_gmap_inv, mem_X hfr]
  · intro c hc
    apply hprim c
    have := mem_Lsub hg hfr Λ _ hc
    rw [map_smul, z_eq hfr] at this
    exact this

end GlobalTheory.RowLatTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusCommutesWithUnipotent
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalSetup

theorem exists_seq {k : ℕ} (u : Fin k → ℝ) : ∃ U : ℕ → ℝ, ∀ i : Fin k, U (i.val + 1) = u i :=
  ⟨fun n => if h : n - 1 < k then u ⟨n - 1, h⟩ else 0, fun i => by simp⟩

theorem exists_setup (hH : Hyps) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Mt k r)} {R : (Fin (2 * r + k + 1) → ℤ) → Rep k r}
    (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) (hS : SideG k r z π u μW μN μG νq) {c : ℝ} (hc : 0 < c)
    (hd : ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS (PI.BesselPeriodGGP.eps48 k r) mu →
      ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * fdegHC mu) :
    ∃ l : ∀ ν, (R ν).H → Wp,
      Setup lam u b bv ga h q0 z π μW μN μG νq R l (fun ν => c * fdegHC (fun a => lam a + (ν a : ℝ))) := by
  obtain ⟨⟨-, -, -, -, hG⟩, hν⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  have h1 : ∀ ν, ∃ l : (R ν).H → Wp, n1 ν ≤ q0 → IsBeL (R ν) z π μW μN l := by
    intro ν
    by_cases hq : n1 ν ≤ q0
    · obtain ⟨l, hl⟩ := GlobalTheory.exists_normalised_bessel_map hH k r _ _ (h / 2) (R ν) Wp _ _ _ _ _ _ _ (hF ν hq)
        (hν ν hq).2.2.1 hG hS
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h' => absurd h' hq⟩
  choose l hl using h1
  exact ⟨l, hN, hF, hS, fun ν hq => ⟨hl ν hq,
    mul_pos hc (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hN ν hq).1, hd _ _ (hF ν hq)⟩⟩

theorem exists_setup_both : Hyps → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w w' θ W hTT hθ hW t ht hNt hψ R hF
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW
  have hv : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]
    exact _root_.GlobalTheory.haarLie_isHaarOn_Nset _ _ _ (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  obtain ⟨U, hU⟩ := exists_seq (uS D w τ)
  obtain ⟨U', hU'⟩ := exists_seq (uS D w' τ)
  have s1 : SideG D.R.k D.R.rS W.z W.π U W.μW W.μN W.μG W.νS :=
    ⟨z1, hT1, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U _ _ z1 hT1 c1 hU, w1, hNH, hG, q1⟩
  have s2 : SideG D.R.k D.R.rS W.z' W.π' U' W.μW' W.μN W.μG W.νS' :=
    ⟨z2, hT2, ⟨_, c2⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ U' _ _ z2 hT2 c2 hU', w2, hNH, hG, q2⟩
  have m1 := (GlobalTheory.T.torus_normaliser_bessel hH _ _ _ _ _ _ _ _ _ _ _ t ht hNt (hψ _ z1).1 (hψ _ z1).2 s1).1
  have m2 := (GlobalTheory.T.torus_normaliser_bessel hH _ _ _ _ _ _ _ _ _ _ _ t ht hNt (hψ _ z2).1 (hψ _ z2).2 s2).1
  obtain ⟨c, hc, hd⟩ := GlobalTheory.BesselDegree.schur_fdeg hH D.R.k D.R.rS (PI.BesselPeriodGGP.eps48 _ _) W.μG hG
  obtain ⟨l, hl⟩ := exists_setup hH (_root_.GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w U hU).1 hF m1 hc
    fun mu R h => (hd mu R h).1
  obtain ⟨l', hl'⟩ := exists_setup hH (_root_.GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w' U' hU').1 hF m2 hc
    fun mu R h => (hd mu R h).1
  exact ⟨U, U', l, l', _, hl, hl'⟩

end GlobalTheory.Amp.LocalSetup
end

