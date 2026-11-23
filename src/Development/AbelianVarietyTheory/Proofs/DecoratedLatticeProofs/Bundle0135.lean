module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemClosureHeckeSplitCongruenceOfFinPartOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingCharIndicatorDualLatticeCosets
section
noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum InDual Lifts)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.Comm.DualCosets

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem inDual_add {L : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual L η) (h' : InDual L ξ) :
    InDual L (η + ξ) := by
  intro y hy
  rw [add_dotProduct]
  exact add_mem (h y hy) (h' y hy)

theorem inDual_sub {L : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual L η) (h' : InDual L ξ) :
    InDual L (η - ξ) := by
  intro y hy
  rw [sub_dotProduct]
  exact sub_mem (h y hy) (h' y hy)

theorem inDual_smul {L : Submodule 𝒪[k] (n → k)} {η : n → k} (h : InDual L η) (s : 𝒪[k]) :
    InDual L (s • η) := by
  intro y hy
  rw [smul_dotProduct, Algebra.smul_def]
  exact mul_mem s.2 (h y hy)

theorem isLocallyConstant_of_periodic (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] {g : (n → k) → ℂ}
    (hg : ∀ η ξ, InDual L ξ → g (η + ξ) = g η) : IsLocallyConstant g := by
  have hD := (dual_compact_open L).2
  refine (IsLocallyConstant.iff_exists_open g).2 fun x => ?_
  refine ⟨{η | InDual L (η - x)}, hD.preimage (continuous_sub_right x), ?_, fun η hη => ?_⟩
  · intro y _
    simp
  · have h := hg x (η - x) hη
    rwa [add_sub_cancel] at h

private theorem secondCountableTopology_localField' (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : SecondCountableTopology K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  obtain ⟨r⟩ := (IsRankLeOne.nonempty : Nonempty (ValuativeRel.RankLeOneStruct K))
  letI : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).RankOne :=
    { hom' := r.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := r.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact secondCountable_of_proper

variable [MeasurableSpace k] [BorelSpace k]

theorem integrable_of_periodic (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (q : Unif k)
    (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] {g : (n → k) → ℂ}
    (hg : ∀ η ξ, InDual L ξ → g (η + ξ) = g η) (hs : ∀ η, g η ≠ 0 → InDual L (q.1 • η)) : Integrable g μ := by
  haveI := secondCountableTopology_localField' k
  have hlc := isLocallyConstant_of_periodic L hg
  have hK : IsCompact {η : n → k | InDual L (q.1 • η)} := by
    have h2 : {η : n → k | InDual L (q.1 • η)} =
        (Homeomorph.smulOfNeZero ((q.1 : 𝒪[k]) : k) q.ne_zero) ⁻¹' {η | InDual L η} := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Homeomorph.smulOfNeZero_apply, Algebra.smul_def]
      rfl
    rw [h2, Homeomorph.isCompact_preimage]
    exact (dual_compact_open L).1
  have hcs : HasCompactSupport g := HasCompactSupport.intro hK fun η hη => by
    by_contra h
    exact hη (hs η h)
  exact hlc.continuous.integrable_of_hasCompactSupport hcs

end GlobalTheory.FinPl.Comm.DualCosets

namespace GlobalTheory.FinPl.Comm.DualCosets

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem dualInd_add (L : Submodule 𝒪[k] (n → k)) (η ξ : n → k) (hξ : InDual L ξ) :
    dualInd L (η + ξ) = dualInd L η := by
  unfold dualInd
  by_cases h : InDual L η
  · rw [if_pos (inDual_add h hξ), if_pos h]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    simpa using inDual_sub h' hξ

theorem dualInd_supp (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (η : n → k) (h : dualInd L η ≠ 0) :
    InDual L (q.1 • η) := by
  unfold dualInd at h
  by_cases hd : InDual L η
  · exact inDual_smul hd q.1
  · exact absurd (if_neg hd) h

theorem cosetInd_add (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : Module.Dual 𝓀[k] (Red L)) (η ξ : n → k)
    (hξ : InDual L ξ) : cosetInd q L f (η + ξ) = cosetInd q L f η := by
  unfold cosetInd
  have e : (∃ F : n → k, Lifts L F f ∧ InDual L (η + ξ - q.inv • F)) ↔
      ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F) := by
    constructor
    · rintro ⟨F, hF, hd⟩
      refine ⟨F, hF, ?_⟩
      have h := inDual_sub hd hξ
      rwa [show η + ξ - q.inv • F - ξ = η - q.inv • F by abel] at h
    · rintro ⟨F, hF, hd⟩
      refine ⟨F, hF, ?_⟩
      have h := inDual_add hd hξ
      rwa [show η - q.inv • F + ξ = η + ξ - q.inv • F by abel] at h
  by_cases h : ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F)
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h]

theorem inDual_of_lifts {L : Submodule 𝒪[k] (n → k)} {F : n → k} {f : Module.Dual 𝓀[k] (Red L)} (h : Lifts L F f) :
    InDual L F := by
  intro y hy
  obtain ⟨s, hs, -⟩ := h ⟨y, hy⟩
  rw [← hs]
  exact s.2

theorem cosetInd_supp (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : Module.Dual 𝓀[k] (Red L)) (η : n → k)
    (h : cosetInd q L f η ≠ 0) : InDual L (q.1 • η) := by
  unfold cosetInd at h
  by_cases hc : ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F)
  · obtain ⟨F, hF, hd⟩ := hc
    have hq1 : q.1 • q.inv = 1 := by
      rw [Algebra.smul_def, Unif.inv]
      exact mul_inv_cancel₀ q.ne_zero
    have hq : q.1 • (q.inv • F) = F := by
      rw [← smul_assoc, hq1, one_smul]
    have h3 : q.1 • η = q.1 • (η - q.inv • F) + F := by
      rw [smul_sub, hq, sub_add_cancel]
    rw [h3]
    exact inDual_add (inDual_smul hd q.1) (inDual_of_lifts hF)
  · exact absurd (if_neg hc) h

theorem inner_add (χ : AddChar k Circle) (hχ : HasConductor χ 1) {e : k} (he : e = 1 ∨ e = -1)
    [MeasurableSpace k] (μ : Measure (n → k)) (L : Submodule 𝒪[k] (n → k)) {a : (n → k) → ℂ}
    (ha : ∀ y, y ∉ L → a y = 0) (η ξ : n → k) (hξ : InDual L ξ) :
    ∫ y, a y * (χ (e * ((η + ξ) ⬝ᵥ y)) : ℂ) ∂μ = ∫ y, a y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ := by
  congr 1
  funext y
  by_cases hy : y ∈ L
  · have hm : e * (ξ ⬝ᵥ y) ∈ 𝒪[k] := by
      rcases he with rfl | rfl
      · simpa using hξ y hy
      · simpa using neg_mem (hξ y hy)
    have h1 : χ (e * (ξ ⬝ᵥ y)) = 1 := apply_int_eq_one hχ ⟨_, hm⟩
    rw [add_dotProduct, mul_add, AddChar.map_add_eq_mul, h1, mul_one]
  · rw [ha y hy, zero_mul, zero_mul]

end GlobalTheory.FinPl.Comm.DualCosets

namespace GlobalTheory.FinPl.Comm.DualCosets

theorem fpair_charInd_dualInd_add_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n), fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red) = fpair χ e μ (vecInd Q.lat) (dualInd Q.lat) := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ Q
  have ha : ∀ y, y ∉ Q.lat → charInd (resChar χ hχ q) Q y = 0 := fun y hy => by
    simp [charInd, vecInd, hy]
  have hF : ∀ (L : Submodule 𝒪[k] (n → k)), L = Q.lat → ∀ η ξ, InDual L ξ →
      (∫ y, charInd (resChar χ hχ q) Q y * (χ (e * ((η + ξ) ⬝ᵥ y)) : ℂ) ∂μ) =
        ∫ y, charInd (resChar χ hχ q) Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ := by
    rintro L rfl η ξ hξ
    exact inner_add χ hχ he μ Q.lat ha η ξ hξ
  have hint1 : Integrable (fun η => (∫ y, charInd (resChar χ hχ q) Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) *
      dualInd Q.lat η) μ := by
    refine integrable_of_periodic μ q Q.lat (fun η ξ hξ => ?_) (fun η h => ?_)
    · simp only [hF Q.lat rfl η ξ hξ, dualInd_add Q.lat η ξ hξ]
    · exact dualInd_supp q Q.lat η (right_ne_zero_of_mul h)
  have hint2 : ∀ Q'' ∈ withLat Q.lat, Integrable (fun η => (∫ y, charInd (resChar χ hχ q) Q y *
      (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) * cosetInd q Q''.lat Q''.red η) μ := by
    intro Q'' hQ''
    have hl : Q''.lat = Q.lat := mem_withLat.1 hQ''
    refine integrable_of_periodic μ q Q''.lat (fun η ξ hξ => ?_) (fun η h => ?_)
    · simp only [hF Q''.lat hl η ξ hξ, cosetInd_add q Q''.lat Q''.red η ξ hξ]
    · exact cosetInd_supp q Q''.lat Q''.red η (right_ne_zero_of_mul h)
  have key : fpair χ e μ (charInd (resChar χ hχ q) Q)
      (dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red) =
      fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) +
        ∑ Q'' ∈ withLat Q.lat, fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) := by
    simp only [fpair]
    rw [← integral_finsetSum _ hint2, ← integral_add hint1 (integrable_finsetSum _ hint2)]
    congr 1
    funext η
    simp [mul_add, Finset.mul_sum]
  obtain ⟨ε, hε⟩ : ∃ ε : 𝓀[k]ˣ, (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1) := by
    rcases he with h | h
    · exact ⟨1, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨-1, Or.inr ⟨h, rfl⟩⟩
  rw [key, _root_.GlobalTheory.FinPl.Comm.fpair_charInd_dualInd k n q χ hχ e he μ Q, zero_add, Finset.sum_eq_single (ε • Q)]
  · exact (GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hε μ Q (ε • Q) (Pair.dia_lat ε Q)).1 rfl
  · intro Q'' hQ'' hne
    exact (GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hε μ Q Q'' (mem_withLat.1 hQ'')).2 hne
  · intro h
    exact absurd (mem_withLat.2 (Pair.dia_lat ε Q)) h

end GlobalTheory.FinPl.Comm.DualCosets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteVectorsDiscreteSeriesSmoothAbsolutelyIrre
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinLoc

open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

theorem kFin_rank_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (h0 : V.rank = 0) :
    kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ),
      GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  have hsub : ∀ g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ, g = g' := fun g g' =>
    Matrix.ext fun i _ => absurd i.2 (by omega)
  have hσ1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  have hσ : ∀ g, M.σ τ g = 1 := fun g => by rw [hsub g 1, hσ1]
  have hrep : ∀ g, M.rep τ g = 1 := fun g => hσ _
  refine ⟨fun x _ => Submodule.subset_span ?_, fun _ => 0, ⟨fun X _ v => ?_, fun X _ v w => by simp⟩, ?_⟩
  · intro k Xs _
    simp only [hrep, ContinuousLinearMap.one_apply]
    exact contDiff_const
  · simp only [hrep, ContinuousLinearMap.one_apply, LinearMap.zero_apply, Submodule.coe_zero]
    exact hasDerivAt_const _ _
  · haveI : CompleteSpace (M.H τ) := (M.ds τ).1

    have hline : ∀ x y : M.H τ, x ≠ 0 → ∃ c : ℂ, c • x = y := fun x y hx => by
      have hcl : IsClosed ((ℂ ∙ x : Submodule ℂ (M.H τ)) : Set (M.H τ)) := Submodule.closed_of_finiteDimensional _
      rcases (M.ds τ).2.2.2.1 _ hcl (fun g _ v hv => by rwa [hσ, ContinuousLinearMap.one_apply]) with hb | ht
      · exact absurd ((Submodule.span_singleton_eq_bot).1 hb) hx
      · exact Submodule.mem_span_singleton.1 (ht ▸ Submodule.mem_top)
    have hK : ∀ x y : kFin M τ, x ≠ 0 → ∃ c : ℂ, c • x = y := fun x y hx => by
      obtain ⟨c, hc⟩ := hline x y (fun e => hx (Subtype.ext e))
      exact ⟨c, Subtype.ext hc⟩
    refine ⟨fun N _ => ?_, fun T _ => ?_⟩
    · by_cases hN : N = ⊥
      · exact Or.inl hN
      · right
        obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
        refine eq_top_iff.2 fun y _ => ?_
        obtain ⟨c, rfl⟩ := hK x y hx0
        exact N.smul_mem c hxN
    · by_cases hz : ∀ x : kFin M τ, x = 0
      · exact ⟨0, LinearMap.ext fun x => by rw [hz x]; simp⟩
      · push_neg at hz
        obtain ⟨x, hx0⟩ := hz
        obtain ⟨c, hc⟩ := hK x (T x) hx0
        refine ⟨c, LinearMap.ext fun y => ?_⟩
        obtain ⟨d, rfl⟩ := hK x y hx0
        rw [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]

theorem kFin_smooth_absIrr (hH : GlobalTheory.Published.HarishChandraModules) (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S) (τ : D.what₂.Tau) :
    kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ),
      GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  rcases Nat.eq_zero_or_pos V.rank with h0 | hpos
  · exact kFin_rank_zero M τ h0
  obtain ⟨p, q, e, he⟩ : ∃ p q : ℕ, ∃ e : Ix p q ≃ Fin V.rank, GlobalTheory.RealPar.BlockOrd e (M.ε τ) :=
    ⟨_, _, GlobalTheory.RealPar.exists_blockOrd (M.ε τ) rfl rfl⟩
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hn : 1 ≤ p + q := hcard ▸ hpos
  let T : GrpData p q := Classical.choice (GlobalTheory.DetSqrtCover.nonempty_grpData p q)
  let P : GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters.SignedPar V.rank :=
    ⟨M.lam τ, M.ε τ, GlobalTheory.DSParam.isHCParam_of_isDS _ _ _ _ _ (M.enum τ).1 (M.ds τ)⟩
  have hsc : SignCompat (M.ε τ) e := by
    rintro (a | a)
    · exact he.1 a
    · exact he.2.1 a
  obtain ⟨R, U, -, hU⟩ := GlobalTheory.CoverModel.exists_pull T (fun U hU => ((hH.1 p q hn T).1 U hU).2.1) P
    (e := e) he (σ := M.σ τ) (M.ds τ)
  have hM : Matches R M τ (plainMat e) 0 U :=
    GlobalTheory.CoverModel.matches_of_grp hH (s := RingHom.id ℂ) (fun _ => rfl) R M τ
      (GlobalTheory.CoverModel.isFormIso_plainMat hsc) 0 U (fun g x => by simp [hU, plainMat])
  obtain ⟨hs, a, ha⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D V S M τ _ _ T R _ 0 _ hM
  have hAI := ((hH.1 p q hn T).1 R.U ⟨R.nontriv, R.irred⟩).2.2 R.HK R.ι ⟨R.ι_inj, R.ι_range, R.der⟩
  exact ⟨hs, a, ha, GlobalTheory.KFinIrr.absIrr_kFin D V S M τ _ _ T R _ 0 U.toLinearEquiv a hM hAI.2 hAI.1 ha⟩

end GlobalTheory.KFinLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemClosureHeckeSplitCongruenceOfFinPartOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_heckeSplitCongruence_of_finPart_one : ∀ (D : D7) (N : ℕ), 0 < N → ∀ z : (AE D)ˣ, finPart D (z : AE D) = 1 → z ∈ closure (GlobalTheory.HeckeSplitAll.grpH D N : Set (AE D)ˣ) := by
  first | exact @GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one | exact GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one | (intros; apply GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
section
namespace I195MixedCoordinates_052755a8a20ae3f544412ebb

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_052755a8a20ae3f544412ebb

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixValues

theorem mixS_theta (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S S₀ T : HSp D) (ρ : ℕ)
    (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ))
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) :
    IsThetaFunO ψ S₀ T ((_root_.I195MixedCoordinates_052755a8a20ae3f544412ebb.source d) T ψ μ 𝓕 f x) := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · change IsThetaFunO ψ S₀ T (I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 f x)
    rw [(_root_.GlobalTheory.Unf.mixRankZero D ψ).1 S S₀ T d μ 𝓕 hμ f x]
    exact ((_root_.GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D ψ S S₀ T d hψ).2.2.1 f).2 hf
  · obtain ⟨hiso, hrat, -, -, -, hres, -⟩ := _root_.GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d
    change IsThetaFunO ψ S₀ T (I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f x)
    rw [hres]
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hrat]; exact hμ
    have hg := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 (d.extX T x) f hf
    exact ((GlobalTheory.TowerRestrict.res_theta D S S₀ T ρ d.e d.i₀ (hiso hρ) ψ hψ μ 𝓕 hμ').1 _ hg).2.1

end GlobalTheory.MixValues

theorem GlobalTheory.MixValues.mixed_values : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D := by
  intro D ψ hψ
  refine ⟨fun S S₀ T ρ d μ 𝓕 hμ f hf x => GlobalTheory.MixValues.mixS_theta D ψ hψ S S₀ T ρ d μ 𝓕 hμ f hf x, ?_⟩
  intro S T T₀ ρ d μ 𝓕 hμ f hf y
  obtain ⟨μ', 𝓕', hμ', -, -, -, hsw⟩ := _root_.GlobalTheory.MixSwap.mixS_cj_dagger D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  have hcd := _root_.GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ
  have h1 : IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) := ((hcd S T).2.2.1 f).2 hf
  have h2 := GlobalTheory.MixValues.mixS_theta D ψ hψ T T₀ S ρ d μ' 𝓕' hμ' _ h1 (incA D D.host.xi0⁻¹ • y)
  change IsThetaFunO ψ T₀ S (I195MixedCoordinates_79cab7195843a34bfe21655d.source d S ψ μ' 𝓕' _ (incA D D.host.xi0⁻¹ • y)) at h2
  rw [hsw] at h2
  exact ((hcd S T₀).2.2.1 _).1 h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormMuInvDetZeroOrOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.ScalarModulusS

theorem norm_muInvDet_zero_or_one : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i < N.R.m → ∀ (n : ℕ) (L : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)) (σ : X.K →+* ℂ), ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 0 ∨ ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h i hi n L fr σ
  obtain ⟨hH, -, ⟨-, hσ, -, ⟨eta, ht⟩, -, hsel⟩, -, hmu, -, hI, -, -⟩ := h
  obtain ⟨-, -, -, -, -, -, hX, -, -, hPr, -⟩ := hH
  rw [← hσ] at ht
  have hS : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := by
    intro P
    classical
    subst hmu
    rcases Finset.mem_union.1 P.2 with h | h
    · exact h
    · have h0 := twistPrimes_trivialTuple_empty sel Sg
      exact absurd (h0 ▸ h) (Finset.notMem_empty _)
  have hnorm : ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 1 := by
    have hU := fun P x y hy => GlobalTheory.ScalarModulus.norm_eq_one_of_locK hX.ok hPr
      (ht.mu0 ⟨i, hi⟩) P x y hy σ
    have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
        ‖σ (Ch.muVal ⟨i, hi⟩ P : X.K)‖ = 1 := fun P hP =>
      hU P (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
    have hfin := GlobalTheory.CharVal.finOrder_tup mu
    have hmuq : ∀ P : rowSG Pr sel mu, ‖σ (cst.muq (i + 1) P)‖ = 1 := by
      intro P
      have hq : ‖σ ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K)‖ = 1 :=
        GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_qVal hfin P.1)
      have hqG := hI.muqG i hi P (hS P) (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
      have hloc : G.σ₀ ((cst.muq (i + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
          (((G.mu0 ⟨i, hi⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
        rw [map_inv₀, map_mul, hqG, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
      have hnormLoc := hU P.1 _ _ hloc
      rwa [map_inv₀, map_mul, norm_inv, norm_mul, hq, mul_one, inv_eq_one] at hnormLoc
    have hoff : ‖σ (muOff sel (rowSG Pr sel mu) (mUof Ch mu i) L)‖ = 1 := by
      unfold muOff
      refine finprod_induction (fun x => ‖σ x‖ = 1) (by simp)
        (fun x y hx hy => by rw [map_mul, norm_mul, hx, hy, one_mul]) fun v => ?_
      split_ifs with hv
      · simp
      · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, norm_zpow, mUof, dite_eq_left hi, Units.val_mul,
          Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, norm_mul,
          norm_inv, norm_inv, hval _ (GlobalTheory.ColPeriod.Scal.g_notMem_sel hX.ok hPr hsel hv),
          GlobalTheory.GO.norm_map_of_finOrder _ (GlobalTheory.CharVal.finOrder_unifVal hfin _)]
        simp
    rw [muInvDet, map_mul, norm_mul, hoff, one_mul, map_prod, norm_prod]
    refine Finset.prod_eq_one fun P _ => ?_
    unfold muAt
    obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul X.E X.K P.1 (qOf P.1) (cst.muq (i + 1) P) _
      ((LinearEquiv.det (fr P) : X.Eˣ) : X.E)
      (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _)
        (GlobalTheory.ColPeriod.levelPrimes X Pr sel Sg mu hX.ok hPr hsel P).1.2) (Units.ne_zero _)
    rw [e, map_mul, map_zpow₀, norm_mul, norm_zpow, hmuq, GlobalTheory.GO.norm_map_of_finOrder _ hζ,
      one_zpow, one_mul]
  exact Or.inr hnorm

end GlobalTheory.ScalarModulusS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PgCLeTwoAtRecord
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc

noncomputable section

namespace GlobalTheory.Core.Deg

theorem pgC_le_two_at_record : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 2 := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' Formalism.L2.SG.Pf.splitPrimeLoc_holds
    Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := Formalism.L2.SG.KappaOffDiagonal.PgLe.one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := Formalism.L2.SG.KappaOffDiagonal.PgLe.one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (1 / 4) * Real.exp (1 / 4) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 2 := Formalism.L2.SG.KappaOffDiagonal.PgLe.exp_quarter_mul_exp_quarter_le_two

end GlobalTheory.Core.Deg
end
end

