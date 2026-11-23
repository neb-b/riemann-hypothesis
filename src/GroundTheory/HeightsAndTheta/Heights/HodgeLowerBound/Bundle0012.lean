module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem StokesLimitPos.proof (hG : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement)
    (hTel : StokesTelescope.Statement) (hNs : NbarSemipos.Statement) (hTp : StokesLimitTp.Statement)
    (hT : StokesLimitT.Statement) (hE : StokesLimitEps.Statement) : StokesLimitPos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B a hII hpos hB hAr hyp
  have hc0 : (0 : ℝ) ≤ ((D.n + 1 : ℕ) : ℝ) := by positivity

  have step : ∀ m : ℕ, ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
      X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1) ≤ X.topNLim B 1 (m + 1) := by
    intro m
    have hp : 1 ≤ 1 := le_rfl
    have hpq : 1 ≤ m + 1 := by omega
    obtain ⟨t₁, ht₁, hN⟩ := hNs II Ψ K ι Ω E D O Lt X B 1 (m + 1) hp hpq
    obtain ⟨tP, htP, hP⟩ := hpos B 1 (m + 1) hB hp hpq
    obtain ⟨tH, htH, hH⟩ := hyp 1 (m + 1) hp hpq
    obtain ⟨t₂, ht₂, hTp'⟩ := hTp II Ψ K ι Ω E D O Lt X B 1 (m + 1) hp hpq

    have stepT : ∀ t : ℝ, 0 < t → t ≤ min t₁ t₂ →
        ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) * X.degN B 1 (m + 1) t) -
          ((D.n + 1 : ℕ) : ℝ) * X.Vb B 1 (m + 1) t ≤ X.topN B 1 (m + 1) t := by
      intro t ht0 ht1
      have hNt := hN t ht0 (ht1.trans (min_le_left _ _))
      obtain ⟨hlim, hVb⟩ := hTp' t ht0 (ht1.trans (min_le_right _ _)) hNt
      have hev : ∀ᶠ t' in 𝓝[>] (0 : ℝ),
          ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) * X.degN B 1 (m + 1) t) -
            ((D.n + 1 : ℕ) : ℝ) * X.I0 B 1 (m + 1) t t' ≤ X.topN B 1 (m + 1) t := by
        filter_upwards [Ioc_mem_nhdsGT (lt_min htP htH)] with t' ht'
        have hsP := (hP t' ht'.1 (ht'.2.trans (min_le_left _ _))).1
        have htel := hTel II Ψ K ι Ω E D O Lt X B 1 (m + 1) t t' hII hpq hsP hNt
        have hh := hH t' ht'.1 (ht'.2.trans (min_le_right _ _))
        have hdeg : geomDegMUc X.H X.S' B 1 (m + 1) t' = X.degN B 1 (m + 1) t := by
          unfold geomDegMUc ComponentSetting.degN
          congr 1
          rw [hG K ι Ω D.y D.n _ D.arith hsP.1, hG K ι Ω D.y D.n _ D.arith hNt.1]
          congr 1
          simp only [ComponentSetting.MUq, MUc, ComponentSetting.NbarQ, smoothRepConj_a, smoothRep_a]
          rfl
        rw [hdeg] at hh
        have e : ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t) = ((D.n + 1 : ℕ) : ℝ) * (a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t := by ring
        linarith
      have hL : Tendsto (fun t' => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
          X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.I0 B 1 (m + 1) t t') (𝓝[>] 0)
          (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.Vlim B 1 (m + 1) t)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)
      have h1 := le_of_tendsto hL hev
      have h2 := mul_le_mul_of_nonneg_left hVb hc0
      linarith
    obtain ⟨hT1, hT2, hT3⟩ := hT II Ψ K ι Ω E D O Lt X B 1 (m + 1) hII hAr hp hpq
    have hL : Tendsto (fun t => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
        X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.Vb B 1 (m + 1) t) (𝓝[>] 0)
        (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
          X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1))) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hT3)).sub (tendsto_const_nhds.mul hT2)
    refine le_of_tendsto_of_tendsto hL hT1 ?_
    filter_upwards [Ioc_mem_nhdsGT (lt_min ht₁ ht₂)] with t ht using stepT t ht.1 ht.2

  obtain ⟨hE1, hE2, hE3⟩ := hE II Ψ K ι Ω E D O Lt X B hII hAr
  have hε : Tendsto (fun m : ℕ => ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Nat.cast_add, Nat.cast_one] using h0
  have hL : Tendsto (fun m : ℕ => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
      X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1)) atTop
      (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - 0 * D.KA) * degMu X.H) -
        ((D.n + 1 : ℕ) : ℝ) * (meanU X.H X.Cd * degMu X.H / 2))) :=
    (tendsto_const_nhds.mul ((tendsto_const_nhds.sub (hε.mul tendsto_const_nhds)).mul hE3)).sub
      (tendsto_const_nhds.mul hE2)
  have key := le_of_tendsto_of_tendsto' hL hE1 step
  calc ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H
      = ((D.n + 1 : ℕ) : ℝ) * ((a - 0 * D.KA) * degMu X.H) -
        ((D.n + 1 : ℕ) : ℝ) * (meanU X.H X.Cd * degMu X.H / 2) := by ring
    _ ≤ arLim X.H X.S B := key

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioFieldEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def HodgeFlagRatioFieldEq.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (c : ∀ k, Pl.ιY k), (∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0) →
    IntermediateField.adjoin Ω (coneRatios (Pl.flagGenericPoint B) c) =
      IntermediateField.adjoin Ω (Set.range (flagMinorRatio0 Ω Ψ D.N D.j))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def HodgeFlagSpan.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (τ : Ψ) (i : Fin (D.N - 1)),
    Submodule.span Ω (Set.range (Pl.pluecker0 B τ i)) =
      Submodule.span Ω (Set.range (flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuMeasureLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuMeasureLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      Tendsto (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
          (fun _ z => Real.log ((muReg X.H X.S B t).h z)) (fun z => X.Cd.cuspWeight z / 2))
        (𝓝[>] 0) (𝓝 (meanU X.H X.Cd * degMu X.H / 2)) ∧
      Tendsto (fun t => geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n) (𝓝[>] 0) (𝓝 (degMu X.H))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegSmooth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuRegSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg X.H X.S B t)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsOmNPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def OmNPoly.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      ∃ v d : ℕ → ℝ → ℝ,
        v 0 = (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
          (fun _ z => Real.log ((muReg X.H X.S B t).h z)) (fun z => X.Cd.cuspWeight z / 2)) ∧
        d 0 = (fun t => geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n) ∧
        ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ),
          X.Vb B 1 q t = ∑ i ∈ Finset.range (D.n + 1), v i t * (1 / (q : ℝ)) ^ i ∧
          X.degN B 1 q t = ∑ i ∈ Finset.range (D.n + 1), d i t * (1 / (q : ℝ)) ^ i

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsPtsNull (P : Ideal (MRing ι)) (e : ℕ) (N : Set ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} = 0

def IsPtsIntegrable (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ φ g y w)

def PtsBddConv.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (r : ℝ) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ) (g₀ : ((Σ k, ι k) → ℂ) → ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (C s₀ : ℝ),
    IsArithVar P (e + 1) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm L → 0 < r → IsPtsNull P e N → 0 < s₀ →
    (∀ s : ℝ, 0 < s → s < s₀ → (∀ z ∈ mcPts P, |g s z| ≤ C) ∧ ContinuousOn (g s) (mcPts P \ N) ∧
      ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, g s (torusSmul c z) = g s z) →
    (∀ z ∈ mcPts P, z ∉ N → Tendsto (fun s => g s z) (𝓝[>] 0) (𝓝 (g₀ z))) →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ ∧
      Tendsto (fun s => ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s)) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀))

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTTop
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def StokesLimitTTop.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B → 1 ≤ p → p ≤ q →
      ∃ L : ℝ, Tendsto (X.topN B p q) (𝓝[>] 0) (𝓝 L)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTVb
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def StokesLimitTVb.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ),
    1 ≤ p → p ≤ q → ∃ L : ℝ, Tendsto (X.Vb B p q) (𝓝[>] 0) (𝓝 L)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesStep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def stokesMixPot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n i : ℕ) :
    Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (A'.h z) else Real.log (A.h z)

def StokesStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n i : ℕ)
    (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), IsArithVar P (n + 1) → A'.a = A.a → IsSemipositiveH P A → IsSemipositiveH P A' →
    i < n →
      ptsIntegral P (stokesMixPot A A' n (i + 1)) (fun z => Real.log (A'.h z) - Real.log (A.h z)) ≤
        ptsIntegral P (stokesMixPot A A' n i) (fun z => Real.log (A'.h z) - Real.log (A.h z))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTopNPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def TopNPoly.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      ∃ c : ℕ → ℝ → ℝ, c 0 = arLimFun X.H X.S B ∧
        ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ),
          X.topN B 1 q t = ∑ i ∈ Finset.range (D.n + 2), c i t * (1 / (q : ℝ)) ^ i

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVertFactorPos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def VertFactorPos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ),
    p ∈ D.S → ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < D.vertFactor p z

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

