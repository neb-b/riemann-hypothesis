module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineModel
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.LineMu
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDimX
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsZhangLowerX
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.FlagLine
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def AmpleOnGenericFibre (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  ∀ (W : Ideal (MRing ι)) (d : ℕ), 1 ≤ d → IsArithVar W (d + 1) → P ≤ W → 0 < geomDeg W A d

def OffBoundary (Bd : Set ((Σ k, ι k) → ℂ)) (W : Ideal (MRing ι)) : Prop :=
  ∀ z ∈ mcPts W, z ∉ Bd

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure ComponentSetting (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] where

  H : HodgeData D

  Cd : CuspData D O Lt

  M : XModel D

  S : LogLogRegularisationSetting M D.Xo (muLine H)

  S_tied : S.IsTied

  S' : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorr H Cd)

  S'_tied : S'.IsTied

  rd : ℝ

  Lval : ℝ

namespace ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
  (X : ComponentSetting D O Lt)

abbrev MUq (B p q : ℕ) (t' : ℝ) : HermLine ι := MUc X.H X.S' B p q t'

def La (B : ℕ) : ℝ := abelian₂ B X.rd X.Lval

end ComponentSetting

variable {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

def CuspBundlePos (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (X.MUq B p q t') ∧
      NefOnFibres (mCoordIdeal D.y) (X.MUq B p q t').a ∧
      AmpleOnGenericFibre (mCoordIdeal D.y) (X.MUq B p q t')

def HtInterior (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def HtBoundary (Ch : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal D.y ≤ W → ¬ OffBoundary D.Bd W →
      -(Ch * D.f * D.j' * X.La B) - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W

def CuspMean (Cu : ℝ) (X : ComponentSetting D O Lt) : Prop :=
  1 ≤ D.j' → 3 * D.j' + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B →
    meanU X.H X.Cd ≤ Cu * D.f * D.j' * X.La B

def StokesLimit.Hyp (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ((D.n + 1 : ℕ) : ℝ) * (a - (p : ℝ) / q * D.KA) * geomDegMUc X.H X.S' B p q t' ≤
      topMUc X.H X.S' B p q t'

def StokesLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (a : ℝ),
    IsIntersectionSystem II → 4 * D.f + 2 ≤ B → ArLimExists X.H X.S B → StokesLimit.Hyp X B a →
      ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H ≤ arLim X.H X.S B

def GrassmannianHeightZTwo.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (cf : ℚ) (e : ℝ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 → 0 < Jint Ψ N j cf →
    (∀ Z : Matrix (Fin (N - j)) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) →
      1 / 2 * Real.log (1 + Z * Z.conjTranspose).det.re ≤ e) →
    -hFl Ψ N II (FA Ψ N j cf) ≤
      ((dimN Ψ N j + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (Fintype.card Ψ : ℝ) * e

def MUConjInvariant (X : ComponentSetting D O Lt) : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsConjInvariantH (X.MUq B p q t')

def slX (X : ComponentSetting D O Lt) (B : ℕ) : ℝ :=
  arLim X.H X.S B / (((D.n + 1 : ℕ) : ℝ) * degMu X.H)

namespace Line

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenericMinors
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

abbrev GenFrac (F : Type) [Field F] (Ψ : Type) (n : ℕ) : Type :=
  FractionRing (MvPolynomial (Ψ × Fin n × Fin n) F)

def genMatFr (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b =>
    algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n) (X (τ, a, b))

def flagMinorRatio (F : Type) [Field F] (Ψ : Type) (n : ℕ) (q : Ψ × Σ j : Fin (n - 1), PluckerBlocks n n j) :
    GenFrac F Ψ n :=
  flagMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2 / _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr F Ψ n q.1) q.2.1

abbrev PivotIdx (Ψ : Type) (n : ℕ) : Type := Ψ × Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) < b}

def pivotRatio (F : Type) [Field F] (Ψ : Type) (n : ℕ) (q : PivotIdx Ψ n) : GenFrac F Ψ n :=
  pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr F Ψ n q.1) q.2.1

theorem PlueckerData.ofΩ_eq {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type}
    [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D)
    (x : Ω) : Pl.ofΩ x = algebraMap Ω (GenFrac Ω Ψ D.N) x := by
  rw [PlueckerData.ofΩ, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply Ω (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) (GenFrac Ω Ψ D.N)]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RegWeightLevi
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {A : HermLine ι}

theorem LogLogRegularisationSetting.eventually_closedBall_subset (S : LogLogRegularisationSetting M Xo A) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.R.mid j),
      closedBall (S.R.chart j x) t ⊆ (S.R.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.R.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.R.chart j '' closure (S.R.mid j)) :=
    hc.image_of_continuousOn ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))
  have hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.R.chart j).map_source (S.R.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.R.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem LogLogRegularisationSetting.eventually_chartLevi (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧
      ∀ k : Fin S.R.N, ∀ x ∈ S.R.mid k, ∀ w : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖w‖ ^ 2 ≤
          levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k x) w := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.GlueRegularised.full M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

