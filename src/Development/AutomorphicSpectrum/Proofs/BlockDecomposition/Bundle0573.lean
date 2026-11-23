module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0547
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdClose
section
open Filter Topology
open GlobalTheory.CompanionTheory.EGlue PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.MCl

theorem nodup_of_close {ε : ℝ} (hε : ε < 1 / 4) {m n : Multiset ℂ}
    (h : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n) (hg : GapM n) : m.Nodup := by
  induction h with
  | zero => exact Multiset.nodup_zero
  | @cons a b as bs hab hrel ih =>
    have hgn : (b ::ₘ bs).Nodup := hg.1
    have hb : b ∉ bs := (Multiset.nodup_cons.1 hgn).1
    have hg' : GapM bs := by
      refine ⟨(Multiset.nodup_cons.1 hgn).2, fun x hx y hy hxy => ?_⟩
      exact hg.2 x (Multiset.mem_cons_of_mem hx) y (Multiset.mem_cons_of_mem hy) hxy
    refine Multiset.nodup_cons.2 ⟨fun ha => ?_, ih hg'⟩
    obtain ⟨y, hy, hay⟩ := Multiset.exists_mem_of_rel_of_mem hrel ha
    have hne : b ≠ y := fun e => hb (e ▸ hy)
    have h1 := hg.2 b (Multiset.mem_cons_self b bs) y (Multiset.mem_cons_of_mem hy) hne
    have h2 : ‖b - y‖ ≤ ‖a - b‖ + ‖a - y‖ := by
      have : b - y = (a - y) - (a - b) := by ring
      rw [this]
      calc ‖(a - y) - (a - b)‖ ≤ ‖a - y‖ + ‖a - b‖ := norm_sub_le _ _
        _ = ‖a - b‖ + ‖a - y‖ := add_comm _ _
    linarith

theorem prod_close (u : ℂ) (n : Multiset ℂ) : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ m : Multiset ℂ,
    Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε) m n →
      ‖(m.map (u + ·)).prod - (n.map (u + ·)).prod‖ < δ := by
  induction n using Multiset.induction_on with
  | empty =>
    intro δ hδ
    refine ⟨1, one_pos, fun m hm => ?_⟩
    have : m = 0 := Multiset.rel_zero_right.1 hm
    subst this
    simpa using hδ
  | cons b bs ih =>
    intro δ hδ
    have hc : ContinuousAt (fun p : ℂ × ℂ => p.1 * p.2) (u + b, (bs.map (u + ·)).prod) :=
      continuous_mul.continuousAt
    obtain ⟨δ', hδ', H⟩ := Metric.continuousAt_iff.1 hc δ hδ
    obtain ⟨ε₁, hε₁, H₁⟩ := ih δ' hδ'
    refine ⟨min ε₁ (δ' / 2), lt_min hε₁ (half_pos hδ'), fun m hm => ?_⟩
    obtain ⟨a, as, hab, has, rfl⟩ := Multiset.rel_cons_right.1 hm
    have has' : Multiset.Rel (fun x y : ℂ => ‖x - y‖ ≤ ε₁) as bs :=
      has.mono fun x _ y _ hxy => hxy.trans (min_le_left _ _)
    have h1 : ‖(u + a) - (u + b)‖ < δ' := by
      have e : (u + a) - (u + b) = a - b := by ring
      rw [e]
      have := hab.trans (min_le_right _ _)
      linarith
    have h2 := H₁ as has'
    have hd : dist ((u + a, (as.map (u + ·)).prod) : ℂ × ℂ) (u + b, (bs.map (u + ·)).prod) < δ' := by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      exact ⟨h1, h2⟩
    have h3 := H hd
    rw [dist_eq_norm] at h3
    simpa [Multiset.map_cons, Multiset.prod_cons] using h3

end GlobalTheory.CompanionTheory.EGlue.MCl

namespace GlobalTheory.CompanionTheory.EGlue

theorem mCloseFacts_holds : MCloseFacts := by
  refine ⟨fun ε m n B h hB x hx => ?_, fun ε m n hε h hg => MCl.nodup_of_close hε h hg,
    fun m n hm u => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := Multiset.exists_mem_of_rel_of_mem h hx
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa using norm_add_le (x - y) y
    have h2 := hB y hy
    have h3 : ‖x - y‖ ≤ ε := hxy
    linarith
  · rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨ε, hε, H⟩ := MCl.prod_close u n δ hδ
    filter_upwards [hm ε hε] with k hk
    rw [dist_eq_norm]
    exact H _ hk

end GlobalTheory.CompanionTheory.EGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectivePointChartRatio
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem ptP_mem_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c) :=
  CxPts.ofHom_mem _ _ _

theorem ev_ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (a : Γ(PSpace ℤ N, chart ℤ N c)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w) = chartHom N c w a :=
  CxPts.ev_ofHom _ _ _ a

theorem ev_ptP_ratio (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) (ratio ℤ N c i) (ptP N c w) = w i / w c := by
  rw [ev_ptP]
  by_cases h : i = c
  · subst h
    rw [ratio, ratioOn_self, map_one, div_self hc]
  · have e : (chartAlgEquiv ℤ N c).symm (ratio ℤ N c i) = X ⟨i, h⟩ := by
      rw [← chartAlgEquiv_X ℤ N c ⟨i, h⟩]
      exact AlgEquiv.symm_apply_apply _ _
    simp [chartHom, e]

theorem ptP_mem_chart_iff (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0 := by
  have e := CxPts.mem_ptsIn_basicOpen (ptP_mem_chart N c w) (ratio ℤ N c i)
  rw [ratio, basicOpen_ratioOn, CxPts.mem_ptsIn_inf] at e
  rw [← ratio, ev_ptP_ratio N c w hc i] at e
  constructor
  · intro h
    have := e.1 ⟨ptP_mem_chart N c w, h⟩
    exact fun h0 => this (by rw [h0, zero_div])
  · intro h
    exact (e.2 (div_ne_zero h hc)).2

theorem ptP_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0) :
    (∀ i, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0) ∧
    ∀ i j, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) →
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (GlobalTheory.CompanionTheory.MPSmooth.ptP N c w) =
        w j / w i := by
  refine ⟨ptP_mem_chart_iff N c w hc, fun i j hi => ?_⟩
  have hwi : w i ≠ 0 := (ptP_mem_chart_iff N c w hc i).1 hi
  have hW : ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i) :=
    CxPts.mem_ptsIn_inf.2 ⟨ptP_mem_chart N c w, hi⟩
  have h₁ : ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left i *
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j =
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left j :=
    ratioOn_mul_ratioOn
  have h₂ := congrArg (fun f => CxPts.ev (PSpace.str ℤ N) σ₀ _ f (ptP N c w)) h₁
  simp only [CxPts.ev_mul] at h₂
  have ea : ∀ k, CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left k) (ptP N c w) = w k / w c := fun k =>
    (CxPts.ev_res inf_le_left hW (ratio ℤ N c k)).trans (ev_ptP_ratio N c w hc k)
  have eb : CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j) (ptP N c w) =
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (ptP N c w) :=
    CxPts.ev_res inf_le_right hW (ratio ℤ N i j)
  rw [ea, ea, eb] at h₂
  field_simp at h₂ ⊢
  exact h₂

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionFiniteOpenCover
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchRep

theorem exists_local_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) (r : L.ι → X.functionFieldˣ) (y : GlobalTheory.CxPts q σ) :
    ∃ (W : X.Opens) (b : L.ι) (a d : Γ(X, W)) (h : genericPoint X ∈ W),
      y ∈ ptsIn q σ W ∧ W ≤ L.U b ∧ fnOf W h d ≠ 0 ∧
        (r b : X.functionField) * fnOf W h d = fnOf W h a := by
  have hb := mem_pick ψ.isLB y
  obtain ⟨W, hW, hyW, hWb⟩ := exists_isAffineOpen_mem_and_subset (mem_ptsIn.1 hb)
  have hg : genericPoint X ∈ W := gen_mem hyW
  haveI : Nonempty W := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  obtain ⟨a, d, hd, e⟩ := IsFractionRing.div_surjective (A := Γ(X, W)) (r (pick ψ.isLB y) : X.functionField)
  have hd0 : fnOf W hg d ≠ 0 := by
    have : algebraMap Γ(X, W) X.functionField d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    exact this
  refine ⟨W, pick ψ.isLB y, a, d, hg, mem_ptsIn.2 hyW, hWb, hd0, ?_⟩
  rw [← e]
  change algebraMap Γ(X, W) X.functionField a / algebraMap Γ(X, W) X.functionField d * fnOf W hg d = _
  have e' : algebraMap Γ(X, W) X.functionField d = fnOf W hg d := rfl
  have e'' : algebraMap Γ(X, W) X.functionField a = fnOf W hg a := rfl
  rw [e', e'', div_mul_cancel₀ _ hd0]

theorem logNorm_of_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {W : X.Opens} {b : L.ι} {a d : Γ(X, W)} {h : genericPoint X ∈ W} (hWb : W ≤ L.U b)
    (e : (r b : X.functionField) * fnOf W h d = fnOf W h a) {y : GlobalTheory.CxPts q σ} (hy : y ∈ ptsIn q σ W)
    (ho : y ∈ offSupp q σ (divOfRatSec ψ.isLB hr)) (hd : ev q σ W d y ≠ 0) :
    GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ W a y‖ - Real.log ‖ev q σ W d y‖ - ψ.φ b y / 2 := by
  have hb : y ∈ ptsIn q σ (L.U b) := mem_ptsIn.2 (hWb (mem_ptsIn.1 hy))
  have hu := IsRatSec.unitAt ψ.isLB hr ho hb
  have hv : ratVal (r b : X.functionField) y ≠ 0 := ratVal_ne_zero hu
  have ev' : ratVal (r b : X.functionField) y * ev q σ W d y = ev q σ W a y := by
    rw [← ratVal_fnOf hy h d, ← ratVal_mul hu.regAt (regAt_fnOf (mem_ptsIn.1 hy) h d), e, ratVal_fnOf hy]
  rw [logNorm_eq ψ hr ho hb, ← ev', norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 hv) (norm_ne_zero_iff.2 hd)]
  ring

theorem logNorm_finite_rep {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ∃ (N : ℕ) (W : Fin N → X.Opens) (b : Fin N → L.ι) (a d : ∀ l, Γ(X, W l)),
      (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) ∧ (∀ l, W l ≤ L.U (b l)) ∧
      (∀ l, ∃ h : genericPoint X ∈ W l, fnOf (W l) h (d l) ≠ 0) ∧
      ∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ offSupp q σ (divOfRatSec ψ.isLB hr) → ev q σ (W l) (d l) y ≠ 0 →
        GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2 := by
  choose W₀ b₀ a₀ d₀ h₀ hy₀ hWb₀ hd₀ e₀ using exists_local_quot ψ r
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => ptsIn q σ (W₀ y))
    (fun y => isOpen_ptsIn _) fun y _ => Set.mem_iUnion.2 ⟨y, hy₀ y⟩
  let c : Fin t.card → GlobalTheory.CxPts q σ := fun l => (t.equivFin.symm l).1
  refine ⟨t.card, fun l => W₀ (c l), fun l => b₀ (c l), fun l => a₀ (c l), fun l => d₀ (c l), fun y => ?_,
    fun l => hWb₀ _, fun l => ⟨h₀ _, hd₀ _⟩, fun l y hy ho hd => logNorm_of_quot ψ hr (hWb₀ _) (e₀ _) hy ho hd⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨z, hz⟩, ?_⟩
  simpa [c] using hyz

end GlobalTheory.CompanionTheory.MixZ.ArchRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

abbrev Over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)
    (z : (Σ k, Bk n k) → ℂ) : Prop :=
  IsUnder (PtsOver.map i rfl _ y) z

abbrev LinProj (n : Fin (m + 1) → ℕ) (D : ℕ) := (((k : Fin (m + 1)) → Bk n k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)

def ratios (Ψ : LinProj n D) (z : (Σ k, Bk n k) → ℂ) : Fin D → ℂ :=
  fun a => Ψ (segre z) a.succ / Ψ (segre z) 0


open Classical in
def liftOf {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : (Σ k, Bk n k) → ℂ :=
  if h : ∃ z, Over i y z then h.choose else 0

def projCoord {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    Fin D → ℂ :=
  ratios Ψ (liftOf i y)

def IsRegAt {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D)
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Prop :=
  LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0

def IsPiece {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n)
    (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
    (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) : Prop :=
  (∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, e.source ⊆ c.e.source) ∧ DifferentiableOn ℂ Γ e.target ∧
    ∀ v ∈ e.target, Over i (e.symm v) (Γ v) ∧ Γ v ∈ mcPts (ptIdeal (i (genericPoint X))) ∧
      Ψ (segre (Γ v)) = Fin.cons 1 v ∧ eval (Γ v) (map (Int.castRingHom ℂ) N) ≠ 0

def pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :=
  {y | ∃ e Γ, IsPiece i Ψ N e Γ ∧ y ∈ e.source}

theorem isOpen_pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    IsOpen (pieceSet i Ψ N) := isOpen_iff_forall_mem_open.mpr fun _ ⟨e, Γ, hp, hy⟩ =>
  ⟨e.source, fun _ hy' => ⟨e, Γ, hp, hy'⟩, e.open_source, hy⟩

theorem segre_orbit {z z' : (Σ k, Bk n k) → ℂ} {c : Fin (m + 1) → ℂ} (h : z = fun p => c p.1 * z' p) :
    segre z = (∏ k, c k) • segre z' := by
  subst h
  funext a
  simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, Finset.prod_mul_distrib]

theorem ratios_eq_of_sameOrbit (Ψ : LinProj n D) {z z' : (Σ k, Bk n k) → ℂ} (h : SameOrbit z z')
    (h0 : Ψ (segre z') 0 ≠ 0) : ratios Ψ z = ratios Ψ z' := by
  obtain ⟨c, hc, rfl⟩ := h
  have hprod : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext a
  simp only [ratios, segre_orbit (c := c) rfl, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hprod

theorem ratios_of_proj (Ψ : LinProj n D) {z : (Σ k, Bk n k) → ℂ} {v : Fin D → ℂ}
    (h : Ψ (segre z) = Fin.cons 1 v) : ratios Ψ z = v := by
  funext a
  simp [ratios, h]

theorem homog_mul {f g : Pol n} {a b : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro d hd k
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hd)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf x hx k, hg y hy k, Pi.add_apply]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPoint
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.FnForm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem evaluation_resG_apply {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    (X.evaluation V x hx).hom (resG X h s) = (X.evaluation U x (h hx)).hom s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

def chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (mchart c) x hx).hom
    (resG _ (mchart_le c p.1) (pullRatio (prB n p.1) _ (c p.1) le_rfl p.2))

theorem ptCoord_eq_mul_chartCoord (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (p : Σ k, Bk n k) :
    ptCoord x p = ptCoord x ⟨p.1, c p.1⟩ * chartCoord c x hx p := by
  obtain ⟨k, j⟩ := p
  let P : MP ℤ m n ⟶ PSpace ℤ (n k) := prB n k
  let W₀ : (MP ℤ m n).Opens := blockChart n k (ptChart x k)
  let W₁ : (MP ℤ m n).Opens := blockChart n k (c k)
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := le_rfl
  have hx₀ : x ∈ W₀ := mem_ptChart x k
  have hx₁ : x ∈ W₁ := mchart_le c k hx
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) (c k) := inf_le_right.trans h₁
  have e₀ : ∀ l : Bk n k, ptCoord x ⟨k, l⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (ptChart x k) hV₀ l) := by
    intro l
    show ((MP ℤ m n).evaluation W₀ x hx₀).hom (pullRatio P W₀ (ptChart x k) h₀ l) = _
    rw [← evaluation_resG_apply (inf_le_left : V ≤ W₀) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₀) inf_le_left)
  have e₁ : chartCoord c x hx ⟨k, j⟩ =
      ((MP ℤ m n).evaluation V x hxV).hom (pullRatio P V (c k) hV₁ j) := by
    show ((MP ℤ m n).evaluation (mchart c) x hx).hom (resG _ (mchart_le c k) (pullRatio P W₁ (c k) h₁ j)) = _
    rw [evaluation_resG_apply, ← evaluation_resG_apply (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  show ptCoord x ⟨k, j⟩ = ptCoord x ⟨k, c k⟩ * chartCoord c x hx ⟨k, j⟩
  rw [e₀ j, e₀ (c k), e₁, ← map_mul]
  exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := j)).symm

theorem evaluation_dehomog (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) (f : Pol n) :
    ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) = aeval (chartCoord c x hx) f := by
  have e : ((MP ℤ m n).evaluation (mchart c) x hx).hom.comp (dehomog c) =
      (aeval (chartCoord c x hx) : Pol n →ₐ[ℤ] _).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp [dehomog, chartCoord])
  exact congrArg (fun φ => φ f) e

theorem aeval_ptCoord_eq_mul (c : ∀ k, Bk n k) (x : MP ℤ m n) (hx : x ∈ mchart c) {f : Pol n}
    {a : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) :
    aeval (ptCoord x) f = (∏ k, ptCoord x ⟨k, c k⟩ ^ a k) *
      ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c f) := by
  rw [evaluation_dehomog, ← GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.aeval_smul hf]
  exact congrArg (fun v => aeval v f) (funext (ptCoord_eq_mul_chartCoord c x hx))

theorem fnAt_ne_zero_of_notMem_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (c : ∀ k, Bk n k) (h : genericPoint X ∈ i ⁻¹ᵁ mchart c) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    f ∉ ptIdeal (i (genericPoint X)) → fnAt i c h f ≠ 0 := by
  intro m n X _ i _ c h f a hf hnot h0
  refine hnot ((mem_ptIdeal_iff_aeval_ptCoord m n _ f a hf).2 ?_)
  have hx : i (genericPoint X) ∈ mchart c := h
  have h1 : i.app (mchart c) (dehomog c f) = 0 :=
    fnOf_injective _ h (h0.trans (map_zero _).symm)
  have h2 : ((MP ℤ m n).evaluation (mchart c) _ hx).hom (dehomog c f) = 0 := by
    apply (i.residueFieldMap (genericPoint X)).hom.injective
    rw [map_zero]
    refine (Scheme.evaluation_naturality_apply i (genericPoint X) hx _).trans ?_
    rw [h1, map_zero]
  rw [aeval_ptCoord_eq_mul c _ hx hf, h2, mul_zero]

end GlobalTheory.CompanionTheory.MixZ.FnForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhatStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_function_schwartz_bruhat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (φ : Mx D m r → ℂ), φ ∈ schwartzA θ m r →
  GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (fun X : Fin r → Fin m → AE D => φ (tupOf X)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA | exact GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA | (intros; apply GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOneStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.socle_of_multiplicity_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | exact GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one | (intros; apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalInfimum
section
open GlobalTheory.CompanionTheory.EGlue

noncomputable section

open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.EGlue.Gl0

theorem topInf : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  intro E _ _ _ τ
  refine ⟨rfl, fun u φ _ => ?_⟩
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

end GlobalTheory.CompanionTheory.EGlue.Gl0

end
end

