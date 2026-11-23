module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0110
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.MultihomogeneousSquares.BlockDiagMinorNeZero
section
noncomputable section

namespace SquareStatements.Sing

open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB
  GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

section Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ}

theorem mem_regRing_of_regAt (hw : w ∈ mcPts (mCoordIdeal x)) {s : Ω} (hs : RegAt x (mCoordIdeal w) s) :
    s ∈ regRing x w := by
  exact ValRing.exists_isValueAt hw hs

theorem valAt_one_multihomogeneous_squares (hw : w ∈ mcPts (mCoordIdeal x)) : valAt x (1 : Ω) w = 1 := (regVal hw).map_one

theorem valAt_zero_multihomogeneous_squares (hw : w ∈ mcPts (mCoordIdeal x)) : valAt x (0 : Ω) w = 0 := (regVal hw).map_zero

theorem valAt_sum_mul' (hw : w ∈ mcPts (mCoordIdeal x)) {σ : Type} (S : Finset σ) (a b : σ → Ω)
    (ha : ∀ m, a m ∈ regRing x w) (hb : ∀ m, b m ∈ regRing x w) :
    valAt x (∑ m ∈ S, a m * b m) w = ∑ m ∈ S, valAt x (a m) w * valAt x (b m) w := by
  have e : (∑ m ∈ S, a m * b m) =
      ((∑ m ∈ S, (⟨a m, ha m⟩ : regRing x w) * ⟨b m, hb m⟩ : regRing x w) : Ω) := by
    push_cast; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← regVal_apply hw, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, regVal_apply, regVal_apply]

end Val

theorem block_diag_minor_ne_zero {N j : ℕ} (hj : j ≤ N) (i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (hb : IsBlockDiag j h)
    (hd : h.det ≠ 0) : ∃ I, IsStepRows N j i I ∧ minorIJ h I (stepCols N j i) ≠ 0 := by
  classical
  set J := stepCols N j i with hJ
  set k := J.card with hk
  let e := J.orderEmbOfFin (rfl : J.card = k)
  let A : Matrix (Fin N) (Fin k) ℂ := fun r c => h r (e c)
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (isUnit_iff_ne_zero.2 hd)
  have hcol : LinearIndependent ℂ A.col :=
    (Matrix.linearIndependent_cols_iff_isUnit.2 hu).comp e e.injective
  have hrank : A.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hcol, Fintype.card_fin]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ A.row
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← hrank, Matrix.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  let I : Finset (Fin N) := Finset.univ.image a
  have hI : I.card = k := by
    rw [Finset.card_image_of_injective _ ha, Finset.card_univ, hcard]
  have hmemI : ∀ t : Fin k, ∃ c : κ, a c = I.orderEmbOfFin hI t := by
    intro t
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 (Finset.orderEmbOfFin_mem I hI t)
    exact ⟨c, hc⟩
  choose f hf using hmemI
  have hfinj : Function.Injective f := by
    intro s t hst
    have : I.orderEmbOfFin hI s = I.orderEmbOfFin hI t := by rw [← hf s, ← hf t, hst]
    exact (I.orderEmbOfFin hI).injective this
  have hrows : LinearIndependent ℂ (h.submatrix (I.orderEmbOfFin hI) e).row := by
    have h2 := hli.comp f hfinj
    have heq : (h.submatrix (I.orderEmbOfFin hI) e).row = (A.row ∘ a) ∘ f := by
      funext t c
      simp [Matrix.row, A, hf]
    rw [heq]
    exact h2
  refine ⟨I, ⟨hI, ?_⟩, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    have hne : A.row (a c) ≠ 0 := by
      have := hli.ne_zero c
      simpa using this
    by_contra hnot
    apply hne
    funext t
    simp only [Matrix.row, A, Pi.zero_apply]
    apply hb
    have hc := MinorCalc.mem_stepCols_block (i := i) (c := e t) hj (Finset.orderEmbOfFin_mem J _ t)
    split_ifs at hc hnot with hij
    · simp [wIdx] at hnot
      intro hiff
      have h3 : (a c : ℕ) < N - j := by omega
      exact absurd (hiff.1 h3) (by omega)
    · simp [omIdx] at hnot
      intro hiff
      exact absurd (hiff.2 hc) (by omega)
  · rw [MinorCalc.minorIJ_eq_det h I J k hI rfl]
    have := Matrix.linearIndependent_rows_iff_isUnit.1 hrows
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

theorem c5 : C5 := by
  intro K _ ι _ Φ _ y Ψ N j M wb F h p k hw hF hG hb hd hk
  classical
  obtain ⟨I0, hI0, hne⟩ := block_diag_minor_ne_zero M.j_le p.2 h hb hd
  set J := stepCols N j p.2 with hJ
  by_contra hall
  push_neg at hall
  have hreg : ∀ (q : (k : K) × ι k) (I : Finset (Fin N)),
      F.u q I ∈ regRing M.x wb ∧ F.u' I q ∈ regRing M.x wb :=
    fun q I => ⟨mem_regRing_of_regAt hw (hG.2.1 q I).1, mem_regRing_of_regAt hw (hG.2.1 q I).2⟩
  have key : ∀ I : Finset (Fin N), IsStepRows N j p.2 I →
      ∑ m : ι k, valAt M.x (F.u' I0 ⟨k, m⟩) wb * valAt M.x (F.u ⟨k, m⟩ I) wb =
        if I0 = I then 1 else 0 := by
    intro I hI
    rw [← valAt_sum_mul' hw Finset.univ (fun m => F.u' I0 ⟨k, m⟩) (fun m => F.u ⟨k, m⟩ I)
      (fun m => (hreg _ _).2) (fun m => (hreg _ _).1)]
    rw [hF.2.2.1 p k hk I0 I hI0 hI]
    split_ifs
    · exact valAt_one_multihomogeneous_squares hw
    · exact valAt_zero_multihomogeneous_squares hw
  have hterm : ∀ I : Finset (Fin N),
      ∑ m : ι k, valAt M.x (F.u' I0 ⟨k, m⟩) wb * (valAt M.x (F.u ⟨k, m⟩ I) wb * minorIJ h I J) =
        if I0 = I then minorIJ h I J else 0 := by
    intro I
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    by_cases hI : IsStepRows N j p.2 I
    · rw [key I hI]
      split_ifs <;> simp
    · rw [MinorCalc.minor_stepCols_eq_zero M.j_le h I hb hI]
      split_ifs with e
      · subst e
        exact absurd hI0 hI
      · simp
  have hsum : ∑ m : ι k, valAt M.x (F.u' I0 ⟨k, m⟩) wb *
      ∑ I : Finset (Fin N), valAt M.x (F.u ⟨k, m⟩ I) wb * minorIJ h I J = minorIJ h I0 J := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hterm]
    simp
  apply hne
  rw [← hsum]
  simp [hall]

end SquareStatements.Sing
end
end

-- bundled from Development.WeilBound.CoreStatements.MultihomogeneousSquares.IsValueAtValAtOfRegAt
section
noncomputable section

namespace SquareStatements.Sing

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree (valAt IsValueAt)

theorem isValueAt_valAt_of_regAt {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    {x : (Σ k, J k) → Ω} {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal w) s) : IsValueAt x s w (valAt x s w) := by
  obtain ⟨d, g, h, hg, hh, hQ, hgh⟩ := hs
  have hwh : (MvPolynomial.eval w) ((MvPolynomial.map (Int.castRingHom ℂ)) h) ≠ 0 := by
    intro h0
    apply hQ
    apply GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero w hh
    rw [MvPolynomial.eval_map] at h0
    simpa [MvPolynomial.aeval_def] using h0
  have hxh : (MvPolynomial.aeval x) h ≠ 0 := by
    intro h0
    exact hwh (hw.2 h (GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero x hh h0))
  have hex : ∃ v, IsValueAt x s w v := ⟨_, d, g, h, hg, hh, hxh, hgh, hwh, rfl⟩
  unfold GroundTheory.Heights₂.Heights.LowerBoundFree.valAt
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem c0 : C0 := by
  intro E _ _ _ H D l Xo c Y S K _ ι _ Φ _ y M 𝔐 𝔐' pr j z w hO hw
  obtain ⟨hd, hf, -, -, -⟩ := hO
  obtain ⟨-, -, hval⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Chg.Stalk.regular_along_dominant 𝔐'.X 𝔐.X Φ M.Ω 𝔐'.ξ 𝔐.ξ pr (algebraMap M.Ω Φ) hd 𝔐'.tie.gen
  have hval' : ∀ (a : M.Ω) (r : ℂ), ValAt 𝔐.ξ (z ≫ pr) a r → ValAt 𝔐'.ξ z (algebraMap M.Ω Φ a) r :=
    fun a r => hval z a r (𝔐'.all _)
  have hco : CoordsAt 𝔐.ξ M.x (z ≫ pr) (basePart M.blk w) :=
    _root_.GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV 𝔐'.X 𝔐.X Φ M.Ω 𝔐'.ξ 𝔐.ξ pr (algebraMap M.Ω Φ) (NonPluckerBlocks M.blk) K (baseIdx ι M.blk) ι M.x y
      Subtype.val (fun _ => Equiv.refl _) hd 𝔐.tie 𝔐'.all (fun k a => M.y_base ⟨k, a⟩)
      (fun z' a r h' => hval z' a r (𝔐'.all _) h') z w hw
  refine ⟨hco, GlobalTheory.CompanionTheory.Ar.Chg.mem_abLocus_iff 𝔐 𝔐' pr hf (centre z), hval', fun s hs => hval' _ _ ?_⟩
  have hm : basePart M.blk w ∈ mcPts (mCoordIdeal M.x) :=
    (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie _).2 ⟨z ≫ pr, 𝔐.all _, hco⟩
  exact (_root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords 𝔐.X M.Ω 𝔐.ξ (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.x 𝔐.tie (z ≫ pr) _ (𝔐.all _) hco s _).2
    (isValueAt_valAt_of_regAt hm hs)

end SquareStatements.Sing
end
end

