module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BdryIsAnalyticSubsetInteriorEmpty
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem bdry_isAnalyticSubset_interior_empty : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsSection A L s → IsSNC A L s m W → A.IsAnalyticSubset (bdry s) ∧ interior (bdry s) = ∅ := by
  intro e X _ A L s n m W hS hSNC
  refine ⟨?_, LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC⟩
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzU⟩
    exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
  · rintro ⟨hzU, hz⟩
    exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagFrameAtGoodPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_diag_frame_at_good_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (w : (Σ k, ι k) → ℂ) (H : Ψ → Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → basePart M.blk w ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk w)) → (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) → (∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, w ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk w) p.2 ⟨k, m⟩ (H p.1)) → w ∈ mcPts (mCoordIdeal y) ∧ ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk w) ∧ M.IsFlagOf F z₀ H := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F w H hF hb hG hH hP
  have hne (k : NonPluckerBlocks M.blk) : w ⟨k.1, F.c k⟩ ≠ 0 := by
    intro hw
    apply hG.1 k
    show mConeMap (basePart M.blk w) (X ⟨k, F.c k⟩) = 0
    have hw' : basePart M.blk w ⟨k, F.c k⟩ = 0 := hw
    rw [mConeMap, aeval_X, hw', map_zero, zero_mul]
  let c (k : K) : ℂ := if hk : ∀ p, M.blk p ≠ some k then (w ⟨k, F.c ⟨k, hk⟩⟩)⁻¹ else 1
  have hc (k : K) : c k ≠ 0 := by
    by_cases hk : ∀ p, M.blk p ≠ some k
    · simpa only [c, dite_eq_left hk] using inv_ne_zero (hne ⟨k, hk⟩)
    · simpa only [c, dite_eq_right hk] using (one_ne_zero : (1 : ℂ) ≠ 0)
  let z₀ (q : Σ k, ι k) : ℂ := c q.1 * w q
  let c' (k : NonPluckerBlocks M.blk) : ℂ := c k.1
  have hc' (k : NonPluckerBlocks M.blk) : c' k ≠ 0 := hc k.1
  have eb : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k => c' q.1 * basePart M.blk w q := rfl
  obtain ⟨hI, hm⟩ := StepW.TorusAct.main _ _ M.Ω M.x (basePart M.blk w) c' hc'
  obtain ⟨hb₀, hval⟩ := hm hb
  rw [← eb] at hI hb₀ hval
  have hflag : M.IsFlagOf F z₀ H := by
    refine ⟨fun k => ?_, hH, fun p k hp => ?_⟩
    · show c k.1 * w ⟨k.1, F.c k⟩ = 1
      simp only [c, dite_eq_left k.2]
      exact inv_mul_cancel₀ (hne k)
    · obtain ⟨a, ha, hw⟩ := hP p k hp
      refine ⟨a, ha, fun m => ?_⟩
      have hk : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
      show c k * w ⟨k, m⟩ = _
      simp only [c, dite_eq_right hk, one_mul]
      rw [hw m, CovMap.LocImg.plk]
      simp only [hval]
  have hG₀ : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by
    rw [hI]
    exact hG
  have hz₀ : z₀ ∈ mcPts (mCoordIdeal y) :=
    ((_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M).2.2 F hF z₀ hb₀ hG₀ hflag.1).mpr
      ⟨H, hflag⟩
  have ho' : SameOrbit w z₀ := ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), by
    funext q
    exact (inv_mul_cancel_left₀ (hc q.1) _).symm⟩
  exact ⟨mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ho' hz₀,
    z₀, ⟨c, hc, rfl⟩, ⟨c', hc', rfl⟩, hflag⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CauchyBinetSumPositionedMinors
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

theorem bExt_posOf (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (s : Ψ ⊕ Ψ)
    (l : Fin (rk Ψ p q s)) (j : Fin (n s)) : bExt B s (posOf p q s l) j = B s l j := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  unfold bExt
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_posOf (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ)
    (j : Fin (n s)) (l : Fin (rk Ψ p q s)) : aExt C s j (posOf p q s l) = C s j l := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  unfold aExt
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb (hinj h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_of_forall_ne (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ)
    (j : Fin (n s)) {b : Fin (p + q)} (h : ∀ l, posOf p q s l ≠ b) : aExt C s j b = 0 :=
  Finset.sum_eq_zero fun l _ => if_neg (h l)

theorem bExt_mul_aExt_row (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (hBC : ∀ s, B s * C s = 1) (s : Ψ ⊕ Ψ)
    (l : Fin (rk Ψ p q s)) (b : Fin (p + q)) :
    (bExt B s * aExt C s) (posOf p q s l) b = (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω) (posOf p q s l) b := by
  have hinj := (BlockEmbeddings.posOf_strictMono (Ψ := Ψ) (p := p) (q := q) s).injective
  rw [Matrix.mul_apply]
  simp only [bExt_posOf]
  by_cases hb : ∃ l', posOf p q s l' = b
  · obtain ⟨l', rfl⟩ := hb
    simp only [aExt_posOf]
    have h := congrFun (congrFun (hBC s) l) l'
    rw [Matrix.mul_apply] at h
    rw [h]
    by_cases e : l = l'
    · subst e
      simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne fun h' => e (hinj h')]
  · have hb' : ∀ l', posOf p q s l' ≠ b := fun l' h' => hb ⟨l', h'⟩
    simp only [aExt_of_forall_ne C s _ hb', mul_zero, Finset.sum_const_zero]
    rw [Matrix.one_apply_ne (hb' l)]

theorem sum_strictMono_eq {M : Type} [AddCommMonoid M] {d m : ℕ} (f : (Fin d → Fin m) → M)
    (hf : ∀ J, ¬ StrictMono J → f J = 0) :
    ∑ J, f J = ∑ s : GroundTheory.PAdicHodge.KSubset m d, f s.emb := by
  classical
  symm
  refine Fintype.sum_of_injective (fun s : GroundTheory.PAdicHodge.KSubset m d => (s.emb : Fin d → Fin m))
    ?_ _ _ ?_ fun _ => rfl
  · intro s s' h
    have h' : Set.range s.emb = Set.range s'.emb := congrArg Set.range h
    rw [GroundTheory.PAdicHodge.KSubset.range_emb, GroundTheory.PAdicHodge.KSubset.range_emb] at h'
    exact Subtype.ext (Finset.coe_injective h')
  · intro J hJ
    refine hf J fun hm => hJ ?_
    have hc : (Finset.univ.image J).card = d := by
      rw [Finset.card_image_of_injective _ hm.injective]
      simp
    refine ⟨⟨Finset.univ.image J, hc⟩, ?_⟩
    exact (Finset.orderEmbOfFin_unique hc (fun x => by simp) hm).symm

theorem sum_sMin_mul_cMin : ∀ {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω)
    (hBC : ∀ s, B s * C s = 1) (t : StepIx Ψ p q) (I I' : Finset (Fin (p + q)))
    (hI : I.card = (t.2 : ℕ) + 1) (hI' : I'.card = (t.2 : ℕ) + 1)
    (hp : ∀ a ∈ I, ∃ l, posOf p q t.1 l = a) (hp' : ∀ a ∈ I', ∃ l, posOf p q t.1 l = a),
    ∑ J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1), sMin B t I J * cMin C t J I' = if I = I' then 1 else 0 := by
  intro Ψ p q Ω _ n C B hBC t I I' hI hI' hp _
  classical
  rw [sum_strictMono_eq (fun J => sMin B t I J * cMin C t J I') (fun J hJ => by
    simp only [sMin, if_neg hJ, zero_mul])]
  have hterm : ∀ s : GroundTheory.PAdicHodge.KSubset (n t.1) ((t.2 : ℕ) + 1),
      sMin B t I s.emb * cMin C t s.emb I' =
        (((bExt B t.1).submatrix (I.orderEmbOfFin hI) id).submatrix id s.emb).det *
          (((aExt C t.1).submatrix id (I'.orderEmbOfFin hI')).submatrix s.emb id).det := by
    intro s
    simp only [sMin, if_pos s.emb.strictMono, bMin, cMin, dif_pos hI, dif_pos hI']
    rfl
  simp only [hterm]
  rw [← GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  have hmat : (bExt B t.1).submatrix (I.orderEmbOfFin hI) id * (aExt C t.1).submatrix id (I'.orderEmbOfFin hI') =
      (1 : Matrix (Fin (p + q)) (Fin (p + q)) Ω).submatrix (I.orderEmbOfFin hI) (I'.orderEmbOfFin hI') := by
    ext x y
    obtain ⟨l, hl⟩ := hp _ (Finset.orderEmbOfFin_mem I hI x)
    have h := bExt_mul_aExt_row C B hBC t.1 l (I'.orderEmbOfFin hI' y)
    rw [hl] at h
    simpa [Matrix.mul_apply] using h
  rw [hmat]
  by_cases e : I = I'
  · subst e
    rw [if_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin hI).injective, Matrix.det_one]
  · rw [if_neg e]
    have hns : ¬ I ⊆ I' := fun hs => e (Finset.eq_of_subset_of_card_le hs (by omega))
    obtain ⟨a, ha, ha'⟩ := Finset.not_subset.1 hns
    have hr : a ∈ Set.range (I.orderEmbOfFin hI) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨x, rfl⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero x fun y => ?_
    rw [Matrix.submatrix_apply]
    refine Matrix.one_apply_ne fun h => ha' ?_
    rw [h]
    exact Finset.orderEmbOfFin_mem _ _ _

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.Inv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open ReciprocityTheory.AnForm.R

def chPrime {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (g : MvPolynomial (Fin m) ℂ) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  (Ideal.span {algebraMap _ (locRing I t) g}).comap (algebraMap _ (locRing I t))

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartWSaturatedAndContinuousSection
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.NoMonodromy

variable {a g : ℕ}

theorem map_mulVec_real (M : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    M.map (fun x : ℤ => (x : ℝ)) *ᵥ (fun k => (v k : ℝ)) = fun k => ((M *ᵥ v) k : ℝ) := by
  funext k
  simp [mulVec, dotProduct]

theorem ker_each (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ)
    (hv : (∑ j, B j) *ᵥ v = 0) (j : Fin a) : B j *ᵥ v = 0 := by
  set r : Fin g → ℝ := fun k => (v k : ℝ) with hr
  have hsum : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have h1 : (∑ j, (B j).map (fun x : ℤ => (x : ℝ))) *ᵥ r = 0 := by
    rw [← hsum, hr, map_mulVec_real, hv]
    funext k
    simp
  have h0 : r ⬝ᵥ ((∑ j, (B j).map (fun x : ℤ => (x : ℝ))) *ᵥ r) = 0 := by
    rw [h1]; simp
  rw [Matrix.sum_mulVec, dotProduct_sum] at h0
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ r ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ r) := by
    intro i _
    simpa using (hB i).dotProduct_mulVec_nonneg r
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
  have h3 : (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ r = 0 :=
    ((hB j).dotProduct_mulVec_zero_iff).1 (by simpa using h2)
  rw [hr, map_mulVec_real] at h3
  funext k
  have := congrFun h3 k
  simpa using this

theorem vec_eq_sum (t : Fin g → ℂ) : t = ∑ i, t i • cst (Pi.single i 1 : Fin g → ℤ) := by
  funext k
  simp [cst, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.NoMonodromy

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NoMonodromy

theorem noMonodromy_lattice : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (k : ℤ), k ≠ 0 → k • x ∈ chartW bas B → x ∈ chartW bas B) ∧ (∀ x ∈ chartW bas B, ContinuousAt (chartS bas A T0 x) 0 ∧ ∀ w ∈ logCover L.a_le, chartS bas A T0 x (expCover a w) = L.P w x) ∧ Function.Injective (chartPer bas A T0 B) ∧ Submodule.span ℂ (Set.range (chartPer bas A T0 B)) = ⊤ := by
  intro n a g Λ _ L bas A T0 B c ρ h
  have hmem : ∀ x, x ∈ chartW bas B ↔ (∑ j, B j) *ᵥ vCo bas x = 0 := fun x => by
    rw [chartW, LinearMap.mem_ker]
    rfl
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hA0 : ContinuousAt A 0 := h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hT0 : ContinuousAt T0 0 := h.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hunit : IsUnit ((A 0)ᵀ).det := Ne.isUnit (by rw [det_transpose]; exact h.A_det)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x k hk hx
    rw [hmem] at hx ⊢
    rw [map_zsmul, Matrix.mulVec_smul] at hx
    exact (smul_eq_zero.1 hx).resolve_left hk
  · intro x hx
    have hxv := (hmem x).1 hx
    refine ⟨?_, fun w hw => ?_⟩
    · have hcts : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
          p.1ᵀ *ᵥ (cst (uCo bas x) + p.2 *ᵥ cst (vCo bas x))) :=
        (continuous_fst.matrix_transpose).matrix_mulVec
          (continuous_const.add (continuous_snd.matrix_mulVec continuous_const))
      exact ContinuousAt.comp (f := fun z => (A z, T0 z)) hcts.continuousAt (hA0.prodMk hT0)
    · rw [h.per w hw x]
      simp only [chartS, tauAt]
      have hz : (∑ j, (w (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
          (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ cst (vCo bas x) = 0 := by
        rw [Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Matrix.smul_mulVec, cst_mulVec, ker_each B h.B_psd _ hxv j, cst_zero, smul_zero]
      rw [Matrix.add_mulVec, hz, add_zero]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hxv := (hmem _).1 x.2
    set u := uCo bas (x : Λ) with hu
    set v := vCo bas (x : Λ) with hv
    have hS : (A 0)ᵀ *ᵥ (cst u + T0 0 *ᵥ cst v) = 0 := hx
    have hy : cst u + T0 0 *ᵥ cst v = 0 := by
      have := congrArg (fun y => ((A 0)ᵀ)⁻¹ *ᵥ y) hS
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit] using this
    set r : Fin g → ℝ := fun k => (v k : ℝ) with hr
    have him : ((T0 0).map Complex.im) *ᵥ r = 0 := by
      funext i
      have h1 := congrArg Complex.im (congrFun hy i)
      simpa [cst, mulVec, dotProduct, hr] using h1
    have hlow := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
      Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball h.ρ_le)) h.B_psd h.c_pos h.im_lower 0
      (Metric.mem_ball_self h.ρ_pos) 0 (fun j hj => absurd rfl hj) (fun _ _ => rfl) r
      (fun j _ => by
        rw [hr, map_mulVec_real, ker_each B h.B_psd _ hxv j]
        funext k
        simp)
    simp only [Pi.zero_apply, zero_div, zero_smul, Finset.sum_const_zero, add_zero] at hlow
    rw [him, dotProduct_zero] at hlow
    have hrr : r ⬝ᵥ r ≤ 0 := by
      by_contra hcon
      exact absurd hlow (not_le.2 (mul_pos h.c_pos (not_le.1 hcon)))
    have hr0 : r = 0 := by
      refine dotProduct_self_eq_zero.1 (le_antisymm hrr ?_)
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hv0 : v = 0 := by
      funext k
      have := congrFun hr0 k
      simpa [hr] using this
    have hu0 : u = 0 := by
      rw [hv0, cst_zero, mulVec_zero, add_zero] at hy
      funext k
      have := congrFun hy k
      simpa [cst] using this
    refine Subtype.ext (eq_of_coords bas ?_ ?_)
    · rw [← hu, hu0]; simp
    · rw [← hv, hv0]; simp
  · rw [eq_top_iff]
    intro y _
    set t : Fin g → ℂ := ((A 0)ᵀ)⁻¹ *ᵥ y with ht
    have hyt : y = (A 0)ᵀ *ᵥ t := by
      rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    have hper : ∀ i, (A 0)ᵀ *ᵥ cst (Pi.single i 1 : Fin g → ℤ) ∈
        Submodule.span ℂ (Set.range (chartPer bas A T0 B)) := by
      intro i
      refine Submodule.subset_span ⟨⟨mk bas (Pi.single i 1) 0, ?_⟩, ?_⟩
      · rw [hmem, vCo_mk]; simp
      · change chartS bas A T0 (mk bas (Pi.single i 1) 0) 0 = _
        simp only [chartS, uCo_mk, vCo_mk, cst_zero, mulVec_zero, add_zero]
    rw [hyt, vec_eq_sum t, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (hper i)

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsComponentInChartRegular
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

open GlobalTheory.CompanionTheory.Ar.TiePrimes (dh mem_coord_iff homog_X eval₂_eq_dh_mul exists_form aeval_eq_dh_mul adjoin_eq
  mem_Wp_iff regAt_iff)

theorem exists_point_of_prime : ∀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (tie : CoordTie ℤ ξ (seg y)) (Q : Ideal (MRing J))
    (hQ : Q.IsPrime) (hle : mCoordIdeal y ≤ Q) (c : ∀ k, J k)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ Q),
    ∃ P : Cpt ξ, InChart ξ (seg y) c P ∧ ∀ a ∈ regAt ξ P, RegAt y Q a := by
  intro Sc Ω _ ξ K _ J _ y tie W hWp hPW c hcX
  classical
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 =>
    hcX k (hPW ((mem_coord_iff y (homog_X _)).2 (by simpa using h0)))
  have hx : seg y c ≠ 0 := GlobalTheory.CompanionTheory.Ar.TiePrimes.seg_ne hc
  haveI : IsDomain (MRing J ⧸ W) := Ideal.Quotient.isDomain W
  let F := FractionRing (MRing J ⧸ W)
  let y' : (Σ k, J k) → F := fun q => algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W (MvPolynomial.X q))
  have ae : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f =
      algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W f) := by
    intro f
    have e : MvPolynomial.eval₂Hom (Int.castRingHom F) y' =
        (algebraMap (MRing J ⧸ W) F).comp (Ideal.Quotient.mk W) :=
      MvPolynomial.ringHom_ext (fun a => by simp) (fun q => by simp [y'])
    exact RingHom.congr_fun e f
  have hzero : ∀ f : MRing J, MvPolynomial.eval₂ (Int.castRingHom F) y' f = 0 ↔ f ∈ W := by
    intro f
    rw [ae, map_eq_zero_iff _ (IsFractionRing.injective (MRing J ⧸ W) F), Ideal.Quotient.eq_zero_iff_mem]
  have hc' : ∀ k, y' ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k ((hzero _).1 (by simpa using h0))
  have memW : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → (g ∈ W ↔ dh y' c g = 0) := by
    intro g d hg
    have h0 : (∏ k, y' ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
    rw [← hzero, eval₂_eq_dh_mul y' c hc' hg, mul_eq_zero, or_iff_left h0]
  let A := Algebra.adjoin ℤ (Set.range fun j => seg y j / seg y c)
  have hdhA : ∀ f, dh y c f ∈ A := fun f => by
    show dh y c f ∈ Algebra.adjoin ℤ _
    rw [adjoin_eq hc]
    exact ⟨f, rfl⟩
  let φ : MRing J →+* A := ((dh y c).codRestrict A hdhA : MRing J →ₐ[ℤ] A).toRingHom
  have hφ : ∀ f, ((φ f : A) : Ω) = dh y c f := fun f => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ (dh y c).range := by
      rw [← adjoin_eq hc]
      exact ha
    obtain ⟨f, rfl⟩ := ha'
    exact ⟨f, Subtype.ext rfl⟩
  let Q : Ideal (MRing J) := RingHom.ker (dh y' c : MRing J →+* F)
  haveI hQ : Q.IsPrime := RingHom.ker_isPrime _
  have hker : RingHom.ker φ ≤ Q := by
    intro f hf
    have hf0 : dh y c f = 0 := by
      rw [← hφ, RingHom.mem_ker.1 hf]
      rfl
    obtain ⟨D, G, hG, e⟩ := exists_form c f
    have e₁ : dh y c G = dh y c f := e Ω _ fun k => div_self (hc k)
    have e₂ : dh y' c G = dh y' c f := e F _ fun k => div_self (hc' k)
    have hGP : G ∈ W := hPW ((mem_coord_iff y hG).2 (by
      rw [aeval_eq_dh_mul y c hc hG, e₁, hf0, zero_mul]))
    show dh y' c f = 0
    rw [← e₂]
    exact (memW G D hG).1 hGP
  let I : Ideal A := Q.map φ
  have hI : I.IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  obtain ⟨p, ⟨hin, hunit⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.chart_point_of_prime Sc Ω ξ ℤ _ (seg y) tie c hx I hI
  have hI' : ∀ g : MRing J, φ g ∈ I ↔ g ∈ Q := by
    intro g
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem φ⟩
    obtain ⟨x, hx', e⟩ := (Ideal.mem_map_iff_of_surjective φ hsurj).1 h
    have : g - x ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    have h2 := Q.add_mem (hker this) hx'
    simpa using h2
  have key : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d →
      (g ∈ GlobalTheory.CompanionTheory.Ar.TiePrimes.Wp tie p ↔ g ∈ W) := by
    intro g d hg
    rw [mem_Wp_iff tie hin hg, memW g d hg, ← hφ, ← hunit (φ g), not_not, hI' g]
    rfl
  refine ⟨p, hin, fun a ha => ?_⟩
  obtain ⟨d, g, h, hg, hh, hW, e⟩ := (regAt_iff tie p a).1 ha
  exact ⟨d, g, h, hg, hh, fun hm => hW ((key h d hh).2 hm), e⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

