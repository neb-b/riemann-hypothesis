module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMoriwakiBigCurve
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CoordFibreDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def CoordFibreDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (d : ℕ) (G : GenFibre v (mCoordIdeal y))
    (i : ∀ k : FibreBlock κ, fibreIdx ι' κ k),
    IsBlockMap κ v → IsArithVar (mCoordIdeal y) d → IsArithVar (imageZ v (mCoordIdeal y)) d →
    IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) i →
    ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal κ G) i = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LelongChartLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def LelongChartLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s →
    IsDegZeroSmooth g → 0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    Tendsto (fun ε : ℝ =>
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L)) g)
      (𝓝[>] 0)
      (𝓝 (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LelongSectionLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def LelongSectionLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    Tendsto (fun ε : ℝ =>
        ptsIntegral P
          (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
            (pot L))
          (fun z => Real.log (B.h z)))
      (𝓝[>] 0)
      (𝓝 (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiBig
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem MoriwakiBig.of_found (hG6 : HilbertSamuel.ArithmeticVolumeBig.Statement) (hC : MoriwakiBigCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact hC K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen
  · exact hG6 K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PAmpleCountAlongMultiples
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem charZero_of_isArithVar_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    simp only [mConeMap, map_natCast]
    rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [h.2.2.1] at hmem
  exact_mod_cast (Ideal.mem_bot).1 hmem

theorem AmpleCountAlongMultiples.proofAmple (hL : LiftModel.Statement) (hC : LiftCountAlongMultiples.Statement) :
    AmpleCountAlongMultiples.StatementAmple := by
  intro K _ _ ι _ _ Ω _ y D N P0 II hD hII har hb hP0 hs hcj hgen hc hfib ε hε
  have : CharZero Ω := charZero_of_isArithVar_mCoordIdeal har
  obtain ⟨a, ι', _, x', ha, hmem, hgo, hbir⟩ := hL K ι Ω y D N.a har hb hgen hc hfib
  refine ⟨a, ha, ?_⟩
  have hapos : (0 : ℝ) < (a : ℝ) ^ (D + 1) := pow_pos (by exact_mod_cast ha) _
  filter_upwards [hC K ι Ω y D N P0 II a ι' x' hD hII har hb hP0 hs hcj ha hmem hgo hbir
    (ε * (a : ℝ) ^ (D + 1)) (mul_pos hε hapos)] with k hk
  have key : (II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε) *
        (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      ((a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) - ε * (a : ℝ) ^ (D + 1)) *
        ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    push_cast
    ring
  rw [key]
  exact hk

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PResAboveCover
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Topology Filter ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ResAboveCover.sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => ?_⟩
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ResAboveCover.sameOrbit_trans {a b d : (Σ k, ι k) → ℂ} (h₁ : SameOrbit a b)
    (h₂ : SameOrbit b d) : SameOrbit a d := by
  obtain ⟨c, hc, rfl⟩ := h₁
  obtain ⟨c', hc', rfl⟩ := h₂
  exact ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => by simp [mul_assoc]⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ResAboveCover.sameOrbit_of_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    {v u : α → (Σ k, ι k) → ℂ} {v₀ u₀ : (Σ k, ι k) → ℂ}
    (hv : Tendsto v l (𝓝 v₀)) (hu : Tendsto u l (𝓝 u₀))
    (hvu : ∀ᶠ a in l, SameOrbit (v a) (u a))
    (hv₀ : ∀ k, ∃ i, v₀ ⟨k, i⟩ ≠ 0) (hu₀ : ∀ k, ∃ i, u₀ ⟨k, i⟩ ≠ 0) :
    SameOrbit v₀ u₀ := by
  choose i hi using hu₀
  have hcross : ∀ k j, v₀ ⟨k, j⟩ * u₀ ⟨k, i k⟩ = v₀ ⟨k, i k⟩ * u₀ ⟨k, j⟩ := by
    intro k j
    have h₁ : Tendsto (fun a => v a ⟨k, j⟩ * u a ⟨k, i k⟩) l (𝓝 (v₀ ⟨k, j⟩ * u₀ ⟨k, i k⟩)) :=
      ((continuous_apply _).continuousAt.tendsto.comp hv).mul
        ((continuous_apply _).continuousAt.tendsto.comp hu)
    have h₂ : Tendsto (fun a => v a ⟨k, i k⟩ * u a ⟨k, j⟩) l (𝓝 (v₀ ⟨k, i k⟩ * u₀ ⟨k, j⟩)) :=
      ((continuous_apply _).continuousAt.tendsto.comp hv).mul
        ((continuous_apply _).continuousAt.tendsto.comp hu)
    refine tendsto_nhds_unique h₁ (h₂.congr' ?_)
    filter_upwards [hvu] with a ha
    obtain ⟨c, -, hc⟩ := ha
    simp only [hc]
    ring
  refine ⟨fun k => v₀ ⟨k, i k⟩ / u₀ ⟨k, i k⟩, fun k => div_ne_zero ?_ (hi k), ?_⟩
  · intro h0
    obtain ⟨j, hj⟩ := hv₀ k
    have h := hcross k j
    rw [h0, zero_mul] at h
    exact hj ((mul_eq_zero.mp h).resolve_right (hi k))
  · funext p
    obtain ⟨k, j⟩ := p
    show v₀ ⟨k, j⟩ = v₀ ⟨k, i k⟩ / u₀ ⟨k, i k⟩ * u₀ ⟨k, j⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hi k)]
    exact hcross k j


omit [Fintype K] in
theorem ResAboveCover.tendsto_lift {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X) :
    Tendsto (R.lift x) (𝓝 x) (𝓝 (R.lift x x)) := by
  refine tendsto_pi_nhds.2 fun p => ?_
  obtain ⟨j, hj⟩ := R.A.cover x
  have han := R.holo x p j (R.A.chart j x)
    ⟨(R.A.chart j).map_source hj, by simp [(R.A.chart j).left_inv hj, R.mem_U x]⟩
  have h₁ := han.continuousAt.comp ((R.A.chart j).continuousAt hj)
  have h₂ : ((fun y => R.lift x y p) ∘ (R.A.chart j).symm) ∘ (R.A.chart j) =ᶠ[𝓝 x]
      fun y => R.lift x y p := by
    filter_upwards [(R.A.chart j).eventually_left_inverse hj] with y hy
    simp [hy]
  exact (h₁.congr h₂).tendsto


omit [Fintype K] in
theorem ResAboveCover.limit {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {α : Type*}
    {l : Filter α} [l.NeBot] {v : α → (Σ k, ι k) → ℂ} {x : α → R.X} {v₀ : (Σ k, ι k) → ℂ}
    {x₀ : R.X} (hv : Tendsto v l (𝓝 v₀)) (hx : Tendsto x l (𝓝 x₀))
    (hvx : ∀ᶠ a in l, SameOrbit (v a) (R.lift (x a) (x a))) (hv₀ : ∀ k, ∃ i, v₀ ⟨k, i⟩ ≠ 0) :
    SameOrbit v₀ (R.lift x₀ x₀) ∧
      ∀ᶠ a in l, x a ∈ R.U x₀ ∧ SameOrbit (v a) (R.lift x₀ (x a)) := by
  have hU : ∀ᶠ a in l, x a ∈ R.U x₀ := hx ((R.isOpen_U x₀).mem_nhds (R.mem_U x₀))
  have h₂ : ∀ᶠ a in l, x a ∈ R.U x₀ ∧ SameOrbit (v a) (R.lift x₀ (x a)) := by
    filter_upwards [hU, hvx] with a ha hva
    exact ⟨ha, ResAboveCover.sameOrbit_trans hva
      (ResAboveCover.sameOrbit_symm (R.compat x₀ (x a) (x a) ⟨ha, R.mem_U _⟩))⟩
  refine ⟨ResAboveCover.sameOrbit_of_tendsto hv ((ResAboveCover.tendsto_lift R x₀).comp hx)
    (h₂.mono fun a h => h.2) hv₀ (R.mem x₀ x₀ (R.mem_U x₀)).1, h₂⟩


omit [Fintype K] in
theorem ResAboveCover.exists_limit {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {α : Type*}
    {l : Filter α} [l.NeBot] {v : α → (Σ k, ι k) → ℂ} {v₀ : (Σ k, ι k) → ℂ}
    (hv : Tendsto v l (𝓝 v₀)) (hv₀ : ∀ k, ∃ i, v₀ ⟨k, i⟩ ≠ 0)
    (hex : ∀ᶠ a in l, ∃ x, SameOrbit (v a) (R.lift x x)) :
    ∃ (F : Ultrafilter α) (x : α → R.X) (x₀ : R.X), (F : Filter α) ≤ l ∧
      Tendsto x F (𝓝 x₀) ∧ SameOrbit v₀ (R.lift x₀ x₀) ∧
      ∀ᶠ a in (F : Filter α), x a ∈ R.U x₀ ∧ SameOrbit (v a) (R.lift x₀ (x a)) := by
  classical
  obtain ⟨-, x₁, -⟩ := hex.exists
  let x : α → R.X := fun a => if h : ∃ x, SameOrbit (v a) (R.lift x x) then h.choose else x₁
  have hvx : ∀ᶠ a in l, SameOrbit (v a) (R.lift (x a) (x a)) :=
    hex.mono fun a h => by simp only [x, dif_pos h]; exact h.choose_spec
  let F := Ultrafilter.of l
  have hFl : (F : Filter α) ≤ l := Ultrafilter.of_le l
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.ultrafilter_le_nhds (F.map x) (by simp)
  have hx : Tendsto x F (𝓝 x₀) := by
    rw [Tendsto, ← Ultrafilter.coe_map]
    exact hx₀
  exact ⟨F, x, x₀, hFl, hx, ResAboveCover.limit R (hv.mono_left hFl) hx (hvx.filter_mono hFl) hv₀⟩

theorem ResAboveCover.surj_all (hND : HilbertSamuel.NonvanishingDense.Statement)
    (P J : Ideal (MRing ι)) {e d : ℕ} (R : AnLogRes P J e) (hP : IsArithVar P d) :
    ∀ v ∈ mcPts P, ∃ x, SameOrbit v (R.lift x x) := by
  intro v hv
  obtain ⟨f, hfJ, hfP⟩ := SetLike.not_le_iff_exists.1 R.nondeg
  have hcl := hND K ι P d f hP hfP hv
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hex : ∀ᶠ w in 𝓝[{w | w ∈ mcPts P ∧ eval w (map (Int.castRingHom ℂ) f) ≠ 0}] v,
      ∃ x, SameOrbit w (R.lift x x) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    obtain ⟨x, hx⟩ := R.surj w hw.1 (fun hJ => hw.2 (hJ.2 f hfJ))
    exact ⟨x, ResAboveCover.sameOrbit_symm hx⟩
  obtain ⟨-, -, x₀, -, -, h, -⟩ := ResAboveCover.exists_limit R (v := fun w => w)
    (tendsto_id.mono_left nhdsWithin_le_nhds) hv.1 hex
  exact ⟨x₀, h⟩

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegrePartition
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (segre)

namespace SegrePartition

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def segreSq (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : ℝ := ‖segre z i‖ ^ 2

def segreSqSum (z : (Σ k, ι k) → ℂ) : ℝ := ∑ i, segreSq z i

def numIdx (ι : K → Type*) [∀ k, Fintype (ι k)] : ℝ := Fintype.card ((k : K) → ι k)

def bump (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : ℝ :=
  Real.smoothTransition (2 * numIdx ι * (segreSq z i / segreSqSum z) - 1)


open Classical in
def rho (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if 0 < segreSqSum z then bump z i / ∑ j, bump z j else 1 / numIdx ι

omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem segreSq_nonneg (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) : 0 ≤ segreSq z i :=
  sq_nonneg _

omit [DecidableEq K] in
theorem contDiff_segreSq (i : (k : K) → ι k) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segreSq z i) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segre z i) :=
    contDiff_prod fun k _ => contDiff_apply ℝ (fun _ => ℂ) (⟨k, i k⟩ : Σ k, ι k)
  exact (contDiff_norm_sq ℝ).comp h

theorem contDiff_segreSqSum :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segreSqSum z) :=
  ContDiff.sum fun i _ => contDiff_segreSq i

theorem segreSqSum_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : 0 < segreSqSum z := by
  choose i hi using hz
  have h : segre z i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hi k
  exact Finset.sum_pos' (fun j _ => segreSq_nonneg z j)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr h) 2⟩


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem segre_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segre (fun p => c p.1 * z p) i = (∏ k, c k) * segre z i :=
  Finset.prod_mul_distrib

omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem segreSq_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (i : (k : K) → ι k) :
    segreSq (fun p => c p.1 * z p) i = ‖∏ k, c k‖ ^ 2 * segreSq z i := by
  simp only [segreSq, segre_smul, norm_mul, mul_pow]

theorem segreSqSum_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segreSqSum (fun p => c p.1 * z p) = ‖∏ k, c k‖ ^ 2 * segreSqSum z := by
  simp only [segreSqSum, segreSq_smul, Finset.mul_sum]

theorem exists_bump_pos (hN : 0 < numIdx ι) {z : (Σ k, ι k) → ℂ} (hS : 0 < segreSqSum z) :
    ∃ j, 0 < bump z j := by
  by_contra h
  push Not at h
  have hle : ∀ j, segreSq z j ≤ segreSqSum z / (2 * numIdx ι) := by
    intro j
    have h1 : 2 * numIdx ι * (segreSq z j / segreSqSum z) - 1 ≤ 0 := by
      by_contra h2
      exact absurd (Real.smoothTransition.pos_of_pos (lt_of_not_ge h2)) (not_lt.mpr (h j))
    rw [le_div_iff₀ (by positivity)]
    have h3 : 2 * numIdx ι * segreSq z j / segreSqSum z ≤ 1 := by
      rw [mul_div_assoc]; linarith
    rw [div_le_one hS] at h3
    linarith
  have hsum : segreSqSum z ≤ numIdx ι * (segreSqSum z / (2 * numIdx ι)) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => segreSq z j) _ fun j _ => hle j
    rw [Finset.card_univ, nsmul_eq_mul] at this
    exact this
  have h4 : numIdx ι * (segreSqSum z / (2 * numIdx ι)) = segreSqSum z / 2 := by
    field_simp
  linarith

theorem bump_sum_pos (hN : 0 < numIdx ι) {z : (Σ k, ι k) → ℂ} (hS : 0 < segreSqSum z) :
    0 < ∑ j, bump z j := by
  obtain ⟨j, hj⟩ := exists_bump_pos hN hS
  exact Finset.sum_pos' (fun i _ => Real.smoothTransition.nonneg _) ⟨j, Finset.mem_univ _, hj⟩

theorem contDiffOn_bump (i : (k : K) → ι k) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => bump z i)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  refine (Real.smoothTransition.contDiff (n := ⊤)).comp_contDiffOn ?_
  refine ContDiffOn.sub (contDiffOn_const.mul ?_) contDiffOn_const
  exact ContDiffOn.div (contDiff_segreSq i).contDiffOn contDiff_segreSqSum.contDiffOn
    fun z hz => (segreSqSum_pos hz).ne'

theorem bump_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (i : (k : K) → ι k) :
    bump (fun p => c p.1 * z p) i = bump z i := by
  have ha : ‖∏ k, c k‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k))
  simp only [bump, segreSq_smul, segreSqSum_smul, mul_div_mul_left _ _ ha]

theorem isDegZeroSmooth_rho (hN : 0 < numIdx ι) (i : (k : K) → ι k) :
    IsDegZeroSmooth (rho (ι := ι) i) := by
  refine ⟨?_, fun c z hc => ?_⟩
  · have hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : (Σ k, ι k) → ℂ => bump z i / ∑ j, bump z j) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
      ContDiffOn.div (contDiffOn_bump i) (ContDiffOn.sum fun j _ => contDiffOn_bump j)
        fun z hz => (bump_sum_pos hN (segreSqSum_pos hz)).ne'
    refine hf.congr fun z hz => ?_
    simp only [rho, if_pos (segreSqSum_pos hz)]
  · have ha : 0 < ‖∏ k, c k‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)) 2
    have hS : 0 < segreSqSum (fun p => c p.1 * z p) ↔ 0 < segreSqSum z := by
      rw [segreSqSum_smul]; exact mul_pos_iff_of_pos_left ha
    simp only [rho, hS, bump_smul c z hc]

theorem sum_rho (hN : 0 < numIdx ι) (z : (Σ k, ι k) → ℂ) : ∑ i, rho (ι := ι) i z = 1 := by
  by_cases hS : 0 < segreSqSum z
  · simp only [rho, if_pos hS]
    rw [← Finset.sum_div, div_self (bump_sum_pos hN hS).ne']
  · simp only [rho, if_neg hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [numIdx] at hN ⊢
    field_simp

theorem rho_eq_zero (hN : 0 < numIdx ι) (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ)
    (h : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * ‖segre z‖) : rho i z = 0 := by
  have hδ : 0 < (Real.sqrt (2 * numIdx ι))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hw : 0 < ‖segre z‖ := by
    by_contra h0
    have : ‖segre z‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    rw [this, mul_zero] at h
    exact absurd h (not_lt.mpr (norm_nonneg _))
  have hle : ‖segre z‖ ≤ Real.sqrt (segreSqSum z) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun j => segreSq z j) (fun j _ => segreSq_nonneg z j)
      (Finset.mem_univ j)
  have hS : 0 < segreSqSum z := Real.sqrt_pos.mp (lt_of_lt_of_le hw hle)
  have h1 : ‖segre z i‖ < (Real.sqrt (2 * numIdx ι))⁻¹ * Real.sqrt (segreSqSum z) :=
    lt_of_lt_of_le h (mul_le_mul_of_nonneg_left hle hδ.le)
  have h2 : segreSq z i < segreSqSum z / (2 * numIdx ι) := by
    have h3 := pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hS.le] at h3
    rw [segreSq]
    calc ‖segre z i‖ ^ 2 < (2 * numIdx ι)⁻¹ * segreSqSum z := h3
      _ = segreSqSum z / (2 * numIdx ι) := by rw [inv_mul_eq_div]
  have hb : bump z i = 0 := by
    refine Real.smoothTransition.zero_of_nonpos ?_
    rw [lt_div_iff₀ (by positivity)] at h2
    have h4 : 2 * numIdx ι * (segreSq z i / segreSqSum z) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one hS]
      linarith
    linarith
  simp only [rho, if_pos hS, hb, zero_div]

end SegrePartition

theorem SegrePartition.proof : SegrePartition.Statement := by
  intro K _ _ ι _ hne
  have hN : 0 < SegrePartition.numIdx ι := by
    rw [SegrePartition.numIdx, Nat.cast_pos]
    exact Fintype.card_pos
  exact ⟨(Real.sqrt (2 * SegrePartition.numIdx ι))⁻¹,
    inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)), SegrePartition.rho,
    SegrePartition.isDegZeroSmooth_rho hN, SegrePartition.sum_rho hN,
    SegrePartition.rho_eq_zero hN⟩

end GroundTheory.Heights₂.Heights
end
end

