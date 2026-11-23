module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentFrameComparison
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentOrbitComparison
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0074
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0103
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwoFramesOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem orbit_ne {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z' z) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem eq_of_orbit_of_normalised {u v : (Σ k, ι k) → ℂ} (h : SameOrbit u v) (e : ∀ k, ι k)
    (hu : ∀ k, u ⟨k, e k⟩ = 1) (hv : ∀ k, v ⟨k, e k⟩ = 1) : u = v := by
  obtain ⟨c, hc, rfl⟩ := h
  have h1 : ∀ k, c k = 1 := fun k => by
    have h2 : c k * v ⟨k, e k⟩ = 1 := hu k
    rwa [hv k, mul_one] at h2
  funext p
  show c p.1 * v p = v p
  rw [h1 p.1, one_mul]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem base_of_orbit (M : FlagModel y Ψ N j) {z z' : (Σ k, ι k) → ℂ} (ho : SameOrbit z z')
    (hz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) :
    mCoordIdeal (basePart M.blk z') = mCoordIdeal (basePart M.blk z) ∧
      basePart M.blk z' ∈ mcPts (mCoordIdeal M.x) := by
  obtain ⟨c, hc, rfl⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho
  have h := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x (basePart M.blk z)
    (fun k => c k.1) (fun k => hc k.1)
  exact ⟨h.1, (h.2 hz).1⟩

theorem normRhs_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F F' : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.IsFrame F' → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F' (mCoordIdeal (basePart M.blk z₀')) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₀' h') → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F' z₀' z₁' h' t' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀ z₁ z₀' z₁' h h' t t' hmc hn₀ hn₁ hbase
    hF hF' hG hG' ho₀ ho₁ hh hd hh' hd' ht ht' hE₀ hE₁ hE₀' hE₁'
  obtain ⟨hid, hmc'⟩ := base_of_orbit M ho₀ hmc
  have hn₀' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₀) hn₀
  have hn₁' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁) hn₁
  have hbase' : basePart M.blk z₁' = basePart M.blk z₀' := by
    have h1 : SameOrbit (basePart M.blk z₁') (basePart M.blk z₁) :=
      basePart_orbit M.blk (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁)
    rw [hbase] at h1
    exact eq_of_orbit_of_normalised
      (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans h1 (basePart_orbit M.blk ho₀)) F'.c (hE₁' a).1 (hE₀' a).1
  obtain ⟨w₀, w₁, S, hw₀, hw₁, hS, hSd, hX₀, hX₁, hnorm⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Move.main K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀' z₁' h' t' hmc' hn₀' hn₁' hbase'
      hF hF' (by rw [hid]; exact hG) hG' hh' hd' ht' hE₀' hE₁'
  rw [← hnorm]
  exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F z₀ z₁ w₀ w₁ h (S * h') t t' hmc hn₀ hn₁
    hbase hF hG (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₀ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₀))
    (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₁ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₁)) hh hd (hS.mul hh')
    (by rw [Matrix.det_mul]; exact mul_ne_zero hSd hd') ht ht' hE₀ hE₁ hX₀ hX₁

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticNinth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section Pair

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]

theorem mConeMap_pair_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap (pairV a b) (rename inlV g) = rename Sum.inl (mConeMap a g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inlV, pairV]

theorem mConeMap_pair_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι') :
    mConeMap (pairV a b) (rename inrV g) = rename Sum.inr (mConeMap b g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inrV, pairV]

theorem imageZ_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inlV (mCoordIdeal (pairV a b)) = mCoordIdeal a := by
  ext f
  show mConeMap (pairV a b) (rename inlV f) = 0 ↔ mConeMap a f = 0
  rw [mConeMap_pair_inl]
  exact (rename_injective _ Sum.inl_injective).eq_iff' (map_zero _)

theorem imageZ_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inrV (mCoordIdeal (pairV a b)) = mCoordIdeal b := by
  ext f
  show mConeMap (pairV a b) (rename inrV f) = 0 ↔ mConeMap b f = 0
  rw [mConeMap_pair_inr]
  exact (rename_injective _ Sum.inr_injective).eq_iff' (map_zero _)

end Pair

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeBound
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem continuous_upV (v : (Σ k, ιk k) → (Σ k, ι k)) : Continuous (upV v) := by
  refine continuous_pi fun q => ?_
  unfold upV
  by_cases h : ∃ q', v q' = q
  · simp only [dif_pos h]
    exact continuous_apply _
  · simp only [dif_neg h]
    exact continuous_const

theorem continuous_pBase (M : FlagModel y Ψ N j) (v : (Σ k, ιk k) → (Σ k, ι k)) : Continuous (pBase M v) := by
  refine continuous_pi fun q => ?_
  exact (continuous_apply (⟨q.1.1, q.2⟩ : Σ k, ι k)).comp (continuous_upV v)

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∃ O' : Set ((Σ k, ιk k) → ℂ), IsOpen O' ∧ pO M Rb keep v F kb V r h = O' ∩ mcPts (mCoordIdeal (y ∘ v)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc
  obtain ⟨hBM, hkp, -, hBC, hr, hrc, -⟩ := hc
  have hmaps : Set.MapsTo (pBase M v) (mcPts (mCoordIdeal (y ∘ v))) (mcPts (mCoordIdeal M.x)) :=
    (_root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main K ι Φ y Ψ N j M keep Kk ιk κ v hBM hkp).1
  have key : ∀ z₀ ∈ pO M Rb keep v F kb V r h,
      pO M Rb keep v F kb V r h ∈ 𝓝[mcPts (mCoordIdeal (y ∘ v))] z₀ := by
    rintro z₀ ⟨hz₀, hsrc, hV₀, hm⟩
    have hbm := hmaps hz₀
    have hG : M.GoodAt F (mCoordIdeal (pBase M v z₀)) := by
      obtain ⟨-, -, hgood, horb⟩ := hBC.2.2.2.2 _ hV₀
      rw [(Rb.A.chart kb).left_inv hsrc] at horb
      rwa [CovMap.mCoordIdeal_eq_of_sameOrbit (orbit_trans (orbit_symm (hr _ hbm)) horb)]
    have hrb : ContinuousWithinAt (fun z => r (pBase M v z)) (mcPts (mCoordIdeal (y ∘ v))) z₀ :=
      (hrc _ hbm).comp (continuous_pBase M v).continuousWithinAt hmaps
    have e₁ := hrb.tendsto.eventually_mem ((Rb.A.chart kb).open_source.mem_nhds hsrc)
    have e₂ := (((Rb.A.chart kb).continuousAt hsrc).tendsto.comp hrb.tendsto).eventually_mem (hBC.1.mem_nhds hV₀)
    have tw := GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.continuousWithinAt_twMinor M F (continuous_pBase M v) (continuous_upV v) hmaps hz₀ hG
    have e₃ : ∀ᶠ z in 𝓝[mcPts (mCoordIdeal (y ∘ v))] z₀, ∀ p k, keep p → M.blk p = some k →
        twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0 := by
      refine eventually_all.2 fun p => eventually_all.2 fun k => ?_
      by_cases hp : keep p ∧ M.blk p = some k
      · exact ((tw p.2 k (h p.1)⁻¹ (stepCols N j p.2)).tendsto.eventually_ne
          (hm p k hp.1 hp.2)).mono fun _ hz _ _ => hz
      · exact Eventually.of_forall fun _ h₁ h₂ => absurd ⟨h₁, h₂⟩ hp
    filter_upwards [self_mem_nhdsWithin, e₁, e₂, e₃] with z h₀ h₁ h₂ h₃
    exact ⟨h₀, h₁, h₂, h₃⟩
  choose! U hU hmem hsub using fun z₀ (hz : z₀ ∈ pO M Rb keep v F kb V r h) =>
    mem_nhdsWithin.1 (key z₀ hz)
  refine ⟨⋃ z₀ ∈ pO M Rb keep v F kb V r h, U z₀, isOpen_biUnion hU, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨Set.mem_biUnion hz (hmem z hz), hz.1⟩
  · rintro z ⟨hz, hzA⟩
    obtain ⟨z₀, h₀, hz₀⟩ := Set.mem_iUnion₂.1 hz
    exact hsub z₀ h₀ ⟨hz₀, hzA⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead
open GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Read

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)


include M in
theorem off_step {p : Ψ × Fin N} {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) (I : Finset (Fin N))
    (hI : ¬ IsStepRows N j p.2 I) : minorIJ A I (stepCols N j p.2) = 0 :=
  ((_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le).2.1 A I hA hI).resolve_right
    (Finset.nonempty_iff_ne_empty.1 (stepCols_nonempty M.j_le p.2))

theorem pluck_eq {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) {z : (Σ k, ι k) → ℂ} {α : ℂ}
    (hz : ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2))
    (I₀ : Finset (Fin N)) (hI₀ : IsStepRows N j p.2 I₀) :
    pluck M F zb k z I₀ = α * minorIJ A I₀ (stepCols N j p.2) := by
  let val := regVal hzb
  let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x zb :=
    fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x zb :=
    fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I') = if I₀ = I' then 1 else 0 := fun I' hI' => by
    have e : ∑ m : ι k, vA I₀ ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I₀ = I' then 1 else 0 := by
      apply Subtype.ext
      have := hF.2.2.1 p k hp I₀ I' hI₀ hI'
      split_ifs at this ⊢ <;> simpa [uA, vA] using this
    have e' := congrArg val e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e'
    simp only [map_mul] at e'
    rw [e']
    split_ifs <;> simp
  have key : ∀ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) =
      if I = I₀ then minorIJ A I₀ (stepCols N j p.2) else 0 := fun I => by
    by_cases hI : IsStepRows N j p.2 I
    · rw [rel I hI]
      by_cases e : I = I₀
      · subst e; simp
      · simp [e, Ne.symm e]
    · have e : I ≠ I₀ := fun e => hI (e ▸ hI₀)
      rw [off_step M hA I hI, if_neg e, mul_zero]
  have read : ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2) =
      minorIJ A I₀ (stepCols N j p.2) := by
    calc _ = ∑ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => ?_
          rw [mul_assoc]
          rfl
      _ = _ := by simp only [key]; simp
  rw [← read, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hz m, mul_left_comm]
  rfl

end Read

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (p : Ψ × Fin N) (k : K) (A g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (α : ℂ) (J : Finset (Fin N)), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → M.blk p = some k → IsBlockDiag j A → (∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2)) → twMinor M F zb p.2 k g z J = α * minorIJ (g * A) J (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F zb p k A g z α J hF hzb hG hp hA hz
  unfold twMinor
  rw [(_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le).1 g A J (stepCols N j p.2), Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · rw [pluck_eq M hF hzb hG hp hA hz I hI]
    ring
  · rw [off_step M hA I hI]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralFibreSumChangeOfVariablesStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fibre_sum_change_of_variables : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → MIntegrable A Φ G → Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) ∧ mInt A Φ G = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsNormFnLogNormSecDiagSec
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isNormFn_logNormSec_diagSec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ (b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ c : ℝ, IsNormFn M τ a k₀ ca cb RW fun x => logNormSec (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) x + c := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL b hb hab hk hca hcb hW c
    x z₀ z₁ F h t h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hd : IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hno := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.not_sameOrbit_of_ptData K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hd
  obtain ⟨-, -, hx, -, -, -, hu, hiff, hnorm⟩ := hL x
  have hψ : ψ x x (i₀ x) ≠ 0 := fun h0 => hno ((hiff x hx).1 h0)
  have hn := hnorm x hx hψ z₀ z₁ F h t hd
  have hne : ‖u x x * ψ x x (i₀ x)‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero (hu x hx) hψ)
  show Real.log (‖u x x * ψ x x (i₀ x)‖ *
    Real.exp (-(Real.log ((potA M τ a k₀).h (RW.lift x x)) + c))) + c = _
  rw [Real.log_mul hne (Real.exp_ne_zero _), Real.log_exp, ← hn]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentMinorFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N : ℕ}

theorem minorIJ_self_of_isLowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) (C : Finset (Fin N)) :
    minorIJ X C C = 1 := by
  have key : minorIJ X C C = minorIJ Xᵀ C C := by
    rw [minorIJ_eq_det X C C C.card rfl rfl, minorIJ_eq_det Xᵀ C C C.card rfl rfl,
      ← Matrix.transpose_submatrix, Matrix.det_transpose]
  rw [key, minorIJ_self_of_triangular Xᵀ (fun i j hij => by simpa [Matrix.transpose_apply] using hX.2 j i hij) C]
  exact Finset.prod_eq_one (fun c _ => hX.1 c)

theorem minorIJ_insert_erase_of_isLowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) {C : Finset (Fin N)}
    {a' b' : Fin N} (hb : b' ∈ C) (hmax : ∀ c ∈ C, c ≤ b') (hlt : b' < a') :
    minorIJ X (insert a' (C.erase b')) C = X a' b' := by
  have ha : a' ∉ C := fun h => absurd (hmax a' h) (not_le.mpr hlt)
  obtain ⟨n, hn⟩ : ∃ n, C.card = n + 1 :=
    ⟨C.card - 1, by have := Finset.card_pos.mpr ⟨b', hb⟩; omega⟩
  have hR : (insert a' (C.erase b')).card = n + 1 := by
    rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hb, hn]
    rfl
  set eC := C.orderEmbOfFin hn with heC
  have hlast : eC (Fin.last n) = b' := by
    have hmem : b' ∈ Set.range eC := by rw [heC, Finset.range_orderEmbOfFin]; exact hb
    obtain ⟨k, hk⟩ := hmem
    rcases (Fin.le_last k).lt_or_eq with h | h
    · have h1 : eC k < eC (Fin.last n) := eC.strictMono h
      have h2 : eC (Fin.last n) ∈ C := Finset.orderEmbOfFin_mem C hn _
      exact absurd (hmax _ h2) (not_le.mpr (hk ▸ h1))
    · rw [← h, hk]
  have hlt' : ∀ k : Fin (n + 1), k ≠ Fin.last n → eC k < b' := fun k hk =>
    hlast ▸ eC.strictMono (lt_of_le_of_ne (Fin.le_last k) hk)
  let f : Fin (n + 1) → Fin N := fun k => if k = Fin.last n then a' else eC k
  have hfmono : StrictMono f := by
    intro i j hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
    simp only [f, if_neg hi]
    by_cases hj : j = Fin.last n
    · rw [if_pos hj]; exact (hlt' i hi).trans hlt
    · rw [if_neg hj]; exact eC.strictMono hij
  have hfmem : ∀ k, f k ∈ insert a' (C.erase b') := by
    intro k
    simp only [f]
    split_ifs with hk
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨(hlt' k hk).ne, Finset.orderEmbOfFin_mem C hn k⟩)
  have hR' : ⇑((insert a' (C.erase b')).orderEmbOfFin hR) = f :=
    (Finset.orderEmbOfFin_unique hR hfmem hfmono).symm
  rw [minorIJ_eq_det X _ C (n + 1) hR hn, hR', Matrix.det_of_lowerTriangular]
  · have h1 : ∀ k : Fin n, X.submatrix f eC k.castSucc k.castSucc = 1 := by
      intro k
      show X (f k.castSucc) (eC k.castSucc) = 1
      simp only [f, if_neg (Fin.castSucc_lt_last k).ne]
      exact hX.1 _
    rw [Fin.prod_univ_castSucc, Finset.prod_eq_one (fun k _ => h1 k), one_mul]
    show X (if Fin.last n = Fin.last n then a' else eC (Fin.last n)) (eC (Fin.last n)) = X a' b'
    rw [if_pos rfl, hlast]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))
    simp only [Matrix.submatrix_apply, f, if_neg hi]
    exact hX.2 _ _ (eC.strictMono hij')

theorem mem_stepCols_stepOf (N j : ℕ) (c : Fin N) :
    c ∈ stepCols N j (stepOf N j c) ∧ ∀ x ∈ stepCols N j (stepOf N j c), x ≤ c := by
  have hc := c.isLt
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [stepCols, stepOf]
    split_ifs
    all_goals (try simp)
    all_goals omega
  · have hx' := x.isLt
    simp only [stepCols, stepOf] at hx
    rw [Fin.le_iff_val_le_val]
    split_ifs at hx
    all_goals (try simp at hx)
    all_goals omega

theorem minorIJ_stepCols_of_isLowerUni (N j : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (a' b' : Fin N) (_hj : j ≤ N)
    (_hd : IsBlockDiag j X) (hX : IsLowerUni X) (hlt : b' < a') (_hs : (a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) :
    minorIJ X (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) = 1 ∧
      minorIJ X (insert a' ((stepCols N j (stepOf N j b')).erase b')) (stepCols N j (stepOf N j b')) = X a' b' := by
  obtain ⟨hb, hmax⟩ := mem_stepCols_stepOf N j b'
  exact ⟨minorIJ_self_of_isLowerUni hX _, minorIJ_insert_erase_of_isLowerUni hX hb hmax hlt⟩

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor
end
end

