module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothAutomorphicOpenInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0440
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceComposition
section
open Filter Topology
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem convComp_proved : ConvComp := by
  intro E _ _ _ N t s φ h hφ
  induction h with
  | leaf V z z₀ h => exact Conv.leaf V (fun k => z (φ k)) z₀ (h.comp hφ.tendsto_atTop)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceInfimum
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvInfProof

theorem tendsto_prod_shift (m₀ : Multiset ℂ) {z : ℕ → ℂ} {z₀ : ℂ} (h : Tendsto z atTop (𝓝 z₀)) (u : ℂ) :
    Tendsto (fun k => ((m₀.map (· + z k)).map (u + ·)).prod) atTop
      (𝓝 (((m₀.map (· + z₀)).map (u + ·)).prod)) := by
  induction m₀ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (tendsto_const_nhds.add (h.const_add a)).mul ih

theorem convInf_of_discInf_topInf : DiscInf → TopInf → ConvInf := by
  intro hD hT E _ _ _ N t s τ hc hs
  induction hc with
  | leaf V z z₀ h =>
    have hex : ∃ m₀, HasInfCharGL V τ m₀ := by
      rcases hs with ⟨rfl, rfl, -⟩ | ⟨-, hV, -⟩
      · exact ⟨0, hT E τ⟩
      · exact hD E _ V hV τ
    obtain ⟨m₀, h₀⟩ := hex
    exact ⟨m₀.map (· + z₀), fun k => m₀.map (· + z k), ⟨m₀, h₀, rfl⟩, fun k => ⟨m₀, h₀, rfl⟩,
      fun u => tendsto_prod_shift m₀ h u⟩
  | node h₁ h₂ ih₁ ih₂ =>
    obtain ⟨a₀, a, ha₀, ha, hat⟩ := ih₁ hs.1
    obtain ⟨b₀, b, hb₀, hb, hbt⟩ := ih₂ hs.2
    refine ⟨a₀ + b₀, fun k => a k + b k, ⟨a₀, b₀, ha₀, hb₀, rfl⟩,
      fun k => ⟨a k, b k, ha k, hb k, rfl⟩, fun u => ?_⟩
    simp only [Multiset.map_add (f := _), Multiset.prod_add]
    exact (hat u).mul (hbt u)

end GlobalTheory.CompanionTheory.EGlue.ConvInfProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceShift
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.EGlue

theorem convShift_holds : ConvShift := by
  intro E _ _ _ N t s z z₀ h hz
  induction h with
  | leaf V w w₀ hw => exact Conv.leaf V (fun k => w k + z k) (w₀ + z₀) (hw.add hz)
  | node _ _ i₁ i₂ => exact Conv.node i₁ i₂

end GlobalTheory.CompanionTheory.EGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStrip
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvStripProof

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def nodeRank : {N : ℕ} → Tr E N → Option ℕ
  | _, .leaf _ _ => none
  | _, @Tr.node _ _ _ _ r _ _ _ => some r

theorem nodeRank_heq {N M : ℕ} (u : Tr E N) (v : Tr E M) (h : N = M) (hh : HEq u v) :
    nodeRank u = nodeRank v := by
  subst h
  rw [eq_of_heq hh]

theorem twists_length_strip : ∀ {N : ℕ} (u : Tr E N), u.strip.twists.length = u.twists.length := by
  intro N u
  induction u with
  | leaf V z => rfl
  | node t₁ t₂ i₁ i₂ => simp [Tr.strip, Tr.twists, i₁, i₂]

theorem twists_length_eq {N : ℕ} {u v : Tr E N} (h : u.strip = v.strip) :
    u.twists.length = v.twists.length := by
  rw [← twists_length_strip u, h, twists_length_strip]

theorem leaf_of_strip {N : ℕ} (u : Tr E N) (V : Submodule ℂ (Sm E N)) (w : ℂ)
    (h : u.strip = .leaf V w) : ∃ z, u = .leaf V z := by
  revert V w h
  cases u with
  | leaf V' z =>
    intro V w h
    simp only [Tr.strip] at h
    injection h with _ h₁
    exact ⟨z, by rw [h₁]⟩
  | node a b =>
    intro V w h
    have := congrArg nodeRank h
    simp [Tr.strip, nodeRank] at this

theorem node_of_strip_eq : ∀ {N : ℕ} (u : Tr E N) {r s : ℕ} (_ : N = r + s) (x : Tr E r) (y : Tr E s),
    HEq u.strip (Tr.node x y) →
    ∃ (a : Tr E r) (b : Tr E s), HEq u (Tr.node a b) ∧ a.strip = x ∧ b.strip = y := by
  intro N u
  cases u with
  | leaf V z =>
    intro r s hN x y h
    subst hN
    have := congrArg nodeRank (eq_of_heq h)
    simp [Tr.strip, nodeRank] at this
  | @node r' s' a b =>
    intro r s hN x y h
    have h₁ : r' = r := by
      have := nodeRank_heq _ _ hN h
      simpa [Tr.strip, nodeRank] using this
    subst h₁
    have h₂ : s' = s := by omega
    subst h₂
    have h₃ := eq_of_heq h
    simp only [Tr.strip] at h₃
    injection h₃ with _ _ e₁ e₂
    exact ⟨a, b, HEq.rfl, e₁, e₂⟩

theorem node_of_strip {r s : ℕ} (u : Tr E (r + s)) (x : Tr E r) (y : Tr E s)
    (h : u.strip = Tr.node x y) :
    ∃ (a : Tr E r) (b : Tr E s), u = Tr.node a b ∧ a.strip = x ∧ b.strip = y := by
  obtain ⟨a, b, e, h₁, h₂⟩ := node_of_strip_eq u rfl x y (heq_of_eq h)
  exact ⟨a, b, eq_of_heq e, h₁, h₂⟩

theorem getD_append_left (A B : List ℂ) {i : ℕ} (h : i < A.length) :
    (A ++ B).getD i 0 = A.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (A B : List ℂ) (i : ℕ) :
    (A ++ B).getD (A.length + i) 0 = B.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem getD_of_le (A : List ℂ) {i : ℕ} (h : A.length ≤ i) : A.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem conv_forward {N : ℕ} {t : ℕ → Tr E N} {s : Tr E N} (h : Conv t s) :
    (∀ k, (t k).strip = s.strip) ∧
      ∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0)) := by
  induction h with
  | leaf V z z₀ h =>
    refine ⟨fun k => rfl, fun i => ?_⟩
    cases i with
    | zero => simpa [Tr.twists] using h
    | succ i => simp [Tr.twists]
  | @node r s t₁ t₂ s₁ s₂ _ _ i₁ i₂ =>
    refine ⟨fun k => ?_, fun i => ?_⟩
    · simp only [Tr.strip, i₁.1 k, i₂.1 k]
    · have hl : ∀ k, (t₁ k).twists.length = s₁.twists.length := fun k => twists_length_eq (i₁.1 k)
      simp only [Tr.twists]
      by_cases hi : i < s₁.twists.length
      · rw [getD_append_left _ _ hi]
        have : (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD i 0) = fun k => (t₁ k).twists.getD i 0 :=
          funext fun k => getD_append_left _ _ (by rw [hl k]; exact hi)
        rw [this]
        exact i₁.2 i
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hi)
        rw [getD_append_right]
        have : (fun k => ((t₁ k).twists ++ (t₂ k).twists).getD (s₁.twists.length + j) 0) =
            fun k => (t₂ k).twists.getD j 0 :=
          funext fun k => by rw [← hl k, getD_append_right]
        rw [this]
        exact i₂.2 j

theorem conv_backward : ∀ {N : ℕ} (s : Tr E N) (t : ℕ → Tr E N), (∀ k, (t k).strip = s.strip) →
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0))) → Conv t s := by
  intro N s
  induction s with
  | leaf V z₀ =>
    intro t hs ht
    choose z hz using fun k => leaf_of_strip (t k) V 0 (hs k)
    obtain rfl : t = fun k => .leaf V (z k) := funext hz
    exact Conv.leaf V z z₀ (by simpa [Tr.twists] using ht 0)
  | @node r s s₁ s₂ i₁ i₂ =>
    intro t hs ht
    choose a b hab ha hb using fun k => node_of_strip (t k) s₁.strip s₂.strip (hs k)
    obtain rfl : t = fun k => .node (a k) (b k) := funext hab
    have hl : ∀ k, (a k).twists.length = s₁.twists.length := fun k => twists_length_eq (ha k)
    simp only [Tr.twists] at ht
    refine Conv.node (i₁ a ha fun i => ?_) (i₂ b hb fun i => ?_)
    · by_cases hi : i < s₁.twists.length
      · have h := ht i
        rw [getD_append_left _ _ hi] at h
        have e : (fun k => ((a k).twists ++ (b k).twists).getD i 0) = fun k => (a k).twists.getD i 0 :=
          funext fun k => getD_append_left _ _ (by rw [hl k]; exact hi)
        rwa [e] at h
      · have e : (fun k => (a k).twists.getD i 0) = fun _ => (0 : ℂ) :=
          funext fun k => getD_of_le _ (by rw [hl k]; exact not_lt.mp hi)
        rw [e, getD_of_le _ (not_lt.mp hi)]
        exact tendsto_const_nhds
    · have h := ht (s₁.twists.length + i)
      rw [getD_append_right] at h
      have e : (fun k => ((a k).twists ++ (b k).twists).getD (s₁.twists.length + i) 0) =
          fun k => (b k).twists.getD i 0 :=
        funext fun k => by rw [← hl k, getD_append_right]
      rwa [e] at h

theorem convStrip : ConvStrip := fun _ _ _ _ _ t s =>
  ⟨conv_forward, fun h => conv_backward s t h.1 h.2⟩

end GlobalTheory.CompanionTheory.EGlue.ConvStripProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.CuspFinGL

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hφ.1.level
  exact GlobalTheory.CompanionTheory.SiegelDecay.rapid_decay_of_one_parabolic_bounds E a φ.1 hc
    (GlobalTheory.CompanionTheory.GGPS.ggps_bound E a φ.1 hs (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E a φ hφ.1)
      (GlobalTheory.CompanionTheory.AutLevel.exists_open_level E a φ hφ.1) (GlobalTheory.CompanionTheory.CuspBridge.isCuspidal_of_isCuspForm E a φ hφ)
      (GlobalTheory.T.arch_lie_derivative_exists E a φ hs hφ.1) (GlobalTheory.CompanionTheory.BoxBound.box_bound E a φ hφ.1))

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

end GlobalTheory.CompanionTheory.CuspFinGL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DehomogenizedEvalEqRatio
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

namespace GlobalTheory.CompanionTheory.MixZ

theorem ev_dehomog_of_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (f : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog f a →
    ∀ (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder w z → w ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) →
    ev (mpStr ℤ m n) σ₀ (mchart c) (dehomog c f) w =
      eval z (map (Int.castRingHom ℂ) f) / ∏ k, z ⟨k, c k⟩ ^ a k := by
  intro m n c f a hf w z H hw
  have hmem : ∀ k, w ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) := fun k =>
    GlobalTheory.CxPts.ptsIn_mono (mchart_le c k) hw
  have hX : ∀ q, GlobalTheory.CxPts.evHom hw (dehomog c (X q)) = z q / z ⟨q.1, c q.1⟩ := by
    rintro ⟨k, i⟩
    rw [← GlobalTheory.CxPts.ev_eq hw]
    simp only [dehomog, coe_eval₂Hom, eval₂_X]
    rw [GlobalTheory.CxPts.ev_res _ hw]
    exact (H k (c k)).2 i (hmem k)
  have hφ : (GlobalTheory.CxPts.evHom hw).comp (dehomog c) =
      eval₂Hom (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun q => ?_)
    · simp
    · simpa using hX q
  have hv : GlobalTheory.CxPts.evHom hw (dehomog c f) =
      eval₂ (Int.castRingHom ℂ) (fun q => z q / z ⟨q.1, c q.1⟩) f := by
    simpa using congrArg (fun φ => φ f) hφ
  rw [GlobalTheory.CxPts.ev_eq hw, hv, MvPolynomial.eval_map, eval₂_eq', eval₂_eq', Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  have hden : ∏ q : Σ k, Bk n k, z ⟨q.1, c q.1⟩ ^ e q = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Bk n k => e ⟨k, i⟩) (z ⟨k, c k⟩)).trans (by rw [hf e he k])
  simp only [div_pow, Finset.prod_div_distrib, hden]
  rw [mul_div_assoc]

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundByRecursionStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_bound_by_recursion : ∀ (H ι : Type) [MeasurableSpace H] (ν : Measure H) (D : Set H → ℝ≥0∞) (Dtot : ℝ≥0∞), Dtot ≠ ⊤ → (∀ Y, MeasurableSet Y → D Y ≤ Dtot) → ∀ (I : Finset ι) (α β : ι → ℝ≥0) (C₀ : ℝ≥0), (∀ Y, MeasurableSet Y → ∃ Z : ι → Set H, (∀ i ∈ I, MeasurableSet (Z i) ∧ ν (Z i) = β i * ν Y) ∧ D Y ≤ C₀ * ν Y + ∑ i ∈ I, α i * D (Z i)) → ∑ i ∈ I, α i * β i < 1 → ∑ i ∈ I, α i < 1 → ∃ C : ℝ≥0, ∀ Y, MeasurableSet Y → D Y ≤ C * ν Y := by
  first | exact @GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated | exact GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated | (intros; apply GlobalTheory.CompanionTheory.DensityIter.bounded_density_of_iterated <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerate
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Frame

theorem det_ne_zero_of_gramQ : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
    ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  intro D W b₀ hb x₀ hx h0
  apply hb
  rw [← hx]
  unfold gramQ
  simp [Matrix.det_mul, h0]

end GlobalTheory.CompanionTheory.ColumnSplitting.Frame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnEvProd
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.Ar.ProdHolo

variable {k : Type} [CommRing k] {Z X : Scheme.{0}} {q : Z ⟶ Sp k} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem mem_ptsIn_preimage {π : Z ⟶ X} {z : CxPts q σ} {x : CxPts p σ} (h : z.1 ≫ π = x.1)
    {U : X.Opens} (hx : x ∈ ptsIn p σ U) : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := by
  rw [mem_ptsIn] at hx ⊢
  rw [← h] at hx
  exact hx

theorem ev_appLE {π : Z ⟶ X} {z : CxPts q σ} {x : CxPts p σ} (h : z.1 ≫ π = x.1)
    {U : X.Opens} {W : Z.Opens} (e : W ≤ π ⁻¹ᵁ U) (hz : z ∈ ptsIn q σ W)
    (a : Γ(X, U)) :
    CxPts.ev q σ W ((π.appLE U W e).hom a) z = CxPts.ev p σ U a x := by
  have h1 := GlobalTheory.CxPts.ev_res (p := q) (σ := σ) e hz ((π.app U).hom a)
  refine Eq.trans ?_ (h1.trans ?_)
  · rfl
  · have h2 := GlobalTheory.Points.valR_comp z.1 π U a
    rw [h] at h2
    exact h2.symm

theorem differentiableOn_ev_prod : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (σ : k →+* ℂ) {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] (T : Set E) (U : X.Opens) (V : Y.Opens), IsAffineOpen U → IsAffineOpen V →
  ∀ (s₁ : E → CxPts f σ) (s₂ : E → CxPts g σ) (s : E → CxPts (pullback.fst f g ≫ f) σ),
  (∀ v, (s v).1 ≫ pullback.fst f g = (s₁ v).1) → (∀ v, (s v).1 ≫ pullback.snd f g = (s₂ v).1) →
  (∀ v ∈ T, s₁ v ∈ ptsIn f σ U) → (∀ v ∈ T, s₂ v ∈ ptsIn g σ V) →
  (∀ a : Γ(X, U), DifferentiableOn ℂ (CxPts.ev f σ U a ∘ s₁) T) →
  (∀ b : Γ(Y, V), DifferentiableOn ℂ (CxPts.ev g σ V b ∘ s₂) T) →
  IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) ∧
  (∀ v ∈ T, s v ∈ ptsIn (pullback.fst f g ≫ f) σ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) ∧
  ∀ t : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V),
    DifferentiableOn ℂ (CxPts.ev (pullback.fst f g ≫ f) σ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) t ∘ s) T := by
  intro k _ X Y f g σ E _ _ T U V hU hV s₁ s₂ s h₁ h₂ m₁ m₂ d₁ d₂
  have H := IsPullback.of_hasPullback f g
  obtain ⟨hW, po⟩ := GlobalTheory.Conormal.isAffineOpen_and_isPushout H (U := ⊤) (T₀ := V) (W := U)
    (isAffineOpen_top _) hV hU le_top le_top
  have hin : ∀ v ∈ T, s v ∈ ptsIn (pullback.fst f g ≫ f) σ
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := fun v hv =>
    mem_ptsIn_inf.2 ⟨mem_ptsIn_preimage (h₁ v) (m₁ v hv), mem_ptsIn_preimage (h₂ v) (m₂ v hv)⟩
  refine ⟨hW, hin, fun t => ?_⟩
  have ht : t ∈ Subring.closure (Set.range (pullback.fst f g |>.appLE U
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_left).hom ∪
      Set.range (pullback.snd f g |>.appLE V
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_right).hom) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout po]
    trivial
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact (d₁ a).congr fun v hv => ev_appLE (h₁ v) _ (hin v hv) a
    · exact (d₂ b).congr fun v hv => ev_appLE (h₂ v) _ (hin v hv) b
  | zero =>
    exact (differentiableOn_const 0).congr fun v hv => by
      simp only [Function.comp_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_zero]
  | one =>
    exact (differentiableOn_const 1).congr fun v hv => by
      simp only [Function.comp_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_one]
  | add x y _ _ hx hy =>
    exact (hx.add hy).congr fun v hv => by
      simp only [Function.comp_apply, Pi.add_apply, GlobalTheory.CxPts.ev_add]
  | neg x _ hx =>
    exact hx.neg.congr fun v hv => by
      simp only [Function.comp_apply, Pi.neg_apply, GlobalTheory.CxPts.ev_eq (hin v hv), map_neg]
  | mul x y _ _ hx hy =>
    exact (hx.mul hy).congr fun v hv => by
      simp only [Function.comp_apply, Pi.mul_apply, GlobalTheory.CxPts.ev_mul]

end GlobalTheory.CompanionTheory.Ar.ProdHolo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesContinuationStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_continuation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧ ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  first | exact @GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane | exact GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane | (intros; apply GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane <;> assumption)
end

