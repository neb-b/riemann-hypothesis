module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
section
open Matrix Finset

noncomputable section

namespace GlobalTheory.UnitaryHighestWeightUnique

open PI.UpqRep GlobalTheory.UnitaryHighestWeight

open Matrix Finset in
theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.height_le {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ}
    (h : _root_.PI.UpqRep.CDom ε μ Λ) :
    ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x ≤ ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x ∧
      (∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x = ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x → Λ = μ) := by
  unfold _root_.PI.UpqRep.CDom at h
  obtain ⟨c, hc, h⟩ := h
  have key : ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x - ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x =
      ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    have hx : ∀ x, Λ x - μ x = (Λ - μ) x := fun x => rfl
    simp_rw [← mul_sub, hx, h]
    unfold _root_.PI.UpqRep.root
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_sub, Finset.sum_sub_distrib, mul_comm, mul_left_comm]
    ring
  have hterm : ∀ a b : Fin n, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have hab := (hc a b h0).1
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hrow : ∀ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    fun a => Finset.sum_nonpos fun b _ => hterm a b
  have hsum : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => hrow a
  refine ⟨by linarith, fun heq => ?_⟩
  have hzero : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) = 0 := by
    linarith
  have hc0 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have hab := (hc a b h0).1
    have hlt : ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) < 0 := by
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      exact mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero h0) (by linarith)
    have ha := (Finset.sum_eq_zero_iff_of_nonpos fun a _ => hrow a).1 hzero a (Finset.mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonpos fun b _ => hterm a b).1 ha b (Finset.mem_univ b)
    linarith
  have : Λ - μ = 0 := by simp [h, hc0]
  exact sub_eq_zero.mp this


open Matrix Finset in
theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest {k : ℕ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} {Λ : Fin k → ℝ}
    (hπ : _root_.PI.UpqRep.IsURepOn (_root_.PI.UpqRep.UJset (_root_.PI.UpqRep.allPos k)) π) (hK : _root_.PI.UpqRep.IsKTypeOf (_root_.PI.UpqRep.allPos k) π Λ ⊤) :
    ∃ E : Fin k → Fin k → Module.End ℂ W, _root_.Formalism.REAL.GlRel E ∧
      (∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
        HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0) ∧
      (∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, E a b x ∈ S) → S = ⊥ ∨ S = ⊤) ∧
      ∃ x, x ≠ 0 ∧ _root_.Formalism.REAL.IsHW E (fun a => (Λ a : ℂ)) x := by
  obtain ⟨E, hrel, -, hder⟩ := _root_.GlobalTheory.UnitaryDerived.exists_derived_action k W π hπ
  unfold _root_.PI.UpqRep.IsKTypeOf at hK
  obtain ⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hK
  refine ⟨E, hrel, hder, ?_, v, hv0, ?_⟩
  · intro S hS
    have hSπ : _root_.PI.UpqRep.IsKStableOn (_root_.PI.UpqRep.allPos k) π S := by
      unfold _root_.PI.UpqRep.IsKStableOn
      intro g hg w hw
      exact _root_.GlobalTheory.UnitaryHighestWeight.stable_of_derived hπ E hder S
        (by unfold _root_.Formalism.REAL.KStable; exact fun a b _ x hx => hS a b x hx) g
        ((_root_.GlobalTheory.UnitaryHighestWeight.mem_K_iff g).1 hg) w hw
    exact hirr S le_top hSπ
  · have hvE : _root_.Formalism.REAL.IsWeight E Λ v := _root_.GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E hder Λ v hvw
    unfold _root_.Formalism.REAL.IsWeight at hvE
    unfold _root_.Formalism.REAL.IsHW
    refine ⟨fun a => hvE a, fun a b hab => ?_⟩
    by_contra hne
    unfold _root_.Formalism.REAL.GlRel at hrel
    have hw : _root_.Formalism.REAL.IsWeight E (Λ + _root_.PI.UpqRep.root a b) (E a b v) := by
      unfold _root_.Formalism.REAL.IsWeight
      intro c
      have hc := congrArg (fun T : Module.End ℂ W => T v) (hrel c c a b)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
      have hsplit : E c c (E a b v) = E a b (E c c v) +
          ((if c = a then E c b else 0) - if b = c then E a c else 0) v := by
        rw [LinearMap.sub_apply, ← hc]; abel
      rw [hsplit, hvE c, map_smul]
      unfold _root_.PI.UpqRep.root
      by_cases hca : c = a
      · subst hca
        have hcb : b ≠ c := ne_of_gt hab
        simp [hcb, Ne.symm hcb, add_smul, add_comm]
      · by_cases hcb : b = c
        · subst hcb
          simp [hca, Ne.symm hca, add_smul, sub_eq_add_neg, add_comm]
        · simp [hca, hcb, Ne.symm hcb]
    have ht := _root_.GlobalTheory.UnitaryHighestWeight.isWtOn_of_isWeight hπ E hder _ _ hw
    have hD := hdom _ (E a b v) Submodule.mem_top hne ht
    have hle := (_root_.GlobalTheory.UnitaryHighestWeightUnique.height_le hD).1
    have hcomp : ∑ x : Fin k, ((x : ℕ) : ℝ) * (Λ + _root_.PI.UpqRep.root a b) x =
        ∑ x : Fin k, ((x : ℕ) : ℝ) * Λ x + (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
      unfold _root_.PI.UpqRep.root
      simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith


open Matrix Finset in
theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.intertwine_group {W₁ W₂ : Type} [NormedAddCommGroup W₁]
    [InnerProductSpace ℂ W₁] [NormedAddCommGroup W₂] [InnerProductSpace ℂ W₂]
    [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
    (U₁ : ℝ → W₁ →L[ℂ] W₁) (A₁ : W₁ →ₗ[ℂ] W₁) (h₁ : ∀ v, U₁ 0 v = v)
    (hadd₁ : ∀ s t v, U₁ (s + t) v = U₁ s (U₁ t v)) (hd₁ : ∀ v, HasDerivAt (fun t => U₁ t v) (A₁ v) 0)
    (U₂ : ℝ → W₂ →L[ℂ] W₂) (A₂ : W₂ →ₗ[ℂ] W₂) (h₂ : ∀ v, U₂ 0 v = v)
    (hadd₂ : ∀ s t v, U₂ (s + t) v = U₂ s (U₂ t v)) (hd₂ : ∀ v, HasDerivAt (fun t => U₂ t v) (A₂ v) 0)
    (T : W₁ →ₗ[ℂ] W₂) (hT : ∀ v, T (A₁ v) = A₂ (T v)) (v : W₁) (t : ℝ) :
    T (U₁ t v) = U₂ t (T v) := by
  let Tc : W₁ →L[ℝ] W₂ := (LinearMap.toContinuousLinearMap T).restrictScalars ℝ
  let Ac : W₂ →L[ℝ] W₂ := (LinearMap.toContinuousLinearMap A₂).restrictScalars ℝ
  have hTc : ∀ x, Tc x = T x := fun x => rfl
  have hAc : ∀ x, Ac x = A₂ x := fun x => rfl
  have hf : ∀ s, HasDerivAt (fun s => T (U₁ s v)) (Ac (T (U₁ s v))) s := by
    intro s
    have h := _root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₁ A₁ hadd₁ hd₁ v s
    have h' := Tc.hasFDerivAt.comp_hasDerivAt s h
    simp only [Function.comp_def, hTc] at h'
    rwa [hAc, ← hT]
  have hg : ∀ s, HasDerivAt (fun s => U₂ s (T v)) (Ac (U₂ s (T v))) s := by
    intro s
    rw [hAc]
    exact _root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₂ A₂ hadd₂ hd₂ (T v) s
  have heq := ODE_solution_unique_univ (v := fun _ => Ac) (s := fun _ => Set.univ)
    (K := ‖Ac‖₊) (t₀ := 0) (fun _ => Ac.lipschitz.lipschitzOnWith)
    (fun s => ⟨hf s, Set.mem_univ _⟩) (fun s => ⟨hg s, Set.mem_univ _⟩) (by simp [h₁, h₂])
  exact congrFun heq t


open Matrix Finset in
theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU : ∀ (k : ℕ) (u : Fin k → ℝ)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁))
    (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), _root_.Formalism.MainNotions.S.IsHCTypeU k u π₁ → _root_.Formalism.MainNotions.S.IsHCTypeU k u π₂ →
    ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  intro k u H₁ _ _ H₂ _ _ π₁ π₂ h₁ h₂
  have h₁' : _root_.PI.UpqRep.IsHCTypeU k u π₁ := h₁
  have h₂' : _root_.PI.UpqRep.IsHCTypeU k u π₂ := h₂
  unfold _root_.PI.UpqRep.IsHCTypeU at h₁' h₂'
  obtain ⟨hnt₁, hfd₁, hπ₁, hK₁⟩ := h₁'
  obtain ⟨hnt₂, hfd₂, hπ₂, hK₂⟩ := h₂'
  obtain ⟨E₁, hrel₁, hder₁, hirr₁, x₁, hx₁, hw₁⟩ :=
    _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₁ hK₁
  obtain ⟨E₂, hrel₂, hder₂, hirr₂, x₂, hx₂, hw₂⟩ :=
    _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₂ hK₂
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.exists_linearEquiv_of_irreducible_isHW H₁ H₂ k E₁ E₂ _ x₁ x₂ hrel₁ hrel₂
    hirr₁ hirr₂ hw₁ hw₂ hx₁ hx₂
  refine ⟨T, fun g hg x => ?_⟩
  have hL : _root_.Formalism.REAL.Jm (_root_.PI.UpqRep.allPos k) = 1 := by
    unfold _root_.Formalism.REAL.Jm _root_.PI.UpqRep.allPos
    simp
  have hgL : g ∈ _root_.Formalism.REAL.Kset (_root_.PI.UpqRep.allPos k) := by
    unfold _root_.Formalism.REAL.Kset
    simp only [hL, mul_one, one_mul, and_true]
    exact hg
  obtain ⟨Y, hY, hexp, -⟩ := _root_.Formalism.REAL.compact_exists_log_bounded _ g hgL
  have hskew : Yᴴ = -Y := by
    unfold _root_.Formalism.REAL.inK _root_.Formalism.REAL.inG at hY
    rw [hL] at hY
    simp only [mul_one, one_mul, and_true] at hY
    exact eq_neg_of_add_eq_zero_left hY
  let A₁ : H₁ →ₗ[ℂ] H₁ := ∑ a, ∑ b, Y a b • E₁ a b
  let A₂ : H₂ →ₗ[ℂ] H₂ := ∑ a, ∑ b, Y a b • E₂ a b
  have hA₁ : ∀ v, A₁ v = ∑ a, ∑ b, Y a b • E₁ a b v := by
    intro v; simp [A₁, LinearMap.sum_apply]
  have hA₂ : ∀ v, A₂ v = ∑ a, ∑ b, Y a b • E₂ a b v := by
    intro v; simp [A₂, LinearMap.sum_apply]
  have hTA : ∀ v, T.toLinearMap (A₁ v) = A₂ (T.toLinearMap v) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hA₁, hA₂, map_sum, map_smul, hT]
  have key := _root_.GlobalTheory.UnitaryHighestWeightUnique.intertwine_group
    (fun t : ℝ => π₁ (NormedSpace.exp ((t : ℂ) • Y))) A₁
    (fun v => _root_.GlobalTheory.UnitaryHighestWeight.group_zero hπ₁ Y v)
    (fun s t v => _root_.GlobalTheory.UnitaryHighestWeight.group_add hπ₁ hskew s t v)
    (fun v => by rw [hA₁]; exact hder₁ Y hskew v)
    (fun t : ℝ => π₂ (NormedSpace.exp ((t : ℂ) • Y))) A₂
    (fun v => _root_.GlobalTheory.UnitaryHighestWeight.group_zero hπ₂ Y v)
    (fun s t v => _root_.GlobalTheory.UnitaryHighestWeight.group_add hπ₂ hskew s t v)
    (fun v => by rw [hA₂]; exact hder₂ Y hskew v)
    T.toLinearMap hTA x 1
  simpa [hexp] using key

end GlobalTheory.UnitaryHighestWeightUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.SmoothLowType

open Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.GardingVec

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_bump (n : ℕ) (ε : Fin n → Bool) (U : Set (UJ ε)) (hU : U ∈ nhds (1 : UJ ε)) :
    ∃ a : Matrix (Fin n) (Fin n) ℂ → ℝ,
      (∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (f : P → Matrix (Fin n) (Fin n) ℂ),
        (∀ i j, ContDiff ℝ ∞ fun p => f p i j) → ContDiff ℝ ∞ fun p => a (f p)) ∧ (∀ y, 0 ≤ a y) ∧ a 1 ≠ 0 ∧
      HasCompactSupport (fun g : UJ ε => a (umat g)) ∧ (∀ g : UJ ε, a (umat g) ≠ 0 → g ∈ U) ∧
      ∀ k ∈ Kset ε, ∀ y, a (k * y) = a (y * k) := by
  obtain ⟨a, ha, h⟩ := GlobalTheory.exists_conjInvariant_bump n ε U hU
  refine ⟨a, fun P _ _ f hf => ha.comp ?_, h⟩
  exact contDiff_pi.2 fun i => contDiff_pi.2 fun j => hf i j
end

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => x i j := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem garding_smooth {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {φ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψc : HasCompactSupport fun g : UJ ε => φ (umat g)) (w : H)
    (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ) (hx : ContDiff ℝ ∞ x) (hxG : ∀ t, x t ∈ UJset ε) :
    ContDiff ℝ ∞ fun t => σ (x t) (∫ g : UJ ε, φ (umat g) • σ (umat g) w ∂(muG ε)) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  set μ := Formalism.REAL.muG ε
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w := (hcont w).comp_continuous hu hmem
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hu
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • σ (umat g) w) μ :=
    (hψ.smul hb).integrable_of_hasCompactSupport hψc.smul_right
  let y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => Formalism.REAL.Jm ε * (x t)ᴴ * Formalism.REAL.Jm ε
  have hy : ContDiff ℝ ∞ y := (contDiff_const.mul (contDiff_conjTranspose.comp hx)).mul contDiff_const
  have hyx : ∀ t, y t * x t = 1 := fun t => by
    have h : (x t)ᴴ * Formalism.REAL.Jm ε * x t = Formalism.REAL.Jm ε := hxG t
    calc y t * x t = Formalism.REAL.Jm ε * ((x t)ᴴ * Formalism.REAL.Jm ε * x t) := by simp only [y, Matrix.mul_assoc]
      _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]
  have hxy : ∀ t, x t * y t = 1 := fun t => mul_eq_one_comm.1 (hyx t)
  have hz : ∀ t, ∃ z : UJ ε, umat z = x t := fun t => by
    have : x t ∈ Set.range (fun g : Formalism.REAL.UJ ε => umat g) := by
      rw [show Set.range (fun g : Formalism.REAL.UJ ε => umat g) = _ from hrange]; exact hxG t
    exact this
  have hform : ∀ t, σ (x t) (∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ)
      = ∫ g : Formalism.REAL.UJ ε, φ (y t * umat g) • σ (umat g) w ∂μ := by
    intro t
    obtain ⟨z, hz'⟩ := hz t
    rw [← ContinuousLinearMap.integral_comp_comm _ hint,
      ← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => φ (y t * umat g) • σ (umat g) w) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = x t * umat g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul, hmul _ (hxG t) _ (hmem g),
      ContinuousLinearMap.map_smul_of_tower]
    rfl
  simp only [hform]
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  have hC : IsCompact (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1)
      ((fun g : UJ ε => umat g) '' tsupport fun g : UJ ε => φ (umat g))) :=
    ((isCompact_closedBall t₀ 1).image hx.continuous).mul (IsCompact.image hψc hu)
  have hK := hemb.isCompact_preimage hC
  have hs : ContDiff ℝ ∞ fun t => ∫ g in (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹'
      (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1)
        ((fun g : UJ ε => umat g) '' tsupport fun g : UJ ε => φ (umat g))),
      φ (y t * umat g) • σ (umat g) w ∂μ :=
    contDiff_infty.2 fun m => contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
      (fun z : (Fin k → ℝ) × (Matrix (Fin n) (Fin n) ℂ × H) => φ (y z.1 * z.2.1) • z.2.2)
      ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
        (contDiff_snd.comp contDiff_snd))
  refine hs.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with t ht
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
  by_contra hne
  obtain ⟨z, hz'⟩ := hz t
  have e : x t * umat (z⁻¹ * g) = umat g := by
    rw [← hz']
    show umat (z * (z⁻¹ * g)) = _
    rw [mul_inv_cancel_left]
  have e' : umat (z⁻¹ * g) = y t * umat g := by
    rw [← e, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  refine hg ⟨x t, ⟨t, ht, rfl⟩, umat (z⁻¹ * g), ⟨z⁻¹ * g, subset_tsupport _ fun h => hne ?_, rfl⟩, e⟩
  have h' : φ (umat (z⁻¹ * g)) = 0 := h
  rw [← e', h', zero_smul]

theorem exists_smooth_ktype {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hK : IsKTypeOf ε σ Λ S) :
    ∃ S' : Submodule ℂ H, IsKTypeOf ε σ Λ S' ∧ ∀ v ∈ S', ∀ (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ),
      ContDiff ℝ ∞ x → (∀ t, x t ∈ UJset ε) → ContDiff ℝ ∞ fun t => σ (x t) v := by
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  haveI := hK.1
  obtain ⟨v, hvS, hv0, -⟩ := hK.2.2.2.1
  have humat : Continuous (fun g : UJ ε => umat g) := (isClosedEmbeddingMatrix n ε).1.continuous
  have hcont : ∀ s : H, Continuous (fun g : UJ ε => σ (umat g) s) := fun s =>
    (hσ.2.2 s).comp_continuous humat (fun g => g.2)
  have hre : Continuous (fun g : UJ ε => (⟪v, σ (umat g) v⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner (hcont v))
  have hone : 0 < (⟪v, σ (umat (1 : UJ ε)) v⟫_ℂ).re := by
    have : σ (umat (1 : UJ ε)) = 1 := hσ.1.1
    rw [this]
    exact re_inner_self_pos (𝕜 := ℂ).2 hv0
  obtain ⟨a, ha', ha0, ha1, hac, haU, haK⟩ := exists_bump n ε
    {g | 0 < (⟪v, σ (umat g) v⟫_ℂ).re} ((isOpen_lt continuous_const hre).mem_nhds hone)
  have ha : ContDiff ℝ ∞ a := ha' _ (fun p => p) contDiff_entry
  have hacont : Continuous (fun g : UJ ε => a (umat g)) := ha.continuous.comp humat
  have hacC : Continuous (fun g : UJ ε => (a (umat g) : ℂ)) := Complex.continuous_ofReal.comp hacont
  have hsuppC : HasCompactSupport (fun g : UJ ε => (a (umat g) : ℂ)) :=
    hac.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hint : ∀ s : H, Integrable (fun g : UJ ε => (a (umat g) : ℂ) • σ (umat g) s) (muG ε) :=
    fun s => (hacC.smul (hcont s)).integrable_of_hasCompactSupport hsuppC.smul_right
  let T : S →ₗ[ℂ] H :=
    { toFun := fun s => ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)
      map_add' := by
        intro s t
        rw [← integral_add (hint s) (hint t)]
        simp only [Submodule.coe_add, map_add (f := _), smul_add]
      map_smul' := by
        intro c s
        rw [RingHom.id_apply, ← integral_smul]
        simp only [Submodule.coe_smul, map_smul, smul_comm c] }
  have hT : ∀ (s : S) (u : H), ⟪u, T s⟫_ℂ =
      ∫ g : UJ ε, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro s u
    show ⟪u, ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε)⟫_ℂ = _
    rw [← integral_inner (hint s)]
    simp only [inner_smul_right]
  refine ⟨_, GlobalTheory.Dec.FormF.rangeType n ε Λ H σ S H σ (LinearMap.toContinuousLinearMap T) hK ?_ ?_, ?_⟩
  · intro k hk s s' hs'
    have hu : k ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact (maximal_compact_facts n ε).1 k hk
    obtain ⟨κ, rfl⟩ := hu
    show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s' ∂(muG ε) =
      σ (umat κ) (∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hint s), hs']
    have e1 : ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) (σ (umat κ) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_right_eq_self
        (fun g : UJ ε => (a (umat (g * κ⁻¹)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (g * κ)) = _ := hσ.1.2 (umat g) g.2 (umat κ) κ.2
      rw [this, mul_inv_cancel_right]
      rfl
    have e2 : ∫ g : UJ ε, σ (umat κ) ((a (umat g) : ℂ) • σ (umat g) s) ∂(muG ε) =
        ∫ g : UJ ε, (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) s ∂(muG ε) := by
      rw [← integral_mul_left_eq_self
        (fun g : UJ ε => (a (umat (κ⁻¹ * g)) : ℂ) • σ (umat g) (s : H)) κ]
      congr 1
      funext g
      have : σ (umat (κ * g)) = _ := hσ.1.2 (umat κ) κ.2 (umat g) g.2
      rw [this, inv_mul_cancel_left, map_smul]
      rfl
    refine e1.trans (Eq.trans ?_ e2.symm)
    congr 1
    funext g
    have hk' : umat κ⁻¹ ∈ Kset ε := (KG ε).inv_mem (x := κ) hk
    have : a (umat (κ⁻¹ * g)) = a (umat (g * κ⁻¹)) := haK _ hk' (umat g)
    rw [this]
  · intro h0
    have hc : T ⟨v, hvS⟩ = 0 := congrArg (fun f : S →L[ℂ] H => f ⟨v, hvS⟩) h0
    have h1 := hT ⟨v, hvS⟩ v
    rw [hc, inner_zero_right] at h1
    have hi : Integrable (fun g : UJ ε => (a (umat g) : ℂ) * ⟪v, σ (umat g) v⟫_ℂ) (muG ε) :=
      (hacC.mul (continuous_const.inner (hcont v))).integrable_of_hasCompactSupport hsuppC.mul_right
    have h2 := congrArg Complex.re h1
    have h3 := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    rw [← h3] at h2
    have h4 : 0 < ∫ g : UJ ε, a (umat g) * (⟪v, σ (umat g) v⟫_ℂ).re ∂(muG ε) := by
      refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
        (hacont.mul hre) hac.mul_right ?_ (mul_ne_zero ha1 hone.ne')
      intro g
      by_cases h : a (umat g) = 0
      · simp [h]
      · exact mul_nonneg (ha0 _) (le_of_lt (haU g h))
    rw [← h2] at h4
    simp at h4
  · rintro _ ⟨s, rfl⟩ k x hx hxG
    have e : (T s : H) = ∫ g : UJ ε, a (umat g) • σ (umat g) (s : H) ∂(muG ε) := by
      show ∫ g : UJ ε, (a (umat g) : ℂ) • σ (umat g) s ∂(muG ε) = _
      simp only [Complex.coe_smul]
    show ContDiff ℝ ∞ fun t => σ (x t) (T s)
    rw [e]
    exact garding_smooth hσ ha hac s k x hx hxG

theorem exists_smoothVec_ktype {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hK : IsKTypeOf ε σ Λ S)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    ∃ S' : Submodule ℂ H, IsKTypeOf ε σ Λ S' ∧
      ∀ v ∈ S', Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v := by
  obtain ⟨S', hS', hs⟩ := exists_smooth_ktype hσ hK
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  refine ⟨S', hS', fun v hv k Xs hX =>
    hs v hv k _ ((contDiff_const.mul (contDiff_expProd Xs)).mul contDiff_const) fun t => ?_⟩
  refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact exp_mem hG (hX i) _

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_lowK_le_sm : ∀ (D : D7) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (τ : D.what₂.Tau),
    ∃ S : Submodule ℂ (M.H τ), IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S ∧ S ≤ M.sm τ := by
  intro D V Sp M τ
  obtain ⟨h1, h2, h3, -, -, ⟨S, hS⟩, -⟩ := M.ds τ
  obtain ⟨S', hS', hs⟩ := exists_smoothVec_ktype h3 hS (M.fr_unit τ) (M.fr_gram τ)
  exact ⟨S', hS', fun v hv => Submodule.subset_span (hs v hv)⟩

end GlobalTheory.SmoothLowType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryAdelicQuotientVolumeIsVolume
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem volIs_trueVol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → VolIs cm τ cd W (trueVol cm τ cd W) := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W hτ hW
  apply trueVol_spec
  obtain ⟨μ, hμ⟩ := _root_.GlobalTheory.Mem.VolExists.exists_isVolMeasF F E cm I τ cd W hτ hW
  obtain ⟨⟨𝓕, h𝓕⟩, hall⟩ := _root_.GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E cm.sig W.rank W.gram μ hμ.1
  have hcm := cmData_isCMExt_and_gram_isHermND F E cm
  have hfin : μ 𝓕 < ⊤ := _root_.GlobalTheory.Mem.VolFin.finVol F E cm.sig hcm.1 W.rank W.gram (hcm.2 W) μ hμ.1 𝓕 h𝓕
  have hne : μ 𝓕 ≠ 0 := (hall 𝓕 𝓕 h𝓕 h𝓕).2
  refine ⟨(μ 𝓕).toReal, ENNReal.toReal_pos hne hfin.ne, ⟨μ, hμ⟩, ?_⟩
  intro μ' hμ'
  have e : μ = μ' := GlobalTheory.Mem.VolUnique.volMeas_unique F E cm I τ cd W hτ hW μ μ' hμ hμ'
  subst e
  refine ⟨⟨𝓕, h𝓕⟩, fun 𝓕' h' => ?_⟩
  rw [ENNReal.ofReal_toReal hfin.ne]
  exact (hall 𝓕' 𝓕 h' h𝓕).1

end GlobalTheory.Mem.Vol
end

