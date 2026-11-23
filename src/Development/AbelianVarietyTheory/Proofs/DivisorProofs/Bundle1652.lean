module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDifferentLatticeProductHermitianIsSelfDual
section
noncomputable section

open NumberField
open scoped Pointwise

namespace GlobalTheory.VacRead.SelfDual

open GlobalTheory.InertSign (IntE hE)

theorem intE_iff {D : Formalism.BasicNotions.D7} {e : D.host.E} : IntE D e ↔ e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := Iff.rfl

theorem intE_gen (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {α₁ α₂ γ₁ γ₂ : D.host.E} (hα₁ : α₁ ∈ cE D cc) (hα₂ : α₂ ∈ cE D cc)
    (hγ₁ : γ₁ ∈ cE D D.host.ccK) (hγ₂ : γ₂ ∈ cE D D.host.ccK) :
    IntE D (r * D.host.conj α₁ * γ₁ / (Ideal.absNorm cc : D.host.E) *
      D.host.conj (r * D.host.conj α₂ * γ₂ / (Ideal.absNorm cc : D.host.E))) := by
  obtain ⟨o₁, h₁⟩ := (_root_.GlobalTheory.VacRead.conj_mul_cE_absNorm D cc).1 α₁ hα₁ α₂ hα₂
  obtain ⟨o₂, h₂⟩ := (_root_.GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).1 γ₂ hγ₂ γ₁ hγ₁
  unfold GlobalTheory.NormExact.IsScale at hs
  refine ⟨o₁ * o₂, ?_⟩
  simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj]
  change (o₁ : D.host.E) * (o₂ : D.host.E) = _
  field_simp
  linear_combination (exp := 1) (-(r * D.host.conj r) * (D.host.conj γ₂ * γ₁)) * h₁ +
    (-(r * D.host.conj r) * (Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E)) * h₂ +
    (-((Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E) * (o₂ : D.host.E))) * hs

def pairSpan (D : Formalism.BasicNotions.D7) (J : Submodule (𝓞 D.host.E) D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ u ∈ J, ∃ x ∈ J, t = u * D.host.conj x}

theorem conj_smul (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) (x : D.host.E) :
    D.host.conj (c • x) = D.host.conj (c : D.host.E) * D.host.conj x := by
  rw [Algebra.smul_def, map_mul]

theorem intE_coe (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) : IntE D (c : D.host.E) := ⟨c, rfl⟩

theorem intE_mul_conj (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {u x : D.host.E} (hu : u ∈ bInv D cc r) (hx : x ∈ bInv D cc r) :
    IntE D (u * D.host.conj x) := by
  unfold bInv at hu hx
  induction hu using Submodule.span_induction generalizing x with
  | mem g hg =>
    obtain ⟨α₁, hα₁, γ₁, hγ₁, rfl⟩ := hg
    induction hx using Submodule.span_induction with
    | mem g' hg' =>
      obtain ⟨α₂, hα₂, γ₂, hγ₂, rfl⟩ := hg'
      exact intE_gen D cc r hn hs hα₁ hα₂ hγ₁ hγ₂
    | zero => rw [map_zero, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _), mul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [conj_smul, mul_left_comm]
      exact mul_mem (GlobalTheory.InertSign.IntE.conj (intE_coe D c)) hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact add_mem (hy hx) (hz hx)
  | smul c y _ hy =>
    rw [Algebra.smul_def, mul_assoc]
    exact mul_mem (intE_coe D c) (hy hx)

theorem one_mem_pairSpan (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    (1 : D.host.E) ∈ pairSpan D (bInv D cc r) := by
  have h₁ := (_root_.GlobalTheory.VacRead.conj_mul_cE_absNorm D cc).2
  have h₂ := (_root_.GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).2
  have hm := Submodule.mul_mem_mul h₁ h₂
  rw [Submodule.span_mul_span] at hm
  set c : D.host.E := r * D.host.conj r / (Ideal.absNorm cc : D.host.E) ^ 2 with hc
  have hle : Submodule.span (𝓞 D.host.E) ({t | ∃ α ∈ cE D cc, ∃ β ∈ cE D cc, t = D.host.conj α * β} *
      {t | ∃ α ∈ cE D D.host.ccK, ∃ β ∈ cE D D.host.ccK, t = D.host.conj α * β}) ≤
      (pairSpan D (bInv D cc r)).comap (LinearMap.mulLeft (𝓞 D.host.E) c) := by
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨α, hα, β, hβ, rfl⟩, _, ⟨γ, hγ, ε, hε, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨r * D.host.conj α * ε / (Ideal.absNorm cc : D.host.E), ?_,
      r * D.host.conj β * γ / (Ideal.absNorm cc : D.host.E), ?_, ?_⟩
    · unfold bInv; exact Submodule.subset_span ⟨α, hα, ε, hε, rfl⟩
    · unfold bInv; exact Submodule.subset_span ⟨β, hβ, γ, hγ, rfl⟩
    · simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj, hc]
      field_simp
  have h := hle hm
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h
  convert h using 1
  unfold GlobalTheory.NormExact.IsScale at hs
  rw [hc]
  field_simp
  linear_combination -hs

theorem mem_of_dual (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) {y : D.host.E}
    (hy : ∀ x ∈ bInv D cc r, IntE D (y * D.host.conj x)) : y ∈ bInv D cc r := by
  have hle : pairSpan D (bInv D cc r) ≤ (bInv D cc r).comap (LinearMap.mulLeft (𝓞 D.host.E) y) := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    obtain ⟨o, ho⟩ := hy x hx
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    have : y * (u * D.host.conj x) = o • u := by rw [Algebra.smul_def, ho]; ring
    rw [this]
    exact Submodule.smul_mem _ o hu
  have h := hle (one_mem_pairSpan D cc r hn hs)
  simpa only [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_one] using h

theorem exists_ne_zero (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    ∃ x ∈ bInv D cc r, x ≠ 0 := by
  by_contra hne
  push_neg at hne
  have hle : pairSpan D (bInv D cc r) ≤ ⊥ := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    simp [hne u hu]
  have h := hle (one_mem_pairSpan D cc r hn hs)
  rw [Submodule.mem_bot] at h
  exact one_ne_zero h

theorem lsB_sd (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) (hcc : cc ≠ ⊥)
    (hs : GlobalTheory.NormExact.IsScale D cc r) : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r a) := by
  have hn : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hcc)
  have hsingle : ∀ (i : Fin a) (u : D.host.E), u ∈ bInv D cc r → (Pi.single i u : Fin a → D.host.E) ∈ lsB D cc r a := by
    intro i u hu
    rw [mem_lsB]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hu
    · simp only [Pi.single_apply, hj, if_false]; exact zero_mem _
  rw [GlobalTheory.InertSign.sd_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x₀, hx₀, hne⟩ := exists_ne_zero D cc r hn hs
    have hcne : D.host.conj x₀ ≠ 0 := (map_ne_zero_iff _ D.host.conj.injective).mpr hne
    let M := Submodule.span (𝓞 D.host.E)
      (Set.range fun i : Fin a => (Pi.single i (D.host.conj x₀)⁻¹ : Fin a → D.host.E))
    have hM : M.FG := Submodule.fg_span (Set.finite_range _)
    haveI := isNoetherian_of_fg_of_noetherian M hM
    refine Submodule.FG.of_le_of_isNoetherian (T := M) ?_
    intro y hy
    rw [mem_lsB] at hy
    rw [pi_eq_sum_univ' y]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨o, ho⟩ := intE_mul_conj D cc r hn hs (hy i) hx₀
    have he : y i • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) = o • Pi.single i (D.host.conj x₀)⁻¹ := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def, ho]
        field_simp
      · simp [Pi.single_apply, hj]
    rw [he]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff]
    intro v _
    have he : ∀ i : Fin a, (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
        Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
      intro i
      have key : ∀ t ∈ pairSpan D (bInv D cc r), t • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
          Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
        intro t ht
        unfold pairSpan at ht
        induction ht using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨u, hu, x, hx, rfl⟩ := hg
          have hg' : (u * D.host.conj x) • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) =
              D.host.conj x • Pi.single i u := by
            funext j
            by_cases hj : j = i
            · subst hj; simp [mul_comm]
            · simp [Pi.single_apply, hj]
          rw [hg']
          exact Submodule.smul_mem _ _ (Submodule.subset_span (hsingle i u hu))
        | zero => rw [zero_smul]; exact zero_mem _
        | add s t _ _ hs' ht' => rw [add_smul]; exact add_mem hs' ht'
        | smul c t _ ht' => rw [smul_assoc]; exact Submodule.smul_of_tower_mem _ c ht'
      simpa using key 1 (one_mem_pairSpan D cc r hn hs)
    rw [pi_eq_sum_univ' v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  · intro y
    rw [mem_lsB]
    constructor
    · intro hy x hx
      rw [mem_lsB] at hx
      rw [intE_iff]
      unfold hE
      exact Subring.sum_mem _ fun i _ => intE_mul_conj D cc r hn hs (hy i) (hx i)
    · intro h i
      refine mem_of_dual D cc r hn hs fun x hx => ?_
      have h' := h (Pi.single i x) (hsingle i x hx)
      unfold hE at h'
      rwa [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
        Pi.single_eq_same] at h'

end GlobalTheory.VacRead.SelfDual

theorem GlobalTheory.VacRead.lsB_selfDual : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → Formalism.MainNotions.StandardLatticesGL3.SD D (GlobalTheory.VacRead.lsB D cc r a) :=
  fun D cc r a hcc hs => GlobalTheory.VacRead.SelfDual.lsB_sd D cc r a hcc hs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvSmulMemRationalHomLatticeScaledOfNormScale
section
noncomputable section

open NumberField

namespace GlobalTheory.VacRead

theorem int_of_mem_bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc) {y : D.host.E} (hy : y ∈ bInv D cc r) :
    GlobalTheory.InertSign.IntE D (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * y /
      (Ideal.absNorm D.host.ccK : D.host.E)) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  have hN : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hc
  have hcE : ((c : D.host.K) : D.host.E) ∈ cE D cc := Submodule.subset_span ⟨c, hcc, rfl⟩
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, hα, γ₂, hγ₂, rfl⟩ := hy
    obtain ⟨o₁, h₁⟩ := (_root_.GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).1 γ hγ γ₂ hγ₂
    obtain ⟨o₂, h₂⟩ := (_root_.GlobalTheory.VacRead.conj_mul_cE_absNorm D cc).1 α hα _ hcE
    refine ⟨o₁ * o₂, ?_⟩
    have e : D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * (r * D.host.conj α * γ₂ / (Ideal.absNorm cc : D.host.E)) /
        (Ideal.absNorm D.host.ccK : D.host.E) =
        (D.host.conj γ * γ₂ / (Ideal.absNorm D.host.ccK : D.host.E)) *
          (D.host.conj α * ((c : D.host.K) : D.host.E) / (Ideal.absNorm cc : D.host.E)) := by
      field_simp
    rw [e, h₁, h₂, mul_div_cancel_left₀ _ hN0, mul_div_cancel_left₀ _ hN]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]; ring⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o * u, ?_⟩
    rw [map_mul, hu, Algebra.smul_def]
    ring

theorem mul_mem_Iid (D : Formalism.BasicNotions.D7) {ε α : D.host.E} (hε : ε ∈ cE D D.host.ccK)
    (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) : ε * α ∈ GlobalTheory.InertSign.Iid D D.host.ccK := by
  induction hε using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c₀, hc₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨c₀, hc₀, α, hα, rfl⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ o hx

theorem smul_mem_homL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc)
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ / (Ideal.absNorm D.host.ccK : D.host.E)) • A ∈
      Formalism.MainNotions.TaylorLogMetric.homL D (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hA' := GlobalTheory.ThetaLatImage.mem_homL.1 hA
  have hint : ∀ i j, GlobalTheory.InertSign.IntE D (A i j) := by
    intro i j
    have h1 : Pi.single j (1 : D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a := by
      rw [GlobalTheory.ThetaLatImage.mem_stdL]
      intro k
      refine ⟨if k = j then 1 else 0, ?_⟩
      by_cases h : k = j
      · subst h; simp
      · simp [h]
    have h2 := GlobalTheory.ThetaLatImage.mem_stdL.1 (hA' _ h1) i
    have hcol : A.mulVec (Pi.single j 1) i = A i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rwa [hcol] at h2
  rw [GlobalTheory.ThetaLatImage.mem_homL]
  intro x hx
  rw [GlobalTheory.ThetaLatImage.mem_stdL]
  intro i
  have hy : A.mulVec x i ∈ bInv D cc r := by
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨o, ho⟩ := hint i j
    rw [← ho, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o (mem_lsB.1 hx j)
  have := int_of_mem_bInv D cc r hc hr hγ hcc hy
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  convert this using 1
  ring

theorem gen_mem_RL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {c : 𝓞 D.host.K} (hcc : c ∈ cc) {α : D.host.E} (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (r⁻¹ * (((c : D.host.K) : D.host.E) * α)) • A ∈
      GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  set X := r⁻¹ * (((c : D.host.K) : D.host.E) * α) with hX
  have key : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t | ∃ γ ∈ cE D D.host.ccK, ∃ ε ∈ cE D D.host.ccK,
      t = D.host.conj γ * ε},
      (t * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A ∈
        GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨γ, hγ, ε, hε, rfl⟩ := ht
      have e : (D.host.conj γ * ε * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A =
          (ε * α) • ((D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ /
            (Ideal.absNorm D.host.ccK : D.host.E)) • A) := by
        rw [smul_smul, hX]
        congr 1
        ring
      rw [e]
      exact Submodule.subset_span ⟨ε * α, mul_mem_Iid D hε hα, _, smul_mem_homL D cc r a d hc hr hγ hcc hA, rfl⟩
    | zero => rw [zero_mul, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [smul_mul_assoc, smul_assoc]; exact Submodule.smul_mem _ o hx
  have h := key _ (_root_.GlobalTheory.VacRead.conj_mul_cE_absNorm D D.host.ccK).2
  rwa [mul_inv_cancel_left₀ hN0] at h

theorem rl_div_scale : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → ∀ z ∈ GlobalTheory.InertSign.RL D cc (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d),
      r⁻¹ • z ∈ GlobalTheory.InertSign.RL D D.host.ccK (GlobalTheory.VacRead.lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  intro D cc r a d hc hs z hz
  have hr : r ≠ 0 := GlobalTheory.NormExact.IsScale.ne_zero hc hs
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    rw [smul_smul]
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨c, hcc, α, hα, rfl⟩ := ht
      exact gen_mem_RL D cc r a d hc hr hcc hα hA
    | zero => rw [mul_zero, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [mul_smul_comm, smul_assoc]; exact Submodule.smul_mem _ o hx
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

end GlobalTheory.VacRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSpanRaisingOperatorWordsLowestKType
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory

theorem kfin_span_raising_words_lowK : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧ ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} = ⊤ := by
  intro n ε H _ _ σ D E lam hHC hCh hDS hK
  obtain ⟨_, hKS, hne, hkill⟩ := _root_.GlobalTheory.HolDS.lowKSub_kMod n ε H σ D E lam hHC hCh hDS hK
  haveI : CompleteSpace H := hDS.1
  set L := (lowKSub ε lam σ).comap D.subtype with hL
  set S := Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
    ∃ x ∈ L, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} with hS
  have hstab : ∀ a b, ∀ x ∈ S, E a b x ∈ S := fun a b x hx =>
    _root_.GlobalTheory.HolDS.raisingSpan_stable n ε D E hK.gl L hKS hkill a b x hx
  have hLS : L ≤ S := by
    intro x hx
    apply Submodule.subset_span
    exact ⟨[], by simp, x, hx, by simp⟩
  rcases GlobalTheory.T.kFiniteModule_irreducible_of_irreducible_unitaryRep n ε H σ D E hDS.1 hDS.2.2.1 hDS.2.2.2.1 hK S hstab with h | h
  · exfalso
    apply hne
    exact le_bot_iff.mp (h ▸ hLS)
  · exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSizesOfStdKer
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows


set_option maxHeartbeats 800000 in
theorem kerSizes_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∀ CY CT : ℝ, GlobalTheory.CoreHt.HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → (∀ u, Real.log ((((I.rec7 l Z).mem u).A.T : ℕ) : ℝ) ≤ CT * (I.rec7 l Z).R.m * L.sc.L) → GlobalTheory.ColRows.KerSizes t W Del h0 CY CT := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta CY CT hH hX' hx hTa hlogT
  have hNum := _root_.GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord (I.rec7 l Z) L Del h0 hDel hEta
  have hSz := _root_.GlobalTheory.CoreHt.sizes_trueCols I hOk l Z L CY hH hX' hx hTa
  refine ⟨?_, ?_, hlogT⟩
  · obtain ⟨hX, -, hPr, -⟩ := hS
    cases t
    dsimp only at hX hPr W hW ⊢
    subst hX
    cases eq_of_heq hPr
    cases eq_of_heq hW
    exact hSz
  · intro u
    have h := _root_.GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec (I.rec7 l Z) L CY hH u
    unfold GlobalTheory.ColumnNormCompare.codeRec at h
    convert h using 1 <;> first | exact hNum.symm | exact HEq.rfl | rfl

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValueStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_idempotent_character_value : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {a' d : ℕ} (J : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl J),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    At (evFin F v) (((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
    ∀ (u₁ u₂ : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u₁ → At (evFin F v) u₂ →
      (u₁.map (piW t) = 0 → u₂.map (piW t) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (-u₂) (-u₁)) ∧
      (u₁.map (piW (t.comp σ)) = 0 → u₂.map (piW (t.comp σ)) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols u₂ u₁) := by
  first | exact @GlobalTheory.SwapAtPlace.swap_at_acts | exact GlobalTheory.SwapAtPlace.swap_at_acts | (intros; apply GlobalTheory.SwapAtPlace.swap_at_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorRightPartialPure
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

namespace GlobalTheory.DblEval.BlockSwap

theorem partR_pureA {F : Type} [Field F] [NumberField F] {κ κ' κ₁' : Type} [Fintype κ]
    [Fintype κ'] [Fintype κ₁']
    (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ) (he : IsLocOp e) :
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F),
      ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F), ∀ f : SInf F (κ ⊕ κ'),
        partR e (pureA F f g) = pureA F (P f) g₁ :=
  GlobalTheory.DblEval.BlockSwap.partR_of_partL e (_root_.GlobalTheory.DblEval.PartLStr.exists_partL_pureA e he)

end GlobalTheory.DblEval.BlockSwap
end

