module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0621
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0432
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0406
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0059
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSelfDualForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevel
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormRapidDecay
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology
noncomputable section

namespace GlobalTheory.CompanionTheory.RapidDecay

theorem decay_step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) {Ω : Set (GAd σ J)} (hΩ : IsCompact Ω)
    (hΩP : Ω ⊆ minParOne σ J X) {c : ℝ} (hc : 0 < c) {U : Subgroup (GAd σ J)} (hU : IsOpen (U : Set (GAd σ J))) (A e m : ℕ)
    (hm : ∀ ψ, Good σ J U A ψ → ∀ Cm : Set (GAd σ J), IsCompact Cm → ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ‖ψ (p * a * k)‖ * rbar t ^ m ≤ B * rbar t ^ e)
    (ψ : GAd σ J → ℂ) (hψ : Good σ J U A ψ) (Cm : Set (GAd σ J)) (hCm : IsCompact Cm) :
    ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm,
      ‖ψ (p * a * k)‖ * rbar t ^ (m + 1) ≤ B * rbar t ^ e := by
  obtain ⟨q, b, Ω₀, Cv, δ₁, hb, hΩ₀, hδ₁, hCv, hmv⟩ := _root_.GlobalTheory.CompanionTheory.RapidDecay.Mean.mean_value F E σ h n J hJ
  have hCm' : IsCompact ((fun x : GAd σ J × GAd σ J => x.1 * x.2) '' (Cm ×ˢ Ω₀)) :=
    (hCm.prod hΩ₀).image (by fun_prop)
  choose B hB using fun i => hm _ (_root_.GlobalTheory.CompanionTheory.RapidDecay.good_lineDer F E σ h n J hJ U A ψ (b i) hψ (hb i)) _ hCm'
  obtain ⟨B₀, hB₀⟩ := hm ψ hψ Cm hCm
  obtain ⟨M, hM0, hM⟩ := _root_.GlobalTheory.CompanionTheory.RapidDecay.near_cusp F E σ h n J hJ r X Y hW Ω Cm c U hΩ hΩP hCm hc hU
  set R₀ := max 1 (M / δ₁) with hR₀
  have hR1 : 1 ≤ R₀ := le_max_left _ _
  have hSum : 0 ≤ ∑ i, |B i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨R₀ * |B₀| + Cv * M * ∑ i, |B i|, fun p hp t ht a ha k hk => ?_⟩
  have hR := one_le_rbar t
  have hRpos : 0 < rbar t := by linarith
  have hRe : 0 < rbar t ^ e := pow_pos hRpos e
  have hRm : 0 < rbar t ^ m := pow_pos hRpos m
  have hT : 0 ≤ Cv * M * ∑ i, |B i| := mul_nonneg (mul_nonneg hCv hM0) hSum
  by_cases hcase : rbar t ≤ R₀
  · calc ‖ψ (p * a * k)‖ * rbar t ^ (m + 1) = rbar t * (‖ψ (p * a * k)‖ * rbar t ^ m) := by ring
      _ ≤ R₀ * (|B₀| * rbar t ^ e) := by
          refine mul_le_mul hcase ((hB₀ p hp t ht a ha k hk).trans ?_) (by positivity) (by linarith)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hRe.le
      _ ≤ _ := by
          rw [← mul_assoc, add_mul]
          exact le_add_of_nonneg_right (mul_nonneg hT hRe.le)
  · push Not at hcase
    have hne : rbar t ≠ 1 := fun e' => by
      rw [e'] at hcase; linarith
    obtain ⟨s, hs⟩ := (rbar_eq t).resolve_left hne
    have hδ : M / rbar t ≤ δ₁ := by
      rw [div_le_iff₀ hRpos]
      have h1 : M / δ₁ ≤ R₀ := le_max_right _ _
      rw [div_le_iff₀ hδ₁] at h1
      nlinarith
    set g := p * a * k with hg
    set cc : Fin q → ℝ := fun i => |B i| * rbar t ^ e / rbar t ^ m with hcc
    have hcc' : ∀ i, ∀ x ∈ Ω₀, ‖lineDer (b i) ψ (g * x)‖ ≤ cc i := fun i x hx => by
      have := hB i p hp t ht a ha (k * x) ⟨(k, x), ⟨hk, hx⟩, rfl⟩
      rw [show p * a * (k * x) = g * x by rw [hg, mul_assoc (p * a)]] at this
      rw [hcc, le_div_iff₀ hRm]
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hRe.le)
    have hvar : ‖ψ g‖ ≤ Cv * (M / rbar t) * ∑ i, cc i := by
      refine _root_.GlobalTheory.CompanionTheory.RapidDecay.norm_le_of_unipRad_variation F E σ h n J hJ ψ hψ.left hψ.cont hψ.cusp _ (pre X s) (Nat.succ_pos _)
        (GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ _) g _ fun m' hm' => ?_
      obtain ⟨γ, hγ, u, κ, hu, hκU, hκf, e'⟩ := hM p hp t ht a ha k hk s m' hm'
      rw [← hs] at hu
      have : ψ (m' * g) = ψ (g * u) := by
        rw [hg, e', hψ.level κ hκU hκf, mul_assoc γ, hψ.left γ hγ]
      rw [this]
      exact hmv ψ hψ.smooth g u _ (div_nonneg hM0 hRpos.le) hδ hu cc hcc'
    have hsum : ∑ i, cc i = (∑ i, |B i|) * rbar t ^ e / rbar t ^ m := by
      rw [hcc, Finset.sum_mul, Finset.sum_div]
    calc ‖ψ g‖ * rbar t ^ (m + 1) ≤ (Cv * (M / rbar t) * ∑ i, cc i) * rbar t ^ (m + 1) :=
          mul_le_mul_of_nonneg_right hvar (pow_pos hRpos _).le
      _ = (Cv * M * ∑ i, |B i|) * rbar t ^ e := by
          rw [hsum, pow_succ]
          field_simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hRe.le
          exact le_add_of_nonneg_left (by positivity)

theorem rapid_decrease : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ), IsCompact (K : Set (GAd σ J)) → IsCompact Ω → Ω ⊆ minParOne σ J X → 0 < c → ∀ φ : GAd σ J → ℂ, IsSmoothModerate σ J φ → IsCuspidal σ J φ → ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ siegelSet σ J X Y Ω c K, ‖φ g‖ * (height σ J g : ℝ) ^ N ≤ C := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW K Ω c hK hΩ hΩP hc φ hs hcu N
  obtain ⟨U, hU, hlev⟩ := hs.level
  obtain ⟨A, hA⟩ := hs.growth
  have hG : Good σ J U A φ := ⟨hs.left, hlev, hs.cont, hs.smooth, hA, hcu⟩
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.CompanionTheory.RapidDecay.height_le_rbar_pow F E σ h n J hJ r X Y hW c hc
  set e := b * A with he
  have hbase : ∀ ψ, Good σ J U A ψ → ∀ Cm : Set (GAd σ J), IsCompact Cm → ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ‖ψ (p * a * k)‖ * rbar t ^ 0 ≤ B * rbar t ^ e := fun ψ hψ Cm hCm => by
    obtain ⟨H, hH0, hH⟩ := hb Ω Cm hΩ hCm
    obtain ⟨C, hC⟩ := hψ.growth [] (by simp)
    refine ⟨|C| * H ^ A, fun p hp t ht a ha k hk => ?_⟩
    have h1 := hC (p * a * k)
    have h2 := hH p hp t ht a ha k hk
    have h3 : (0 : ℝ) ≤ (height σ J (p * a * k) : ℝ) := NNReal.coe_nonneg _
    simp only [List.foldr_nil] at h1
    rw [pow_zero, mul_one, he, pow_mul, mul_assoc |C|, ← mul_pow]
    exact h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg h3 _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 A) (abs_nonneg _)))
  have hall : ∀ m : ℕ, ∀ ψ, Good σ J U A ψ → ∀ Cm : Set (GAd σ J), IsCompact Cm → ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ‖ψ (p * a * k)‖ * rbar t ^ m ≤ B * rbar t ^ e := fun m => by
    induction m with
    | zero => exact hbase
    | succ m ih => exact fun ψ hψ Cm hCm => decay_step h hJ hW hΩ hΩP hc hU A e m ih ψ hψ Cm hCm
  obtain ⟨B, hB⟩ := hall (b * N + e) φ hG _ hK
  obtain ⟨H, hH0, hH⟩ := hb Ω K hΩ hK
  refine ⟨|B| * H ^ N, ?_⟩
  rintro _ ⟨p, hp, t, ht, a, ha, k, hk, rfl⟩
  have hR := one_le_rbar t
  have hRpos : 0 < rbar t := by linarith
  have h1 := hB p hp t ht a ha k hk
  have h2 := hH p hp t ht a ha k hk
  have h3 : (0 : ℝ) ≤ (height σ J (p * a * k) : ℝ) := NNReal.coe_nonneg _
  have h4 : ‖φ (p * a * k)‖ * rbar t ^ (b * N) ≤ |B| := by
    rw [pow_add, ← mul_assoc] at h1
    have h5 := h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos hRpos e).le)
    exact le_of_mul_le_mul_right h5 (pow_pos hRpos e)
  calc ‖φ (p * a * k)‖ * (height σ J (p * a * k) : ℝ) ^ N ≤ ‖φ (p * a * k)‖ * (H * rbar t ^ b) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 N) (norm_nonneg _)
    _ = (‖φ (p * a * k)‖ * rbar t ^ (b * N)) * H ^ N := by rw [mul_pow, pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 (pow_nonneg hH0 _)

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalLatticeIndexPow
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.LatDiag

variable {E : Type} [Field E] [NumberField E] {w : Pl E}

theorem unif_ne_zero {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  rintro rfl
  unfold IsUnifV at h
  rw [map_zero] at h
  exact WithZero.zero_ne_coe h

theorem unif_lt_one {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : Valued.v ϖ < 1 := by
  unfold IsUnifV at h
  rw [h]
  exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1)

theorem le_one_of_unif_mul {ϖ x : w.adicCompletion E} (h : IsUnifV E w ϖ)
    (hx : Valued.v (ϖ * x) < 1) : Valued.v x ≤ 1 := by
  unfold IsUnifV at h
  rw [map_mul, h] at hx
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · rw [h0]; exact zero_le
  obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp h0
  rw [← hm] at hx ⊢
  have h1 : Multiplicative.ofAdd (-1 : ℤ) * m < 1 := by exact_mod_cast hx
  have h2 : (-1 : ℤ) + Multiplicative.toAdd m < 0 := h1
  have h3 : m ≤ 1 := by
    show Multiplicative.toAdd m ≤ 0
    omega
  exact_mod_cast h3

theorem mem_max_iff (x : w.adicCompletionIntegers E) :
    x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ↔
      Valued.v (x : w.adicCompletion E) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx
    refine lt_of_le_of_ne x.2 fun h1 => hx ?_
    have hx0 : (x : w.adicCompletion E) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E := by
      show Valued.v (x : w.adicCompletion E)⁻¹ ≤ 1
      rw [map_inv₀, h1, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hx0))
  · intro hx hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have h1 : Valued.v (x : w.adicCompletion E) * Valued.v (y : w.adicCompletion E) = 1 := by
      rw [← map_mul]
      have : (x : w.adicCompletion E) * (y : w.adicCompletion E) = 1 := congrArg Subtype.val hy
      rw [this, map_one]
    have h2 : Valued.v (y : w.adicCompletion E) ≤ 1 := y.2
    have h3 := lt_of_le_of_lt (mul_le_of_le_one_right' h2) hx
    exact absurd h1 (ne_of_lt h3)

def posR {a i : ℕ} (hi : i ≤ a) (r : Fin i) : Fin a := Fin.castLE hi r

def posS {b j : ℕ} (s : Fin (b - j)) : Fin b := ⟨j + s, by have := s.2; omega⟩

theorem corner_mem {ϖ : w.adicCompletion E} {a b i j : ℕ} (hi : i ≤ a)
    (W : latD ϖ a b i j) (p : Fin i × Fin (b - j)) :
    ϖ * W.1 (posR hi p.1) (posS p.2) ∈ w.adicCompletionIntegers E := by
  have h := W.2 (posR hi p.1) (posS p.2)
  have hc : ((posR hi p.1 : Fin a) : ℕ) < i ∧ j ≤ ((posS p.2 : Fin b) : ℕ) :=
    ⟨p.1.2, Nat.le_add_right _ _⟩
  rw [if_pos hc] at h
  exact h

def cornerMap (ϖ : w.adicCompletion E) (a b i j : ℕ) (hi : i ≤ a) :
    latD ϖ a b i j →+
      (Fin i × Fin (b - j) → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) where
  toFun W p := IsLocalRing.residue _ ⟨_, corner_mem hi W p⟩
  map_zero' := by
    funext p
    have : (⟨_, corner_mem hi (0 : latD ϖ a b i j) p⟩ : w.adicCompletionIntegers E) = 0 :=
      Subtype.ext (by simp)
    simp only [this, map_zero, Pi.zero_apply]
  map_add' X Y := by
    funext p
    have : (⟨_, corner_mem hi (X + Y) p⟩ : w.adicCompletionIntegers E) =
        ⟨_, corner_mem hi X p⟩ + ⟨_, corner_mem hi Y p⟩ :=
      Subtype.ext (by simp [mul_add])
    simp only [this, map_add (f := _), Pi.add_apply]

theorem cornerMap_apply (ϖ : w.adicCompletion E) (a b i j : ℕ) (hi : i ≤ a) (W : latD ϖ a b i j)
    (p : Fin i × Fin (b - j)) :
    cornerMap ϖ a b i j hi W p = IsLocalRing.residue _ ⟨_, corner_mem hi W p⟩ := rfl

theorem ker_cornerMap {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (a b i j : ℕ) (hi : i ≤ a)
    (hj : j ≤ b) :
    (cornerMap ϖ a b i j hi).ker = (intSub a b w).addSubgroupOf (latD ϖ a b i j) := by
  ext W
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro hW r s
    have hWp : ∀ p : Fin i × Fin (b - j), Valued.v (ϖ * W.1 (posR hi p.1) (posS p.2)) < 1 := by
      intro p
      have := congrFun hW p
      rw [cornerMap_apply, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff] at this
      exact this
    by_cases hc : (r : ℕ) < i ∧ j ≤ (s : ℕ)
    · have := hWp (⟨r, hc.1⟩, ⟨s - j, by have := s.2; omega⟩)
      have hr : posR hi ⟨(r : ℕ), hc.1⟩ = r := Fin.ext rfl
      have hs : posS (j := j) (⟨(s : ℕ) - j, by have := s.2; omega⟩ : Fin (b - j)) = s :=
        Fin.ext (by simp [posS]; omega)
      simp only [hr, hs] at this
      exact le_one_of_unif_mul h this
    · have := W.2 r s
      rw [if_neg hc] at this
      exact this
  · intro hW
    funext p
    rw [cornerMap_apply, Pi.zero_apply, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
    show Valued.v (ϖ * W.1 (posR hi p.1) (posS p.2)) < 1
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hW _ _)) (unif_lt_one h)

theorem cornerMap_surjective {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (a b i j : ℕ)
    (hi : i ≤ a) (hj : j ≤ b) : Function.Surjective (cornerMap ϖ a b i j hi) := by
  intro c
  choose x hx using fun p => IsLocalRing.residue_surjective (c p)
  have h0 := unif_ne_zero h
  let M : Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun r s =>
    if hc : (r : ℕ) < i ∧ j ≤ (s : ℕ) then
      ϖ⁻¹ * (x (⟨r, hc.1⟩, ⟨s - j, by have := s.2; omega⟩) : w.adicCompletion E) else 0
  have hM : M ∈ latD ϖ a b i j := by
    intro r s
    by_cases hc : (r : ℕ) < i ∧ j ≤ (s : ℕ)
    · rw [if_pos hc]
      simp only [M, dif_pos hc]
      rw [mul_inv_cancel_left₀ h0]
      exact (x _).2
    · rw [if_neg hc]
      simp only [M, dif_neg hc]
      exact (Ov E w).zero_mem
  refine ⟨⟨M, hM⟩, ?_⟩
  funext p
  rw [cornerMap_apply, ← hx p]
  congr 1
  apply Subtype.ext
  have hc : ((posR hi p.1 : Fin a) : ℕ) < i ∧ j ≤ ((posS p.2 : Fin b) : ℕ) :=
    ⟨p.1.2, Nat.le_add_right _ _⟩
  show ϖ * M (posR hi p.1) (posS p.2) = _
  simp only [M, dif_pos hc]
  rw [mul_inv_cancel_left₀ h0]
  congr 2
  refine Prod.ext (Fin.ext rfl) (Fin.ext ?_)
  simp [posS]

theorem relIndex_intSub_latD (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (ϖ : w.adicCompletion E) (h : IsUnifV E w ϖ) (i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    (intSub a b w).relIndex (latD ϖ a b i j) = (qV E w) ^ (i * (b - j)) := by
  have hcard : Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) = qV E w := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue w]
    simp [qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [AddSubgroup.relIndex, ← ker_cornerMap h a b i j hi hj, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (cornerMap_surjective h a b i j hi hj), AddSubgroup.card_top,
    Nat.card_fun, hcard, Nat.card_prod, Nat.card_fin, Nat.card_fin]

end GlobalTheory.CompanionTheory.CtS.LatDiag
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexDegenerateColumnIso
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem row_iso_of_columns : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  intro R _ K a hK j
  have hab : ∀ p q, a < q → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_gt h)
  have hbe : ∀ p q, q < a → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_lt h)
  have hs := _root_.GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic K a j hab
  have hk := _root_.GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero K a j hab
  have hi := _root_.GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE K a j hbe
  have hl := GlobalTheory.T.double_complex_lead_surjective K a j hbe
  let c := clsZ K (a + j) j
  let ψ : Zf K (a + j) j →ₗ[R] (colH K a).H j := leadE K j a
  have hle : LinearMap.ker c ≤ LinearMap.ker ψ := fun z hz => hk z hz
  let L := (LinearMap.ker c).liftQ ψ hle
  have hL : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun x hx => ?_
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      have hz : ψ z = 0 := by simpa [L] using hx
      have hc : c z = 0 := hi z hz
      exact (Submodule.Quotient.mk_eq_zero _).2 hc
    · intro y
      obtain ⟨z, rfl⟩ := hl y
      exact ⟨Submodule.Quotient.mk z, Submodule.liftQ_apply _ _ _⟩
  let e0 := c.quotKerEquivOfSurjective hs
  refine ⟨e0.symm.trans (LinearEquiv.ofBijective L hL), fun z => ?_⟩
  have h0 : e0.symm (c z) = Submodule.Quotient.mk z :=
    e0.symm_apply_eq.2 (LinearMap.quotKerEquivOfSurjective_apply_mk c hs z).symm
  change L (e0.symm (c z)) = ψ z
  rw [h0]
  exact Submodule.liftQ_apply _ _ _

end GlobalTheory.CompanionTheory.CechSerre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTraceFromLocalInputs
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section
namespace GlobalTheory.CompanionTheory.EllTrace
open GlobalTheory.TruncKer

theorem countable_GF {D : D7} (V : HSp D) : Countable (GF V) := by
  haveI : Countable D.host.E :=
    (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
    (show Countable (Fin V.rank → Fin V.rank → D.host.E) from inferInstance)
  haveI : Countable (GL (Fin V.rank) D.host.E) := Units.val_injective.countable
  infer_instance

theorem kernel_diag_hasSum {D : D7} (V : HSp D) {f : GA D V → ℂ} (hf : f ∈ CcGA V) (x : GA D V) :
    (Function.support fun δ : GF V => f (x⁻¹ * rat V δ * x)).Finite ∧
    HasSum (fun δ : GF V => f (x⁻¹ * rat V δ * x)) (GlobalTheory.AutomorphicL2Unitary.kernel (GQ V) f x x) := by
  have hcs := continuous_of_mem_ccAd hf
  have hr : (ratEmb D.sp.cm.sig V.gram).range = GQ V := by rw [range_ratEmb]; rfl
  let e : GF V ≃* GQ V :=
    (MonoidHom.ofInjective (ratEmb_injective D.sp.cm.sig V.gram)).trans (MulEquiv.subgroupCongr hr)
  have he : ∀ δ : GF V, ((e δ : GQ V) : GA D V) = rat V δ := fun δ => rfl
  refine ⟨?_, ?_⟩
  · have hC : IsCompact ((fun g : GA D V => x * g * x⁻¹) '' tsupport f) :=
      hcs.2.isCompact.image (by fun_prop)
    have hfin := finite_mem_compact (Γ := GQ V) hC
    refine (hfin.preimage e.injective.injOn).subset fun δ hδ => ?_
    refine ⟨x⁻¹ * rat V δ * x, subset_tsupport _ hδ, ?_⟩
    simp only [he]
    group
  · have := hasSum_kernel (Γ := GQ V) hcs.2 x x
    exact (e.toEquiv.hasSum_iff (f := fun γ : GQ V => f (x⁻¹ * (γ : GA D V) * x))).2 this

theorem charpoly_eq_of_isConj {D : D7} {V : HSp D} {a b : GF V} (h : IsConj a b) :
    a.1.1.charpoly = b.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  change a.1.1.charpoly = ((c.1 : GL _ _) * a.1 * (c.1)⁻¹ : GL _ _).1.charpoly
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end GlobalTheory.CompanionTheory.EllTrace
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfdualMeasureHermitianTuples
section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN

theorem exists_sdW_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ μ : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n μ := by
  intro F E _ _ _ _ _ σ hCM M J hJ ψ hψ n
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨B, hsym, hdet, -, hR'⟩ :=
    GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ _ b
  obtain ⟨h1, h2, h3, h4, -, -, hcc, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := hBor n M
  have hc : IsHomeomorph (GlobalTheory.CompanionTheory.SW.SdTuples.cf (F := F) (E := E) (AF F) b) := hcc _ b
  have hsym' : (Matrix.blockDiagonal fun _ : Fin n => B).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    simp only [hsym.eq]
  have hdet' : (Matrix.blockDiagonal fun _ : Fin n => B).det ≠ 0 := by
    rw [Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hdet
  obtain ⟨μ, hμ⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.SdExist.exists_selfDual_form ψ hψ _ hsym' hdet'
    (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M)
  refine ⟨μ, ?_⟩
  unfold SdW
  have hf : (fun X Y : Fin n → Fin M → AF F ⊗[F] E => ψ (BR (AF F) σ J X Y)) = fun X Y =>
      ψ (dotProduct (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M X) (Matrix.mulVec
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F (AF F)))
        (GlobalTheory.CompanionTheory.SW.SdTuples.tupE hc n M Y))) := by
    funext X Y
    rw [← GlobalTheory.CompanionTheory.SW.SdTuples.BR_eq hc J B (hR' (AF F)).1 X Y]
  rw [hf]
  exact hμ

end GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_level : Ad3.R.B0 → Ad3.R.F1 := by
  first | exact @GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists | exact GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists | (intros; apply GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists <;> assumption)
end

