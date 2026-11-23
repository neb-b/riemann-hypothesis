module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeDeltaInvariantBasis
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeDeltaInvariantBasisStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_deltaInvariant_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.s = 1 → l ≠ 2 → ∀ (e s' : ℕ) (π' : AA K LL) (E' : Let K → Polynomial ↥(OL LL)), 0 < s' → wachRingRelations W e s' π' E' → wachModuleOverLetters W T π' := by
  first | exact @GlobalTheory.NL.InvBasis.invariant_basis | exact GlobalTheory.NL.InvBasis.invariant_basis | (intros; apply GlobalTheory.NL.InvBasis.invariant_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnityStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLevelExpansionLaws_of_rootsOfUnity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; LevLaws W := by
  first | exact @GlobalTheory.NL.Expansion.levLaws | exact GlobalTheory.NL.Expansion.levLaws | (intros; apply GlobalTheory.NL.Expansion.levLaws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfCoboundaryDetects
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_wild_top_le_of_detects : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → Detects p r ⊤ B → jumpSum (wild F L) ⊤ B ≤ 6 * E := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E r B hp hE hord hax hdet
  obtain ⟨hanti, hbot⟩ := _root_.GlobalTheory.PMon.Ram.wild_antitone_and_eventually_bot F L
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.PMon.Ram.exists_initialSegment_not_inf_le _ (wild F L) ⊤ B hanti hbot
  rcases n with _ | k
  · rw [_root_.GlobalTheory.PMon.Ram.jumpSum_eq_sum_range _ (wild F L) ⊤ B 0 hanti hn]
    simp
  · have hk : ¬ (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L k ≤ B := (hn k).1 (Nat.lt_succ_self k)
    obtain ⟨σ₀, hσ₀, hσ₀B⟩ := SetLike.not_le_iff_exists.1 hk
    have hσ₀k : σ₀ ∈ wild F L k := (Subgroup.mem_inf.1 hσ₀).2
    obtain ⟨x, a, hxa, hnd⟩ := hdet σ₀ (Subgroup.mem_top σ₀) hσ₀B
    obtain ⟨J, hJ, hJsum⟩ := _root_.GlobalTheory.PMon.Ram.jumpSum_kernel_le_six_mul F L p E r x a hp hE hord hax
      (fun σ => hxa σ (Subgroup.mem_top σ)) ⟨σ₀, hnd⟩
    have hσ₀J : σ₀ ∉ J := fun h => hnd ((hJ σ₀).1 h)
    have hmono : ∀ t, (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ J → (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ B := by
      intro t ht
      by_contra hB
      have htk : t ≤ k := Nat.lt_succ_iff.1 ((hn t).2 hB)
      have hσ₀t : σ₀ ∈ wild F L t := hanti htk hσ₀k
      exact hσ₀J (ht (Subgroup.mem_inf.2 ⟨Subgroup.mem_top σ₀, hσ₀t⟩))
    exact le_trans (_root_.GlobalTheory.PMon.Ram.jumpSum_mono_of_le _ (wild F L) ⊤ B J hanti hbot hmono) hJsum

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqOfSubMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem wittVector_exists_eq_pow_add_natCast_mul (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k]
    [CharP k l] [PerfectRing k l] (w : WittVector l k) :
    ∃ a b : WittVector l k, w = a ^ l + (l : WittVector l k) * b := by

  obtain ⟨c, hc⟩ : ∃ c : k, c ^ l = w.coeff 0 := ⟨_, frobeniusEquiv_symm_pow_p k l _⟩
  set a : WittVector l k := WittVector.teichmuller l c with ha

  have h0 : ∀ i < 1, (w - a ^ l).coeff i = 0 := by
    intro i hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    change WittVector.constantCoeff (w - a ^ l) = 0
    rw [map_sub, map_pow]
    change w.coeff 0 - (WittVector.teichmuller l c).coeff 0 ^ l = 0
    rw [WittVector.teichmuller_coeff_zero, hc, sub_self]
  have hV : w - a ^ l = WittVector.verschiebung ((w - a ^ l).shift 1) :=
    WittVector.eq_iterate_verschiebung h0

  set y := (w - a ^ l).shift 1 with hy
  set b := (WittVector.frobeniusEquiv l k).symm y with hb
  have hFb : WittVector.frobenius b = y := (WittVector.frobeniusEquiv l k).apply_symm_apply y
  refine ⟨a, b, ?_⟩
  have hVb : WittVector.verschiebung y = b * (l : WittVector l k) := by
    rw [← hFb, WittVector.verschiebung_frobenius]
  calc w = (w - a ^ l) + a ^ l := by ring
    _ = b * (l : WittVector l k) + a ^ l := by rw [hV, hVb]
    _ = a ^ l + (l : WittVector l k) * b := by ring

theorem wittVector_ringHom_eq_of_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C] (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ ω ω' : WittVector l k →+* C, (∀ w, ω w - ω' w ∈ J) → ω = ω' := by
  intro l _ k _ _ _ C _ J hl hJ ω ω' h

  have key : ∀ n : ℕ, ∀ w, ω w - ω' w ∈ J ^ (n + 1) := by
    intro n
    induction n with
    | zero => intro w; simpa using h w
    | succ n ih =>
      intro w
      obtain ⟨a, b, rfl⟩ := wittVector_exists_eq_pow_add_natCast_mul l k w
      obtain ⟨d, hdJ, hda⟩ : ∃ d, d ∈ J ^ (n + 1) ∧ ω a = ω' a + d := ⟨_, ih a, by ring⟩
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (ω' a) d
      have e : ω (a ^ l + (l : WittVector l k) * b) - ω' (a ^ l + (l : WittVector l k) * b) =
          d ^ l + (l : C) * (ω' a * d * r) + (l : C) * (ω b - ω' b) := by
        simp only [map_add (f := _), map_mul, map_pow, map_natCast]
        rw [hda, hr]
        ring
      rw [e]
      have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
      refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      ·
        have hpow : d ^ l ∈ J ^ ((n + 1) * l) := by
          rw [pow_mul]
          exact Ideal.pow_mem_pow hdJ l
        exact Ideal.pow_le_pow_right (by nlinarith) hpow
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hl (Ideal.mul_mem_right r _ (Ideal.mul_mem_left _ (ω' a) hdJ))
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hl (ih b)

  refine RingHom.ext fun w => ?_
  rw [← sub_eq_zero]
  refine hJ.haus _ fun n => ?_
  rw [SModEq.zero]
  have hn : ω w - ω' w ∈ J ^ n := by
    cases n with
    | zero => simp
    | succ n => exact key n w
  simpa using Submodule.smul_mem_smul hn (Submodule.mem_top : (1 : C) ∈ ⊤)

end GlobalTheory
end

