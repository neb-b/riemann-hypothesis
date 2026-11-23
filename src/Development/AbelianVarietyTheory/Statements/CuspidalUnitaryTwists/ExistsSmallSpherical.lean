module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.ArchimedeanLeaf.LeafARCHFree
public import Formalism.PairingDivisors.PairingDivisorProofs.Height
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245

@[expose] public section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.NormSum

def IntegralOver (D : D7) {N : ℕ} (p : ℕ) (h : GA D N) : Prop :=
  ∃ k ∈ intG D N, TrivAt D p ((h * k : GA D N) : GL (Fin N) (AE D))

def intBound (C : ℝ) (f N : ℕ) (B L : ℝ) (Q : ℕ) : ℝ :=
  C * f * (2 * (N : ℝ)) * Real.log ((f : ℝ) * (2 * (N : ℝ))) + C * f * (2 * (N : ℝ)) * B * L +
    C * f * (2 * (N : ℝ)) ^ 2 * B * Real.log Q

def Exponents (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ) : Prop :=
  (∀ l ∈ S, l.Prime) ∧ (∀ l, 0 ≤ del_vp l) ∧ (∀ l, l ∉ S → del_vp l = 0) ∧ ∑ l ∈ S, del_vp l * Real.log l ≤ b

def CoordInt (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (del_vp : ℕ → ℝ) : Prop :=
  ∀ (δ t0 : ℂ) (p : ℕ) [Fact p.Prime] (Q' : ℕ), padicValNat p Q' ≤ padicValNat p Q →
    ∀ P : Pair D ⊤ δ t0 Q', P.Small N B →
      (∀ q : Cls D P.d P.J, ∃ h, DoubleCoset.mk (ratG D P.d) P.J h = q ∧ IntegralOver D p h) ∧
      (∀ h, gam D P.J h ≠ 0 ∧ (padicValNat p (gam D P.J h) : ℝ) ≤ del_vp p) ∧
      ∀ h, IntegralOver D p h → ∀ T, P.coord h T ∈ Qbar ∧
        ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam (P.coord h T)‖ ≤ (p : ℝ) ^ del_vp p

def NormInt (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ) : Prop :=
  ∀ (δ t0 : ℂ) (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) (ι : Type)
    (P P' : ι → Pair D ⊤ δ t0 Q) (zA zA' : ι → K),
    (∀ i, (P i).Small N B ∧ (P' i).Small N B) →
    (∀ i, (∃ h T, (P i).coord h T ≠ 0) ∧ ∃ h T, (P' i).coord h T ≠ 0) →
    (∀ i, σ (zA i) = ((P i).norm : ℂ) ∧ σ (zA' i) = ((P' i).norm : ℂ)) →
    NonArchimedeanDefectBound (Formalism.PairingDivisionLocalBalance.wt S del_vp) zA zA' b

def IntSt : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (Q N : ℕ) (B L : ℝ), GoodLevel D Q → 1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L →
    ∃ (S : Finset ℕ) (del_vp : ℕ → ℝ), Exponents S del_vp (intBound C (fF D) N B L Q) ∧
      CoordInt D N B Q del_vp ∧ NormInt D N B Q S del_vp (intBound C (fF D) N B L Q)

def ArchSt : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (Q : ℕ), Crv D cc δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → 0 < Q →
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) (ι : Type) (N : ℕ) (B L : ℝ)
      (P P' : ι → Pair D cc δ t0 Q) (zA zA' : ι → K),
      1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L →
      (∀ i, (P i).Small N B ∧ (P' i).Small N B) →
      (∀ i, σ (zA i) = ((P i).norm : ℂ) ∧ σ (zA' i) = ((P' i).norm : ℂ)) →
      ArchimedeanHeightBound zA zA'
        (C * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) +
          C * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q)

section Places

open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Finset ℕ} {del : ℕ → ℝ} {b : ℝ}

theorem Exponents.wt_eq (h : Exponents S del b) {p : ℕ} (hp : p.Prime) (w : Pl K) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    wt S del w = del p * (vw w (p : K) : ℝ) := by
  unfold wt
  refine Finset.sum_eq_single p (fun l hl hne => ?_) fun hS => by rw [h.2.2.1 p hS, zero_mul]
  have hn : (l : 𝓞 K) ∉ w.asIdeal := fun hm => by
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (h.1 l hl) hp).2 hne)).map
      (Int.castRingHom (𝓞 K))
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hm)) (Ideal.mul_mem_left _ _ (by simpa using hw))
  have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
  simp only [map_natCast] at this
  rw [this]; simp

theorem Exponents.wt_size [_root_.NumberField.IsTotallyComplex K] (h : Exponents S del b) :
    (∀ w : Pl K, 0 ≤ wt S del w) ∧ ∀ F : Finset (Pl K), ∑ w ∈ F, Formalism.DivisionValues.lw w * wt S del w ≤ b := by
  obtain ⟨h1, h2, h3⟩ := Formalism.PairingDivisionLocalBalance.weight_sum' K S del
  have h0 := h3 fun l _ => h.2.1 l
  refine ⟨h0, fun F => le_trans ?_ (h2 ▸ h.2.2.2)⟩
  rw [finsum_eq_sum_of_support_subset (s := F ∪ h1.toFinset) _
    (fun w hw => Finset.mem_coe.2 (Finset.mem_union_right _ (h1.mem_toFinset.2 hw)))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun w _ _ =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (h0 w)

def conjQbar : Qbar →+* Qbar :=
  ((starRingEnd ℂ).comp (algebraMap Qbar ℂ)).codRestrict Qbar fun x =>
    mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 x.2).algHom ((starRingEnd ℂ).toRatAlgHom))

theorem conj_bound {p : ℕ} [Fact p.Prime] {z : ℂ} {r : ℝ} (hz : z ∈ Qbar) (h : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam z‖ ≤ r)
    (lam : Qbar →+* ℂ_[p]) : ‖lamC lam ((starRingEnd ℂ) z)‖ ≤ r := by
  have h1 := h (lam.comp conjQbar)
  have hz' : (starRingEnd ℂ) z ∈ Qbar := (conjQbar ⟨z, hz⟩).2
  rw [lamC, dite_eq_left hz] at h1
  rw [lamC, dite_eq_left hz']
  exact h1

end Places

theorem reps_and_stabilisers {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (p : ℕ)
    [hp : Fact p.Prime] :
    (∀ q : Cls D P.d P.J, ∃ h, DoubleCoset.mk (ratG D P.d) P.J h = q ∧ IntegralOver D p h) ∧
      ∀ h, gam D P.J h ≠ 0 ∧ padicValNat p (gam D P.J h) ≤
        padicValNat p (8 ^ (2 * fF D * P.d) * (2 * (2 * fF D * P.d)).factorial) := by
  constructor
  · intro q
    obtain ⟨γ, k, γ', h1, h2, h3⟩ := exists_rep_trivial_at D P.d p hp.out q.out
    refine ⟨γ * q.out, ?_, k, (mem_intG k).2 h2, h3⟩
    rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
    exact ⟨γ⁻¹, inv_mem ((mem_ratG γ).2 ⟨γ', h1⟩), 1, one_mem _, by simp [DoubleCoset.out_eq']⟩
  · intro h
    obtain ⟨h0, hd, -⟩ := GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D P.d P.J P.J_le h
    exact ⟨h0, ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (by positivity)).1 ((_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)).trans hd)⟩

end GlobalTheory.NormSum
