module

public import Mathlib
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0081
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0076

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNcardEntrywiseBoxLe
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Counting


open GroundTheory.Automorphic.CuspidalSpectrum in
theorem exists_ncard_entrywiseBox_le (K : Type) [Field K] [NumberField K] (n : ℕ)
    (𝒦 : Set (FiniteAdeleRing (𝓞 K) K)) (h𝒦 : IsCompact 𝒦) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ T i j) →
      (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)).Finite ∧
      ((Set.ncard (setOf fun γ : GL (Fin n) K => (∀ i j,
        algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
        ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j)) : ℕ) : ℝ) ≤
        ∏ i, ∏ j, C * (1 + T i j) ^ Module.finrank ℚ K := by
  obtain ⟨m, hm, hint⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact K h𝒦
  obtain ⟨C₀, hC₀, hcount⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_integers_le K
  have hw : ∀ (w : InfinitePlace K) (x : K), w ((m : K) * x) = (m : ℝ) * w x := by
    intro w x
    rw [← w.norm_embedding_eq, map_mul, norm_mul, w.norm_embedding_eq, w.norm_embedding_eq, w.map_natCast]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨C₀ * (m : ℝ) ^ Module.finrank ℚ K, mul_nonneg hC₀ (by positivity), ?_⟩
  intro T hT
  have hA : ∀ p : Fin n × Fin n,
      (((↑) : 𝓞 K → K) '' {z | ∀ w : InfinitePlace K, w (z : K) ≤ (m : ℝ) * T p.1 p.2}).Finite ∧
      ((((↑) : 𝓞 K → K) '' {z | ∀ w : InfinitePlace K, w (z : K) ≤ (m : ℝ) * T p.1 p.2}).ncard : ℝ) ≤
        C₀ * (1 + (m : ℝ) * T p.1 p.2) ^ Module.finrank ℚ K := by
    intro p
    obtain ⟨hf, hc⟩ := hcount ((m : ℝ) * T p.1 p.2) (mul_nonneg (by positivity) (hT p.1 p.2))
    exact ⟨hf.image _, le_trans (by exact_mod_cast Set.ncard_image_le hf) hc⟩
  let F : GL (Fin n) K → (Fin n × Fin n → K) := fun γ p => (m : K) * (γ : Matrix (Fin n) (Fin n) K) p.1 p.2
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin n × Fin n → K), t = Fintype.piFinset fun p => (hA p).1.toFinset := ⟨_, rfl⟩
  have key : ∀ γ : GL (Fin n) K, (∀ i j, algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
      ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j) → F γ ∈ (t : Set (Fin n × Fin n → K)) := by
    intro γ hγ
    rw [Finset.mem_coe, ht, Fintype.mem_piFinset]
    intro p
    rw [Set.Finite.mem_toFinset]
    obtain ⟨z, hz⟩ := hint _ (hγ p.1 p.2).1
    refine ⟨z, fun w => ?_, hz⟩
    rw [hz, hw]
    exact mul_le_mul_of_nonneg_left ((hγ p.1 p.2).2 w) (by positivity)
  have inj : ∀ γ γ' : GL (Fin n) K, F γ = F γ' → γ = γ' := by
    intro γ γ' h
    ext i j
    exact mul_left_cancel₀ hmK (congrFun h (i, j))
  refine ⟨?_, ?_⟩
  · exact Set.Finite.of_finite_image ((t.finite_toSet).subset (Set.image_subset_iff.mpr fun γ hγ => key γ hγ))
      (fun γ _ γ' _ h => inj γ γ' h)
  · refine le_trans (Nat.cast_le.mpr (Set.ncard_le_ncard_of_injOn F (fun γ hγ => key γ hγ)
      (fun γ _ γ' _ h => inj γ γ' h) t.finite_toSet)) ?_
    rw [Set.ncard_coe_finset, ht, Fintype.card_piFinset, Nat.cast_prod, Fintype.prod_prod_type]
    apply Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
    intro i _
    apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
    intro j _
    rw [← Set.ncard_eq_toFinset_card _ (hA (i, j)).1]
    refine le_trans (hA (i, j)).2 ?_
    rw [mul_assoc, ← mul_pow]
    apply mul_le_mul_of_nonneg_left _ hC₀
    apply pow_le_pow_left₀ (by nlinarith [hT i j])
    nlinarith [hT i j]

end GlobalTheory.CompanionTheory.Counting
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryInterlacingRealization
section
open Finset Matrix PositivityTheory.RgHe.Frame

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeFrame

def sg (b : Bool) : ℝ := if b then 1 else -1

lemma sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

lemma sg_ne_zero (b : Bool) : sg b ≠ 0 := by cases b <;> simp [sg]

lemma sg_cast (b : Bool) : ((sg b : ℝ) : ℂ) = if b then 1 else -1 := by cases b <;> simp [sg]

variable {n : ℕ}

def cc (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (i : Fin (n + 1)) : ℝ := 1 / √|pfD d d' i|

def yy (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (j : Fin n) : ℝ :=
  √(-(sg (ε' j) * pfR d d' j))

def G0 (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (r : Fin n ⊕ Unit)
    (i : Fin (n + 1)) : ℝ :=
  Sum.elim (fun j => cc d d' i * yy ε' d d' j / (d i - d' j)) (fun _ => cc d d' i) r

def X0 (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (r t : Fin n ⊕ Unit) : ℝ :=
  Sum.elim
    (fun a => Sum.elim (fun b => if a = b then d' a else 0) (fun _ => yy ε' d d' a) t)
    (fun _ => Sum.elim (fun b => sg (ε' b) * yy ε' d d' b) (fun _ => pfX d d') t) r

lemma yy_sq {ε' : Fin n → Bool} {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {j : Fin n}
    (h : 0 < -(sg (ε' j) * pfR d d' j)) :
    sg (ε' j) * (yy ε' d d' j * yy ε' d d' j) = -pfR d d' j := by
  unfold yy
  rw [Real.mul_self_sqrt h.le]
  have := sg_mul_self (ε' j)
  linear_combination (-pfR d d' j) * this

lemma cc_sq {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {i : Fin (n + 1)} {b : Bool}
    (h : 0 < sg b * pfD d d' i) : cc d d' i * cc d d' i * pfD d d' i = sg b := by
  have hcc : cc d d' i * cc d d' i = 1 / |pfD d d' i| := by
    unfold cc
    rw [div_mul_div_comm, Real.mul_self_sqrt (abs_nonneg _), one_mul]
  rw [hcc]
  cases b with
  | true =>
    have hp : 0 < pfD d d' i := by simpa [sg] using h
    rw [abs_of_pos hp]
    simp only [sg]
    field_simp
    simp
  | false =>
    have hp : pfD d d' i < 0 := by simpa [sg] using h
    rw [abs_of_neg hp]
    simp only [sg]
    have := hp.ne
    field_simp
    simp

lemma cc_ne_zero {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {i : Fin (n + 1)} {b : Bool}
    (h : 0 < sg b * pfD d d' i) : cc d d' i ≠ 0 := by
  intro h0
  have := cc_sq h
  rw [h0] at this
  exact sg_ne_zero b (by simpa using this.symm)

lemma sum_terms {ε' : Fin n → Bool} {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ}
    (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j)) (i k : Fin (n + 1)) :
    ∑ j, (cc d d' i * yy ε' d d' j / (d i - d' j)) * sg (ε' j) *
        (cc d d' k * yy ε' d d' j / (d k - d' j)) =
      -(cc d d' i * cc d d' k * ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j))) := by
  rw [mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h := yy_sq (hR j)
  calc (cc d d' i * yy ε' d d' j / (d i - d' j)) * sg (ε' j) *
        (cc d d' k * yy ε' d d' j / (d k - d' j))
      = cc d d' i * cc d d' k * (sg (ε' j) * (yy ε' d d' j * yy ε' d d' j)) /
          ((d i - d' j) * (d k - d' j)) := by
          simp only [div_eq_mul_inv, mul_inv]; ring
    _ = _ := by rw [h]; ring

lemma gram {ε : Fin (n + 1) → Bool} {d : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {d' : Fin n → ℝ}
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (hz : ε (e (Sum.inr ())) = true)
    (hs : ∀ a, ε (e (Sum.inl a)) = ε' a) (hinj : Function.Injective (Sum.elim d d'))
    (hD : ∀ i, 0 < sg (ε i) * pfD d d' i) (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j))
    (i k : Fin (n + 1)) :
    ∑ r, G0 ε' d d' (e.symm r) i * sg (ε r) * G0 ε' d d' (e.symm r) k =
      if i = k then sg (ε i) else 0 := by
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply, G0, Sum.elim_inl, Sum.elim_inr, hs, hz, univ_unique,
    sum_singleton]
  rw [sum_terms hR]
  have hz1 : sg true = 1 := by simp [sg]
  rw [hz1]
  by_cases hik : i = k
  · subst hik
    have h1 := _root_.GlobalTheory.CompanionTheory.RgHeFrame.pfDer d d' hinj i
    have h2 := cc_sq (hD i)
    simp only [if_true]
    have h3 : ∑ j, pfR d d' j / ((d i - d' j) * (d i - d' j)) =
        ∑ j, pfR d d' j / (d i - d' j) ^ 2 := by
      refine sum_congr rfl fun j _ => ?_
      rw [sq]
    rw [h3]
    linear_combination (cc d d' i * cc d d' i) * h1 + h2
  · have h1 := _root_.GlobalTheory.CompanionTheory.RgHeFrame.pfOrth d d' hinj i k hik
    simp only [hik, if_false]
    linear_combination (cc d d' i * cc d d' k) * h1

lemma inter {d : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {d' : Fin n → ℝ}
    (hinj : Function.Injective (Sum.elim d d'))
    (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j)) (r : Fin n ⊕ Unit) (i : Fin (n + 1)) :
    ∑ t, X0 ε' d d' r t * G0 ε' d d' t i = G0 ε' d d' r i * d i := by
  have hne : ∀ j, d i - d' j ≠ 0 := by
    intro j h
    have : (Sum.inl i : Fin (n + 1) ⊕ Fin n) = Sum.inr j :=
      hinj (by simpa using sub_eq_zero.mp h)
    simp at this
  rw [Fintype.sum_sum_type]
  rcases r with a | u
  · simp only [X0, G0, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton, ite_mul, zero_mul,
      sum_ite_eq, mem_univ, if_true]
    have := hne a
    field_simp
    ring
  · simp only [X0, G0, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton]
    have h0 := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj i
    have h1 : ∑ j, sg (ε' j) * yy ε' d d' j * (cc d d' i * yy ε' d d' j / (d i - d' j)) =
        -(cc d d' i * ∑ j, pfR d d' j / (d i - d' j)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun j _ => ?_
      have h := yy_sq (hR j)
      calc sg (ε' j) * yy ε' d d' j * (cc d d' i * yy ε' d d' j / (d i - d' j))
          = cc d d' i * (sg (ε' j) * (yy ε' d d' j * yy ε' d d' j)) / (d i - d' j) := by ring
        _ = _ := by rw [h]; ring
    rw [h1]
    linear_combination (-cc d d' i) * h0

theorem build : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), ε (e (Sum.inr ())) = true → (∀ a, ε (e (Sum.inl a)) = ε' a) → Function.Injective (Sum.elim d d') → (∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i) → (∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j)) → ∃ g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Formalism.REAL.inUJ ε g ∧ X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) ∧ (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) ∧ ∀ i, ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ)) i ≠ 0 := by
  intro n ε d ε' d' e hz hs hinj hD hR
  have hD' : ∀ i, 0 < sg (ε i) * pfD d d' i := hD
  have hR' : ∀ j, 0 < -(sg (ε' j) * pfR d d' j) := hR
  obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ r i, g r i = ((G0 ε' d d' (e.symm r) i : ℝ) : ℂ) := ⟨Matrix.of _, fun _ _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ r t, X r t = ((X0 ε' d d' (e.symm r) (e.symm t) : ℝ) : ℂ) := ⟨Matrix.of _, fun _ _ => rfl⟩
  refine ⟨g, X, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.REAL.inUJ Formalism.REAL.Jm
    ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hg,
      RCLike.star_def, Complex.conj_ofReal]
    have h := gram e hz hs hinj hD' hR' i k
    have h2 := congrArg (fun x : ℝ => (x : ℂ)) h
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, sg_cast] at h2
    rw [h2]
    by_cases hik : i = k
    · simp [hik, sg_cast]
    · simp [hik]
  · ext r i
    rw [Matrix.mul_diagonal, Matrix.mul_apply, ← Equiv.sum_comp e]
    simp only [hg, hX, Equiv.symm_apply_apply]
    have h := inter (ε' := ε') hinj hR' (e.symm r) i
    exact_mod_cast h
  · intro a b
    simp only [hX, Equiv.symm_apply_apply, X0, Sum.elim_inl]
    split_ifs <;> simp
  · intro i
    rw [Matrix.mulVec_single_one]
    change (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) i (e (Sum.inr ())) ≠ 0
    unfold Formalism.REAL.Jm
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hg,
      Equiv.symm_apply_apply, G0, Sum.elim_inr, hz, RCLike.star_def, Complex.conj_ofReal]
    have hc := cc_ne_zero (hD' i)
    have : ((cc d d' i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
    cases h : ε i <;> simpa using this

end GlobalTheory.CompanionTheory.RgHeFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOutNeZero
section
open GlobalTheory.SplitFlip

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeAdj

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_out_ne_zero (K : Subgroup G) (hKo : IsOpen (K : Set G)) {φ : G → ℂ} (hφ : HasCompactSupport φ) :
    {q : G ⧸ K | φ q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport φ) :=
    hφ.isCompact.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport φ hq, QuotientGroup.out_eq' q⟩

variable [MeasurableSpace G] [BorelSpace G]

theorem measure_coset (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (q : G ⧸ K) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) = μ (K : Set G) := by
  have e : (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q} = (fun h => q.out⁻¹ * h) ⁻¹' (K : Set G) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  rw [e, measure_preimage_mul]

theorem integral_eq_sum (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {φ : G → ℂ} (hφ : HasCompactSupport φ)
    (hr : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) :
    ∫ g, φ g ∂μ = μ.real (K : Set G) • ∑ᶠ q : G ⧸ K, φ q.out := by
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hF := finite_out_ne_zero K hKo hφ
  set S : Finset (G ⧸ K) := hF.toFinset with hS
  have hmeas : ∀ q : G ⧸ K, MeasurableSet ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) := fun q =>
    ((isOpen_discrete ({q} : Set (G ⧸ K))).preimage QuotientGroup.continuous_mk).measurableSet
  have hout : ∀ g : G, φ ((g : G ⧸ K)).out = φ g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hr g k k.2]
  have hsum : φ = fun g => ∑ q ∈ S, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g := by
    funext g
    have : ∀ q : G ⧸ K, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g =
        if (g : G ⧸ K) = q then φ q.out else 0 := fun q => by
      simp [Set.indicator_apply]
    simp only [this, Finset.sum_ite_eq]
    split_ifs with h
    · exact (hout g).symm
    · have : φ ((g : G ⧸ K)).out = 0 := by
        by_contra h0
        exact h (hF.mem_toFinset.2 h0)
      rw [← hout g, this]
  have hint : ∀ q ∈ S, Integrable (((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out)) μ := by
    intro q _
    refine (integrable_indicator_iff (hmeas q)).2 (integrableOn_const ?_)
    rw [measure_coset]
    exact hfin
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun q hq => hF.mem_toFinset.2 hq)]
  conv_lhs => rw [hsum]
  rw [MeasureTheory.integral_finsetSum S hint, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hmeas q)]
  simp only [Measure.real, measure_coset]

theorem adjoint_of_inv (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (e : G → ℂ) (he : HasCompactSupport e)
    (hbi : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, e (k₁ * g * k₂) = e g)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (v w : V) (hv : ∀ k ∈ K, ρ k v = v) (hw : ∀ k ∈ K, ρ k w = w) :
    B (∑ᶠ q : G ⧸ K, e q.out • ρ q.out v) w =
      B v (∑ᶠ q : G ⧸ K, starRingEnd ℂ (e q.out⁻¹) • ρ q.out w) := by
  have hfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hpos : μ.real (K : Set G) ≠ 0 :=
    (ENNReal.toReal_pos (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne' hfin).ne'
  set φ₁ : G → ℂ := fun g => e g * B (ρ g v) w with hφ₁
  set φ₂ : G → ℂ := fun g => e g⁻¹ * B v (ρ g w) with hφ₂
  have hinv : ∀ g, φ₂ g = φ₁ g⁻¹ := fun g => by
    have h := hB g (ρ g⁻¹ v) w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    simp only [hφ₁, hφ₂, h]
  have he' : HasCompactSupport (fun g : G => e g⁻¹) := he.comp_homeomorph (Homeomorph.inv G)
  have hc₁ : HasCompactSupport φ₁ := he.mul_right
  have hc₂ : HasCompactSupport φ₂ := he'.mul_right
  have hr₁ : ∀ g, ∀ k ∈ K, φ₁ (g * k) = φ₁ g := fun g k hk => by
    have h1 : e (g * k) = e g := by simpa using hbi 1 K.one_mem k hk g
    simp only [hφ₁, h1, map_mul, Module.End.mul_apply, hv k hk]
  have hr₂ : ∀ g, ∀ k ∈ K, φ₂ (g * k) = φ₂ g := fun g k hk => by
    have h1 : e (g * k)⁻¹ = e g⁻¹ := by
      rw [mul_inv_rev]
      simpa using hbi k⁻¹ (K.inv_mem hk) 1 K.one_mem g⁻¹
    simp only [hφ₂, h1, map_mul, Module.End.mul_apply, hw k hk]
  have hs₁ : (Function.support fun q : G ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_out_ne_zero K hKo he).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  have hs₂ : (Function.support fun q : G ⧸ K => starRingEnd ℂ (e q.out⁻¹) • ρ q.out w).Finite :=
    (finite_out_ne_zero K hKo he').subset fun q hq h0 => hq (by simp [show e q.out⁻¹ = 0 from h0])
  have l₁ : B (∑ᶠ q : G ⧸ K, e q.out • ρ q.out v) w = ∑ᶠ q : G ⧸ K, φ₁ q.out := by
    have := AddMonoidHom.map_finsum (AddMonoidHom.mk' (fun x => B x w) (by simp)) hs₁
    simpa [hφ₁] using this
  have l₂ : B v (∑ᶠ q : G ⧸ K, starRingEnd ℂ (e q.out⁻¹) • ρ q.out w) = ∑ᶠ q : G ⧸ K, φ₂ q.out := by
    have := AddMonoidHom.map_finsum (AddMonoidHom.mk' (fun x => B v x) (by simp)) hs₂
    simpa [hφ₂] using this
  have hI : ∫ g, φ₂ g ∂μ = ∫ g, φ₁ g ∂μ := by
    simp only [hinv]
    exact integral_inv_eq_self φ₁ μ
  rw [integral_eq_sum μ K hKo hfin hc₁ hr₁, integral_eq_sum μ K hKo hfin hc₂ hr₂] at hI
  rw [l₁, l₂]
  exact (smul_right_injective ℂ hpos hI).symm

end Abstract

section GeneralLinearIntegers

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isInvInvariant [MeasurableSpace F] [BorelSpace F] (μ : Measure (GL ι F)) [μ.IsHaarMeasure]
    (K : Subgroup (GL ι F)) (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) :
    μ.IsInvInvariant := by
  refine ⟨?_⟩
  have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have hne : μ (K : Set (GL ι F)) ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hnt : μ (K : Set (GL ι F)) ≠ ⊤ := hKc.measure_lt_top.ne
  have h2 := congrArg (fun m : Measure (GL ι F) => m (K : Set (GL ι F))) hc
  open scoped Pointwise in
  have hKi : (K : Set (GL ι F))⁻¹ = K := inv_coe_set
  simp only [Measure.inv_apply, hKi, Measure.coe_nnreal_smul_apply] at h2
  have h3 : ((Measure.haarScalarFactor μ.inv μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
  have h4 : Measure.haarScalarFactor μ.inv μ = 1 := by exact_mod_cast h3
  rw [hc, h4, one_smul]

end GeneralLinearIntegers

theorem hk_adjoint : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    IsHk K (hstar e) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∀ v ∈ fixed ρ K, ∀ w ∈ fixed ρ K,
      B (hk ρ K e v) w = B v (hk ρ K (hstar e) w) := by
  intro F _ _ _ _ ι _ _ K e he
  obtain ⟨hKo, hKc, hc, hbi⟩ := he
  refine ⟨⟨hKo, hKc, ?_, ?_⟩, ?_⟩
  · have h1 : HasCompactSupport (fun g : GL ι F => e g⁻¹) := hc.comp_homeomorph (Homeomorph.inv _)
    exact h1.comp_left (g := starRingEnd ℂ) (map_zero _)
  · intro k₁ h₁ k₂ h₂ g
    show starRingEnd ℂ (e (k₁ * g * k₂)⁻¹) = starRingEnd ℂ (e g⁻¹)
    rw [show (k₁ * g * k₂)⁻¹ = k₂⁻¹ * g⁻¹ * k₁⁻¹ by group, hbi _ (K.inv_mem h₂) _ (K.inv_mem h₁)]
  · intro V _ _ ρ B hB v hv w hw
    borelize F
    haveI := isInvInvariant (Measure.haar : Measure (GL ι F)) K hKo hKc
    exact adjoint_of_inv Measure.haar K hKo hKc e hc hbi ρ B hB v w
      (fun k hk => by simpa using hv ⟨k, hk⟩) (fun k hk => by simpa using hw ⟨k, hk⟩)

end GlobalTheory.CompanionTheory.HeckeAdj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FractionFieldTranscendenceBasisExt
section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TraceJac

theorem det_completed_eq_minor {L : Type*} [Field L] {d m : ℕ} (κ : Fin m ↪ Fin d)
    (E : Fin d → L → L) (τ : Fin d → L) (hE : ∀ k j, E k (τ j) = if k = j then 1 else 0)
    (β : Fin m → L) :
    let e : Fin m ⊕ ↥(Set.range κ)ᶜ ≃ Fin d :=
      (Equiv.sumCongr (Equiv.ofInjective κ κ.injective) (Equiv.refl _)).trans
        (Equiv.Set.sumCompl (Set.range κ))
    (Matrix.of fun k l => E k ((Sum.elim β (fun j : ↥(Set.range κ)ᶜ => τ j)) (e.symm l))).det =
      (Matrix.of fun k l => E (κ k) (β l)).det := by
  classical
  intro e
  have he1 : ∀ i, e (Sum.inl i) = κ i := fun i => by simp [e]
  have he2 : ∀ j : ↥(Set.range κ)ᶜ, e (Sum.inr j) = j := fun j => by simp [e]
  rw [← Matrix.det_submatrix_equiv_self e]
  have hblock : (Matrix.of fun k l =>
      E k ((Sum.elim β (fun j : ↥(Set.range κ)ᶜ => τ j)) (e.symm l))).submatrix e e =
      Matrix.fromBlocks (Matrix.of fun k l => E (κ k) (β l)) 0
        (Matrix.of fun (j : ↥(Set.range κ)ᶜ) l => E j (β l)) 1 := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_apply_apply]
    rcases x with i | j <;> rcases y with i' | j'
    · simp [he1]
    · have hne : κ i ≠ (j' : Fin d) := fun h => j'.2 ⟨i, h⟩
      simp [he1, hE, hne]
    · simp [he2]
    · have : ((j : Fin d) = j') ↔ j = j' := Subtype.ext_iff.symm
      simp [he2, hE, Matrix.one_apply, this]
  rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

theorem trace_minor_mem : ∀ (K : Type) [Field K] [CharZero K] (d : ℕ) (A : Type) [CommRing A] [IsDomain A] [Algebra K A] (t : Fin d → A), Function.Injective (MvPolynomial.aeval t : MvPolynomial (Fin d) K →ₐ[K] A) → (∀ a : A, ∃ f g : MvPolynomial (Fin d) K, IsUnit (MvPolynomial.aeval t g) ∧ a * MvPolynomial.aeval t g = MvPolynomial.aeval t f) → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [Module.Finite A B], Function.Injective (algebraMap A B) → ∀ (F L : Type) [Field F] [Field L] [Algebra A F] [IsFractionRing A F] [Algebra B L] [IsFractionRing B L] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower K B L] (D : Fin d → Derivation K L L), (∀ k j, D k (algebraMap A L (t j)) = if k = j then 1 else 0) → ∀ (m : ℕ) (κ : Fin m ↪ Fin d) (c : B) (b : Fin m → B), ∃ a : A, algebraMap A F a = Algebra.trace F L (algebraMap B L c * (Matrix.of fun k l => D (κ k) (algebraMap B L (b l))).det) := by
  intro K _ _ d A _ _ _ t ht hloc B _ _ _ _ _ _ hB F L _ _ _ _ _ _ _ _ _ _ _ _ D hD m κ c b
  classical
  let e : Fin m ⊕ ↥(Set.range κ)ᶜ ≃ Fin d :=
    (Equiv.sumCongr (Equiv.ofInjective κ κ.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range κ))
  let b' : Fin d → B := fun l =>
    (Sum.elim b (fun j : ↥(Set.range κ)ᶜ => algebraMap A B (t j))) (e.symm l)
  obtain ⟨a, ha⟩ := trace_jacobian_mem K d A t ht hloc B hB F L D hD c b'
  refine ⟨a, ha.trans ?_⟩
  have hdet := det_completed_eq_minor κ (fun k x => D k x) (fun j => algebraMap A L (t j)) hD
    (fun l => algebraMap B L (b l))
  have hmat : (Matrix.of fun k l => D k (algebraMap B L (b' l))) =
      Matrix.of fun k l => D k ((Sum.elim (fun l => algebraMap B L (b l))
        (fun j : ↥(Set.range κ)ᶜ => algebraMap A L (t j))) (e.symm l)) := by
    ext k l
    simp only [Matrix.of_apply, b']
    rcases e.symm l with i | j
    · simp
    · simp [← IsScalarTower.algebraMap_apply A B L]
  rw [hmat]
  exact congrArg (fun x => Algebra.trace F L (algebraMap B L c * x)) hdet

end GlobalTheory.CompanionTheory.TraceJac
end

