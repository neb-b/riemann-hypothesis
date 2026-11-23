module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntWitness
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.GaussModulus
open Formalism.L2.Host (atFin IsUnitAt)

namespace GlobalTheory.GaussModulus

theorem exists_int_witness {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (ha : a ≠ 0) (hE : ExpAt χ w a) :
    ∃ (y : 𝓞 E) (u : Eˣ), (u : E) = y ∧ y ∉ w.asIdeal ∧ y - 1 ∈ w.asIdeal ^ (a - 1) ∧ χ.locK w u ≠ 1 := by
  have hnot : ¬ χ.LevelLe w (a - 1) := fun h => by
    have := (hE (a - 1)).mp h
    omega
  have hlev : χ.LevelLe w a := (hE a).mpr le_rfl
  simp only [Formalism.L2.Host.HChar.LevelLe, not_forall] at hnot
  obtain ⟨x, hxu, hx1, hxχ⟩ := hnot
  have hxv : Valued.v (x : w.adicCompletion E) = 1 := hxu
  obtain ⟨y, hy⟩ := exists_int_approx w hxv.le a
  have hlt : WithZero.exp (-(a : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hyv' : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = 1 := by
    rw [← hxv]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [Valuation.map_sub_swap, hxv]
    exact lt_of_le_of_lt hy hlt
  have hyv : w.valuation E (y : E) = 1 := by rwa [← valued_algebraMap]
  have hy0 : (y : E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hyv
    exact zero_ne_one hyv
  refine ⟨y, Units.mk0 (y : E) hy0, rfl, ?_, ?_, ?_⟩
  · rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E)]
    exact hyv
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← valued_algebraMap]
    have e : algebraMap E (w.adicCompletion E) ((algebraMap (𝓞 E) E) (y - 1)) =
        (algebraMap E (w.adicCompletion E) (y : E) - (x : w.adicCompletion E)) + ((x : w.adicCompletion E) - 1) := by
      simp
    rw [e]
    refine Valuation.map_add_le _ ?_ hx1
    rw [Valuation.map_sub_swap]
    refine hy.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  · intro hχ
    apply hxχ
    set u : Eˣ := Units.mk0 (y : E) hy0 with hu
    have hau : ((atFin w u : (w.adicCompletion E)ˣ) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (y : E) := rfl
    have h1 : χ.loc w (x * (atFin w u)⁻¹) = 1 := by
      refine hlev _ ?_ ?_
      · show Valued.v (((x * (atFin w u)⁻¹ : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = 1
        rw [Units.val_mul, Units.val_inv_eq_inv_val, hau, map_mul, map_inv₀, hxv, hyv', inv_one, one_mul]
      · rw [Units.val_mul, Units.val_inv_eq_inv_val, hau]
        have hne : algebraMap E (w.adicCompletion E) (y : E) ≠ 0 := by
          intro h; rw [h, map_zero] at hyv'; exact zero_ne_one hyv'
        rw [show (x : w.adicCompletion E) * (algebraMap E (w.adicCompletion E) (y : E))⁻¹ - 1 =
            ((x : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) *
              (algebraMap E (w.adicCompletion E) (y : E))⁻¹ by field_simp]
        rw [map_mul, map_inv₀, hyv', inv_one, mul_one]
        exact hy
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [h1]
    exact hχ

end GlobalTheory.GaussModulus

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegersApproximatingRootOfUnityTwists
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

theorem v_pow_sub_pow_lt_one {C : Type} [Field C] (v : Valuation C NNReal) {x y : C} (hx : v x ≤ 1) (hy : v y ≤ 1)
    (hxy : v (x - y) < 1) (n : ℕ) : v (x ^ n - y ^ n) < 1 := by
  rw [← geom_sum₂_mul x y n, map_mul]
  have hs : v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one₀ (pow_le_one₀ zero_le hx) zero_le (pow_le_one₀ zero_le hy)
  calc v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * v (x - y) ≤ 1 * v (x - y) :=
        mul_le_mul_of_nonneg_right hs zero_le
    _ = v (x - y) := one_mul _
    _ < 1 := hxy

private lemma exists_mem_sub_one_mem_of_maximal_ne {R : Type} [CommRing R] {P Q : Ideal R} (hP : P.IsMaximal)
    (hQ : Q.IsMaximal) (h : P ≠ Q) : ∃ a ∈ P, a - 1 ∈ Q := by
  have htop : P ⊔ Q = ⊤ := Ideal.IsMaximal.coprime_of_ne hP hQ h
  have h1 : (1 : R) ∈ P ⊔ Q := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  refine ⟨a, ha, ?_⟩
  have hb' : a - 1 = -b := by rw [← hab]; ring
  rw [hb']
  exact Q.neg_mem hb

theorem exists_sub_one_mem_and_mem {R ι : Type} [CommRing R] [Finite ι] (P : ι → Ideal R) (hP : ∀ i, (P i).IsMaximal)
    (t : ι) : ∃ e : R, e - 1 ∈ P t ∧ ∀ i, P i ≠ P t → e ∈ P i := by
  classical
  haveI := Fintype.ofFinite ι
  have hc : ∀ i, ∃ a : R, (P i ≠ P t → a ∈ P i) ∧ a - 1 ∈ P t := by
    intro i
    by_cases hi : P i = P t
    · exact ⟨1, fun h => absurd hi h, by simp⟩
    · obtain ⟨a, ha, ha1⟩ := exists_mem_sub_one_mem_of_maximal_ne (hP i) (hP t) hi
      exact ⟨a, fun _ => ha, ha1⟩
  choose a ha using hc
  refine ⟨∏ i, a i, ?_, ?_⟩
  · refine Ideal.Quotient.eq.1 ?_
    rw [map_prod, map_one]
    exact Finset.prod_eq_one fun i _ => by
      rw [← map_one (Ideal.Quotient.mk (P t))]
      exact Ideal.Quotient.eq.2 (ha i).2
  · intro i hi
    rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
    exact Ideal.mul_mem_right _ _ ((ha i).1 hi)

private lemma pow_pow_mul_eq_self_of_pow_sub_one_eq_one {C : Type} [Field C] {z : C} {h : ℕ} (p : ℕ) (hp : 0 < p)
    (hz : z ^ (p ^ h - 1) = 1) (M : ℕ) : z ^ p ^ (h * M) = z := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih]
    have hph : p ^ h = p ^ h - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)).symm
    rw [hph, pow_succ, hz, one_mul]

theorem exists_approx_root_twists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ (τ : E →+* ℂ) (h : ℕ), 0 < h → ∀ (lab : ZMod h → (E →+* ℂ)), (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) → ∀ z : X.C, z ^ (p ^ h - 1) = 1 → (∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1) → ∀ r : ℝ, ∃ a : 𝓞 E, (∀ s, (r : WithTop ℝ) ≤ vX_vp X (embX io X (lab s) a - z ^ p ^ s.val)) ∧ ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a) := by
  intro E _ _ _ H l c p _ T io X τ h hh lab hlab z hz ha₀ r
  classical
  obtain ⟨a₀, ha₀⟩ := ha₀
  have hp : p.Prime := Fact.out
  haveI : NeZero h := ⟨hh.ne'⟩
  obtain ⟨e, he1, he⟩ := exists_sub_one_mem_and_mem (fun σ : E →+* ℂ => primeBelow io X σ)
    (fun σ => (primeBelow_isMaximal_card E H l c p T io X σ).1) τ
  have hv1 : ∀ σ a, X.v (embX io X σ a) ≤ 1 := fun σ a => v_embX_le_one io X σ a
  have hvz : X.v z ≤ 1 := by
    have hn : p ^ h - 1 ≠ 0 := by
      have : 2 ≤ p ^ h := le_trans hp.two_le (Nat.le_self_pow hh.ne' p)
      omega
    have h1 : X.v z ^ (p ^ h - 1) ≤ 1 := by rw [← map_pow, hz, map_one]
    exact (pow_le_one_iff_of_nonneg zero_le hn).1 h1
  have hvzs : ∀ n : ℕ, X.v (z ^ n) ≤ 1 := fun n => by rw [map_pow]; exact pow_le_one₀ zero_le hvz
  have he1' : X.v (embX io X τ e - 1) < 1 := by
    have : X.v (embX io X τ (e - 1)) < 1 := he1
    rwa [map_sub, map_one] at this
  have hτb : X.v (embX io X τ (e * a₀) - z) < 1 := by
    have hsplit : embX io X τ (e * a₀) - z =
        (embX io X τ e - 1) * embX io X τ a₀ + (embX io X τ a₀ - z) := by rw [map_mul]; ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ ha₀
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le he1' (hv1 τ a₀)
  have hlabb : ∀ s : ZMod h, X.v (embX io X (lab s) (e * a₀) - z ^ p ^ s.val) < 1 := by
    intro s
    have hsplit : embX io X (lab s) (e * a₀) - z ^ p ^ s.val =
        (embX io X (lab s) (e * a₀) - embX io X τ (e * a₀) ^ p ^ s.val) +
          (embX io X τ (e * a₀) ^ p ^ s.val - z ^ p ^ s.val) := by ring
    rw [hsplit]
    exact Valuation.map_add_lt _ (hlab s (e * a₀))
      (v_pow_sub_pow_lt_one X.v (hv1 τ _) hvz hτb _)
  have hoth : ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → X.v (embX io X σ (e * a₀)) < 1 := by
    intro σ hσ
    have hmem : X.v (embX io X σ e) < 1 := he σ hσ
    rw [map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hmem (hv1 σ a₀)
  have hs : ∀ s : ZMod h, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤
      vX_vp X (embX io X (lab s) (e * a₀) ^ p ^ N - (z ^ p ^ s.val) ^ p ^ N) := by
    intro s
    exact _root_.GlobalTheory.PowLim.pow_prime_pow_close X.C (vX_vp X) p hp (vX_vp_p X) _ _ ((isIntV_iff X _).2 (hv1 _ _))
      ((isIntV_iff X _).2 (hvzs _)) ((vX_vp_pos_iff X _).2 (hlabb s)) r
  have hσ : ∀ σ : E →+* ℂ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → primeBelow io X σ ≠ primeBelow io X τ →
      (r : WithTop ℝ) ≤ vX_vp X (embX io X σ (e * a₀) ^ p ^ N) := by
    intro σ
    by_cases hne : primeBelow io X σ = primeBelow io X τ
    · exact ⟨0, fun _ _ h' => absurd hne h'⟩
    · have hlt : X.v (embX io X σ (e * a₀) - 0) < 1 := by rw [sub_zero]; exact hoth σ hne
      obtain ⟨N₀, hN₀⟩ := _root_.GlobalTheory.PowLim.pow_prime_pow_close X.C (vX_vp X) p hp (vX_vp_p X) _ 0 ((isIntV_iff X _).2 (hv1 _ _))
        ((isIntV_iff X _).2 (by simp)) ((vX_vp_pos_iff X _).2 hlt) r
      refine ⟨N₀, fun N hN _ => ?_⟩
      have := hN₀ N hN
      rwa [zero_pow (pow_ne_zero _ hp.ne_zero), sub_zero] at this
  choose Ns hNs using hs
  choose Nσ hNσ using hσ
  set M := (∑ s, Ns s) + ∑ σ, Nσ σ with hM
  have hMN : M ≤ h * M := Nat.le_mul_of_pos_left M hh
  refine ⟨(e * a₀) ^ p ^ (h * M), fun s => ?_, fun σ hne => ?_⟩
  · have hzN : (z ^ p ^ s.val) ^ p ^ (h * M) = z ^ p ^ s.val := by
      rw [← pow_mul, mul_comm, pow_mul, pow_pow_mul_eq_self_of_pow_sub_one_eq_one p hp.pos hz M]
    have hle : Ns s ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s))
        (Nat.le_add_right _ _)) hMN
    have := hNs s (h * M) hle
    rwa [hzN, ← map_pow] at this
  · have hle : Nσ σ ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ))
        (Nat.le_add_left _ _)) hMN
    have := hNσ σ (h * M) hle hne
    rwa [← map_pow] at this

end GlobalTheory.PrimePart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseDifferentMaxValuation
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem invDifferent_exists_max_valuation :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ e : E, e ≠ 0 ∧
      (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧
      ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
        w.valuation E f ≤ w.valuation E e := by
  intro E _ _ w
  classical

  have hint : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      IsIntegral ℤ ((NumberField.discr E : E) * f) := by
    intro f hf
    have hmem : f ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
      have h := hf y
      rw [IsIntegrallyClosed.isIntegral_iff] at h
      obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      rw [Algebra.traceForm_apply, hk, mul_comm]
    have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
      rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
    have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
      (1 : Submodule (𝓞 E) E) hb h1 hmem
    rw [← coe_discr, Algebra.smul_def, mul_one] at this
    simpa using this
  have hle : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      w.valuation E ((NumberField.discr E : E) * f) ≤ 1 := by
    intro f hf
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hint f hf)
    rw [← hy]
    exact w.valuation_le_one y
  have hd0 : (NumberField.discr E : E) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hvd : w.valuation E (NumberField.discr E : E) ≠ 0 := by simpa using hd0
  have hP1 : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * 1)) := fun o => by
    rw [mul_one]; exact Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
  let S : ℤ → Prop := fun k => ∃ f : E, f ≠ 0 ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) ∧
      WithZero.log (w.valuation E f) = k
  have hbdd : ∃ b, ∀ z, S z → z ≤ b := by
    refine ⟨-WithZero.log (w.valuation E (NumberField.discr E : E)), ?_⟩
    rintro z ⟨f, hf0, hf, rfl⟩
    have hvf : w.valuation E f ≠ 0 := by simpa using hf0
    have h := hle f hf
    rw [map_mul, ← WithZero.exp_log hvd, ← WithZero.exp_log hvf, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  have hne : ∃ z, S z := ⟨_, 1, one_ne_zero, hP1, rfl⟩
  obtain ⟨k, ⟨e, he0, he, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨e, he0, he, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · subst hf0; simp
  have hvf : w.valuation E f ≠ 0 := by simpa using hf0
  have hve : w.valuation E e ≠ 0 := by simpa using he0
  have h := hmax _ ⟨f, hf0, hf, rfl⟩
  rw [← WithZero.exp_log hvf, ← WithZero.exp_log hve, WithZero.exp_le_exp]
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisAtPrimeOfIsLattice
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem exists_valuation_bound_of_fg {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG) :
    ∃ C : WithZero (Multiplicative ℤ), ∀ x ∈ L, ∀ i, w.valuation E (x i) ≤ C := by
  classical
  obtain ⟨s, rfl⟩ := hL
  refine ⟨(s ×ˢ (Finset.univ : Finset (Fin n))).sup fun p => w.valuation E (p.1 p.2), ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro i
    exact Finset.le_sup (f := fun p : (Fin n → E) × Fin n => w.valuation E (p.1 p.2))
      (b := (x, i)) (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; exact Valuation.map_add_le _ (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (w.valuation_le_one a)).trans (hx i)

theorem valuation_det_le_pow_of_entry_le {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (X : Matrix (Fin n) (Fin n) E)
    {C : WithZero (Multiplicative ℤ)} (h : ∀ i j, w.valuation E (X i j) ≤ C) :
    w.valuation E X.det ≤ C ^ n := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  have h1 : w.valuation E ((Equiv.Perm.sign σ : ℤ) : E) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine (mul_le_of_le_one_left' h1).trans ?_
  calc ∏ i, w.valuation E (X (σ i) i) ≤ ∏ _i : Fin n, C :=
        Finset.prod_le_prod' fun i _ => h _ _
    _ = C ^ n := by simp

theorem exists_det_ne_zero_col_mem_of_span_eq_top {E : Type} [Field E] {n : ℕ}
    {S : Set (Fin n → E)} (hS : Submodule.span E S = ⊤) :
    ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ ∀ j, (fun i => X i j) ∈ S := by
  classical
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent E S
  rw [hS] at hspan
  let b : Module.Basis t E (Fin n → E) := Module.Basis.mk hli (by simp [hspan])
  have hfin : Finite t := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  have hc : Fintype.card t = n := by
    rw [← Module.finrank_eq_card_basis b]; simp
  let e : t ≃ Fin n := Fintype.equivFinOfCardEq hc
  let b' := b.reindex e
  refine ⟨Matrix.of fun i j => b' j i, ?_, fun j => ?_⟩
  · have hli' : LinearIndependent E (Matrix.of fun i j => b' j i).col := b'.linearIndependent
    have := Matrix.linearIndependent_cols_iff_isUnit.1 hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  · have : (fun i => (Matrix.of fun i j => b' j i) i j) = (e.symm j : Fin n → E) := by
      funext i; simp [b', b]
    rw [this]
    exact htS (e.symm j).2

theorem exists_local_basis_of_isLattice (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) :
    ∃ X : Matrix (Fin n) (Fin n) E, IsUnit X.det ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1 := by
  classical
  obtain ⟨C, hC⟩ := exists_valuation_bound_of_fg w hL.fg
  obtain ⟨X₀, hX₀, hX₀L⟩ := exists_det_ne_zero_col_mem_of_span_eq_top hL.span_eq_top
  have hbd : ∀ X : Matrix (Fin n) (Fin n) E, (∀ j, (fun i => X i j) ∈ L) →
      w.valuation E X.det ≤ C ^ n := fun X hX =>
    valuation_det_le_pow_of_entry_le w X fun i j => hC _ (hX j) i
  obtain ⟨m, ⟨X, hX, hXL, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m => ∃ X : Matrix (Fin n) (Fin n) E, X.det ≠ 0 ∧ (∀ j, (fun i => X i j) ∈ L) ∧
      WithZero.log (w.valuation E X.det) = m)
    ⟨WithZero.log (C ^ n), by
      rintro _ ⟨X, hX, hXL, rfl⟩
      have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
      have h1 := hbd X hXL
      have h2 : C ^ n ≠ 0 := fun h => h0 (le_antisymm (h ▸ h1) zero_le')
      exact (WithZero.log_le_log h0 h2).2 h1⟩
    ⟨_, X₀, hX₀, hX₀L, rfl⟩
  have h0 : w.valuation E X.det ≠ 0 := by simpa using hX
  refine ⟨X, hX.isUnit, hXL, fun x hx i => ?_⟩
  have hcr : X.det * (X⁻¹ *ᵥ x) i = (X.updateCol i x).det := by
    have := congrFun (Matrix.det_smul_inv_mulVec_eq_cramer X x hX.isUnit) i
    simpa [Matrix.cramer_apply] using this
  have hle : w.valuation E (X.updateCol i x).det ≤ w.valuation E X.det := by
    by_cases hY : (X.updateCol i x).det = 0
    · simp [hY]
    · have h1 : w.valuation E (X.updateCol i x).det ≠ 0 := by simpa using hY
      refine (WithZero.log_le_log h1 h0).1 (hmax _ ⟨_, hY, fun j => ?_, rfl⟩)
      by_cases hj : j = i
      · subst hj
        simpa using hx
      · simpa [Matrix.updateCol_ne hj] using hXL j
  rw [← hcr, map_mul] at hle
  have hpos : 0 < w.valuation E X.det := zero_lt_iff.2 h0
  exact (mul_le_iff_le_one_right hpos).1 hle

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixAdjoinTensorUnramifiedOfCommuteSepar
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolyTensorCommutant

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

def algK : Algebra K (KQ p K r) := inferInstanceAs (Algebra K (K ⊗[ℚ_[p]] Qr p r))

attribute [local instance] algK

theorem inclK_mul (a : K) (x : KQ p K r) : inclK p K r a * x = a • x := by
  rw [Algebra.smul_def]; rfl

def bQ : Module.Basis (Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r)) K (KQ p K r) :=
  Algebra.TensorProduct.basis K (Module.Basis.ofVectorSpace ℚ_[p] (Qr p r))

theorem bQ_apply (i) : bQ p K r i = inclQ p K r (Module.Basis.ofVectorSpace ℚ_[p] (Qr p r) i) :=
  Algebra.TensorProduct.basis_apply _ _

theorem mul_algebraMap_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) (KQ p K r)) (c : KQ p K r) (i j : Fin n) :
    (M * algebraMap (KQ p K r) (Matrix (Fin n) (Fin n) (KQ p K r)) c) i j = M i j * c := by
  rw [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply,
    Matrix.mul_diagonal]

theorem exists_phi_eq : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ)
    (γ : Matrix (Fin n) (Fin n) K), 0 < r → γ.charpoly.Separable → ∀ X : Matrix (Fin n) (Fin n) (KQ p K r),
    Commute X (γ.map (inclK p K r)) → ∃ x, GlobalTheory.PolyTensor.phi p K n γ r x = X := by
  intro p _ K n r γ _ hsep X hX
  classical
  let Xc : Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r) → Matrix (Fin n) (Fin n) K :=
    fun i => X.map (fun x => (bQ p K r).coord i x)
  have hcomm : ∀ i, Commute (Xc i) γ := by
    intro i
    refine Matrix.ext fun a c => ?_
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) (KQ p K r) => (bQ p K r).coord i (M a c)) hX.eq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, Xc] at h ⊢
    simp only [mul_comm (X _ _) (inclK p K r _), inclK_mul, map_smul, smul_eq_mul] at h
    simpa [mul_comm] using h
  have hmem : ∀ i, Xc i ∈ GlobalTheory.PolyTensor.polySub p K n γ := by
    intro i
    obtain ⟨q, hq⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n γ (Xc i) hsep (hcomm i)
    rw [GlobalTheory.PolyTensor.mem_polySub, hq]
    exact Polynomial.aeval_mem_adjoin_singleton K γ
  let y : Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r) → GlobalTheory.PolyTensor.PolyAlg p K n γ := fun i => ⟨Xc i, hmem i⟩
  let e := Module.Basis.ofVectorSpace ℚ_[p] (Qr p r)
  let s : Finset (Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r)) :=
    Finset.univ.biUnion (fun ac : Fin n × Fin n => ((bQ p K r).repr (X ac.1 ac.2)).support)
  refine ⟨∑ i ∈ s, y i ⊗ₜ e i, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Matrix.ext fun a c => ?_
  simp only [GlobalTheory.PolyTensor.phi_tmul, Matrix.sum_apply, mul_algebraMap_apply, Matrix.map_apply]
  have hv : ∀ i, GlobalTheory.PolyTensor.val p K n γ (y i) = Xc i := fun i => rfl
  simp only [hv, Xc, Matrix.map_apply, inclK_mul, ← bQ_apply]
  simp only [e, ← bQ_apply, Module.Basis.coord_apply]
  have hsub : ((bQ p K r).repr (X a c)).support ⊆ s := fun i hi =>
    Finset.mem_biUnion.2 ⟨(a, c), Finset.mem_univ _, hi⟩
  rw [← Finsupp.sum_of_support_subset _ hsub (fun i k => k • bQ p K r i) (fun i _ => zero_smul _ _),
    ← Finsupp.linearCombination_apply, Module.Basis.linearCombination_repr]

end GlobalTheory.PolyTensorCommutant
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicPowMulMemTensorUnramifiedIntegersStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padic_pow_mul_mem_tensorUnramifiedIntegers : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : KQ p K r), ∃ k : ℕ, (p : KQ p K r) ^ k * x ∈ intKQ p K r := by
  first | (exact @GlobalTheory.LKRes.exists_pow_mul_mem_intKQ) | (exact GlobalTheory.LKRes.exists_pow_mul_mem_intKQ) | (intros; apply GlobalTheory.LKRes.exists_pow_mul_mem_intKQ  <;> assumption)
end

