module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinUnfoldingPeterssonEisensteinLatticeSum
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.EisM

def rkPsi (k : ℕ) (s : ℝ) (h b : ℕ → ℂ) (τ : ℍ) : ℂ :=
  conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)

theorem rankin_transf (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ)
    (h b : ℕ → ℂ) (s : ℝ) (hNL : N ∣ L) (hh : CF (2 * e + 1) L (ch ε) h) (hb : MF e L χ b)
    (hχ : ∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (τ : ℍ) :
    rkPsi (2 * e + 1) s h b (γ • τ) =
      φ ((γ 1 1 : ℤ) : ZMod L) * trm (e + 1) s (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * rkPsi (2 * e + 1) s h b τ := by
  set j : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hjdef
  have hdenom : UpperHalfPlane.denom γ τ = j := ModularGroup.denom_apply γ τ
  have hj : j ≠ 0 := by rw [← hdenom]; exact UpperHalfPlane.denom_ne_zero _ τ
  have him : (γ • τ).im = τ.im / Complex.normSq j := by rw [ModularGroup.im_smul_eq_div_normSq, hdenom]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨m, hm⟩ := hγ
  have hcop : IsCoprime (γ 1 1) (L : ℤ) := ⟨γ 0 0, -(γ 0 1 * m), by rw [hm] at hdet; linear_combination hdet⟩
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
    obtain ⟨n, hn⟩ := hNL
    have h1 : ((γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) : ℤ) : ZMod N) = 1 := by
      rw [hm, hn] at hdet; push_cast at hdet
      have : γ 1 1 * γ 0 0 + (-(γ 0 1 * m * n)) * (N : ℤ) = 1 := by linear_combination hdet
      rw [this]; simp
    push_cast at h1; simp only [mul_neg, neg_mul, ZMod.natCast_self, mul_zero, neg_zero, add_zero] at h1
    exact ⟨⟨_, ((γ 0 0 : ℤ) : ZMod N), h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hεε : conj (ch ε (γ 1 1)) * ch ε (γ 1 1) = 1 := by
    have hn : ‖ch ε (γ 1 1)‖ = 1 := by
      unfold ch; rw [← hunit.unit_spec]; exact DirichletCharacter.unit_norm_eq_one ε hunit.unit
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have hH := hh.1.2 γ ⟨m, hm⟩ τ
  have hB := hb.2 γ ⟨m, hm⟩ τ
  rw [hχ _ hcop] at hB
  rw [← hjdef] at hH hB
  have hNpos : 0 < Complex.normSq j := Complex.normSq_pos.2 hj
  have hy := τ.im_pos
  unfold rkPsi trm
  rw [hH, hB, him, Real.div_rpow hy.le hNpos.le, Real.rpow_add hNpos, Real.rpow_natCast]
  have hn2 : ‖j‖ ^ (-2 * s) = (Complex.normSq j ^ s)⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)]
    congr 1; push_cast; ring
  rw [hn2]
  have hP : (Complex.normSq j ^ s) ≠ 0 := (Real.rpow_pos_of_pos hNpos s).ne'
  have hcj : conj j ≠ 0 := by simpa using hj
  have hNc : ((Complex.normSq j : ℝ) : ℂ) = j * conj j := (Complex.mul_conj j).symm
  simp only [ch] at hεε ⊢
  have hε0 : ε ((γ 1 1 : ℤ) : ZMod N) ≠ 0 := by intro h0; rw [h0, mul_zero] at hεε; exact zero_ne_one hεε
  have hεc : conj (ε ((γ 1 1 : ℤ) : ZMod N)) = (ε ((γ 1 1 : ℤ) : ZMod N))⁻¹ := eq_inv_of_mul_eq_one_left hεε
  push_cast
  rw [hNc]
  simp only [map_mul, map_pow, hεc]
  field_simp
  ring_nf

theorem latF_kills (L : ℕ) (φ : DirichletCharacter ℂ L) (hφ : φ ≠ 1) :
    Kills L (0, 1) (latF L (fun _ => 1) φ) := by
  intro x
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL; simp
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have h0 : ∑ z : ZMod (n + 1), φ z = 0 := MulChar.sum_eq_zero_of_ne_one hφ
  unfold latF
  have e1 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).1 = x.1 := by intro r; simp
  by_cases hx : ((n + 1 : ℕ) : ℤ) ∣ x.1
  · have e2 : ∀ r : ℕ, (x - (r : ℤ) • ((0 : ℤ), (1 : ℤ))).2 = x.2 - r := by intro r; simp
    simp only [e1, e2, hx, if_true, one_mul]
    rw [← h0]
    refine Finset.sum_nbij' (fun r : ℕ => (((x.2 - r : ℤ)) : ZMod (n + 1)))
      (fun z => ((x.2 : ZMod (n + 1)) - z).val) (fun _ _ => Finset.mem_univ _)
      (fun z _ => Finset.mem_range.2 (ZMod.val_lt _)) ?_ ?_ (fun _ _ => rfl)
    · intro r hr
      have hr' : r < n + 1 := Finset.mem_range.1 hr
      simp [ZMod.val_cast_of_lt hr']
    · intro z _
      simp
  · simp only [e1, hx, if_false, Finset.sum_const_zero]

theorem rankin_summ (e : ℕ) (h b : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) (hs : 0 < s)
    (hb : ∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1))
    (hh : Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s)) :
    (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) ∧
      LSeriesSummable (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := hb
  have hb2 : Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((_root_.GlobalTheory.DivSq.summable_card_divisors_sq_div_rpow s hs).mul_left (C ^ 2))
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have : (2 * (e : ℝ) - 1 + s) ≠ 0 := by
        have : (1 : ℝ) ≤ e := by exact_mod_cast he
        linarith
      simp [Real.zero_rpow this]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have key : (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) = ((n : ℝ) ^ (e - 1)) ^ 2 * (n : ℝ) ^ (1 + s) := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hn0]
      congr 1; push_cast [Nat.cast_sub he]; ring
    have hA : 0 < (n : ℝ) ^ (e - 1) := by positivity
    have hB : 0 < (n : ℝ) ^ (1 + s) := Real.rpow_pos_of_pos hn0 _
    have hle := hC n hn.ne'
    rw [key, div_le_iff₀ (by positivity)]
    calc ‖b n‖ ^ 2 ≤ (C * n.divisors.card * (n : ℝ) ^ (e - 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = C ^ 2 * ((n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ (1 + s)) * (((n : ℝ) ^ (e - 1)) ^ 2 * (n : ℝ) ^ (1 + s)) := by
        field_simp
  refine ⟨hb2, ?_⟩
  unfold LSeriesSummable
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((hh.add hb2).div_const 2))
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [Complex.ofReal_re, norm_mul, Complex.norm_conj]
  have e1 : (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n * n := by
    rw [← Real.rpow_add_one hn0.ne', ← Real.rpow_add_one hn0.ne']; congr 1; push_cast; ring
  have e2 : (n : ℝ) ^ (2 * (e : ℝ) + s) = (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) * n := by
    rw [← Real.rpow_add_one hn0.ne']; congr 1; ring
  rw [e1, e2]
  have hu : 0 < (n : ℝ) ^ (2 * (e : ℝ) - 1 + s) := Real.rpow_pos_of_pos hn0 _
  set u := (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)
  set A := ‖h n‖
  set B := ‖b n‖
  have : (A ^ 2 / (u * n * n) + B ^ 2 / u) / 2 - A * B / (u * n) = (A - B * n) ^ 2 / (2 * u * n ^ 2) := by
    field_simp; ring
  have h2 : 0 ≤ (A - B * n) ^ 2 / (2 * u * n ^ 2) := by positivity
  linarith

theorem rankin_unfold : ∀ (e L N : ℕ) (ε : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ L) (χ : ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → 0 < L → N ∣ L → Wt L ρ → φ ≠ 1 → CF (2 * e + 1) L (ch ε) h → MF e L χ b → (∀ d : ℤ, IsCoprime d L → χ d = ch φ d * ch ε d) → (∃ C : ℝ, ∀ n, n ≠ 0 → ‖b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (e - 1)) → pet (2 * e + 1) ρ (qs h) (fun τ => qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) = LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) * (((Real.Gamma (2 * (e : ℝ) + s) / (4 * π) ^ (2 * (e : ℝ) + s) : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ)) := by
  intro e L N ε φ χ ρ h b s he hs hL hNL hρ hφ hh hb hχ hbC
  have hcont := fun a (ha : PolyB a) => (_root_.GlobalTheory.EisM.qs_summable_continuous a ha).2
  set Lφ := LSeries (fun n => φ n) ((e + 1 : ℕ) + 2 * s) with hLφ
  have hlat : ∀ τ : ℍ, lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ = Lφ *
      ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, φ (x.1.2 : ZMod L) * trm (e + 1) s ((x.1.1 : ℂ) * τ + x.1.2) := by
    intro τ
    have hb1 : ∃ C : ℝ, ∀ x, ‖latF L (fun _ => 1) φ x‖ ≤ C := ⟨1, fun x => by
      unfold latF; split_ifs <;> simp [DirichletCharacter.norm_le_one]⟩
    rw [(_root_.GlobalTheory.EisM.lat_eq_tsum_of_kills (e + 1) L s (0, 1) _ τ (by omega) hs hL hb1 (latF_kills L φ hφ)).2]
    exact GlobalTheory.T.eisenstein_lattice_sum_gcd_factor_out (e + 1) L s φ τ (by omega) hs hL
  set Ψ := rkPsi (2 * e + 1) s h b with hΨ
  set W : ℤ × ℤ → ℍ → ℂ := fun x τ => φ (x.2 : ZMod L) * trm (e + 1) s ((x.1 : ℂ) * τ + x.2) * Ψ τ with hW
  have hpt : ∀ τ : ℍ, (ρ τ : ℂ) * (conj (qs h τ) * (qs b τ * lat (e + 1) s L (0, 1) (latF L (fun _ => 1) φ) τ * ((τ.im ^ s : ℝ) : ℂ)) * (τ.im : ℂ) ^ (2 * e + 1)) =
      Lφ * ((ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ) := by
    intro τ
    rw [hlat τ]
    simp only [hW]
    rw [tsum_mul_right]
    have hy : ((τ.im ^ (((2 * e + 1 : ℕ) : ℝ) + s) : ℝ) : ℂ) = (τ.im : ℂ) ^ (2 * e + 1) * ((τ.im ^ s : ℝ) : ℂ) := by
      rw [Real.rpow_add τ.im_pos, Real.rpow_natCast]; push_cast; ring
    simp only [hΨ, rkPsi, hy]
    ring
  have hmsq := _root_.GlobalTheory.rankin_mean_square (2 * e + 1) L (ch ε) h (by omega) hh
  obtain ⟨hbsq, hLS⟩ := rankin_summ e h b s he hs hbC (by simpa using hmsq.2.2.1 s hs)
  have hint : IntegrableOn Ψ strip := by
    exact _root_.GlobalTheory.EisM.strip_integrable_rankin (2 * e + 1) e L N ε h b s rfl he hs hL hNL hh hb.1 hbsq
  have hmeas : AEStronglyMeasurable Ψ := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [hΨ, rkPsi]
    refine ((Complex.continuous_conj.comp (hcont h hh.1.1)).mul (hcont b hb.1)).mul (Complex.continuous_ofReal.comp ?_)
    exact (UpperHalfPlane.continuous_im).rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hunf := _root_.GlobalTheory.EisM.unfold_strip L ρ Ψ W hρ hint hmeas (fun γ hγ τ => by
    simpa [hW] using rankin_transf e L N ε φ χ h b s hNL hh hb hχ γ hγ τ)
  have hmel := _root_.GlobalTheory.EisM.strip_eq_LSeries h b (2 * (e : ℝ) + s) (by positivity) hh.1.1 hb.1 hmsq.1 hLS
  have hΨeq : (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((2 * (e : ℝ) + s) + 1) : ℝ) : ℂ)) = Ψ := by
    funext τ; simp only [hΨ, rkPsi]; congr 3; push_cast; ring
  rw [hΨeq] at hmel
  unfold pet
  simp_rw [hpt]
  rw [integral_const_mul, hunf, hmel hint]

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerRoots
section
noncomputable section

open Polynomial

namespace GlobalTheory.Compare.TeichmullerRoots

open Formalism.BasicNotions Formalism.CyclotomicNorms GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem zero_mem_rootsBar {f : (ZMod g)[X]} (hf : f.Monic) : 0 ∈ rootsBar f ↔ f.coeff 0 = 0 := by
  unfold rootsBar
  rw [mem_roots (hf.map _).ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map]
  exact map_eq_zero_iff _ (RingHom.injective _)

theorem exists_monic_of_stable (S : Multiset (Fbar g)) (hS : S.map (fun x => x ^ g) = S) :
    ∃ f : (ZMod g)[X], f.Monic ∧ rootsBar f = S := by
  set P : (Fbar g)[X] := (S.map fun x => X - C x).prod with hP
  have hm : P.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x
  have hfix : P.map (frobenius (Fbar g) g) = P := by
    rw [hP, Polynomial.map_multiset_prod, Multiset.map_map]
    conv_rhs => rw [← hS, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp [frobenius_def]
  have hl : P ∈ lifts (algebraMap (ZMod g) (Fbar g)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have h1 : P.coeff n ^ g = P.coeff n := by
      have := congrArg (fun q => q.coeff n) hfix
      simpa [frobenius_def] using this
    have h2 : P.coeff n ∈ (⊥ : Subfield (Fbar g)) := (Subfield.mem_bot_iff_pow_eq_self _ g).2 h1
    rw [Subfield.bot_eq_of_zMod_algebra g] at h2
    exact h2
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  unfold rootsBar
  rw [hq, hP, roots_multiset_prod_X_sub_C]

theorem root_pow_rootExp {N : ℕ} {f : (ZMod g)[X]} (hf : IsLabel N f) {x : Fbar g} (hx : x ∈ rootsBar f) :
    x ^ rootExp N g = 1 := by
  have hx0 : x ≠ 0 := fun h => hf.2.2 ((zero_mem_rootsBar hf.1).1 (h ▸ hx))
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hroot : aeval x f = 0 := by
    have := (mem_roots (hf.1.map _).ne_zero).1 hx
    rwa [IsRoot, eval_map_algebraMap] at this
  have hd : (minpoly (ZMod g) x).natDegree ≤ N := by
    rw [← hf.2.1]
    exact natDegree_le_of_dvd (minpoly.dvd _ _ hroot) hf.1.ne_zero
  have hd1 : 1 ≤ (minpoly (ZMod g) x).natDegree := minpoly.natDegree_pos hint
  set K := IntermediateField.adjoin (ZMod g) ({x} : Set (Fbar g))
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ (minpoly (ZMod g) x).natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hint]
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  rw [hc] at h1
  have h2 : x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) = 1 := by
    have := congrArg Subtype.val h1
    simpa [y] using this
  obtain ⟨c, hc⟩ : g ^ (minpoly (ZMod g) x).natDegree - 1 ∣ rootExp N g :=
    Finset.dvd_lcm (f := fun d => g ^ d - 1) (Finset.mem_Icc.2 ⟨hd1, hd⟩)
  rw [hc, pow_mul, h2, one_pow]

theorem roots_reverse_prod {F : Type} [Field F] (S : Multiset F) (hS : 0 ∉ S) :
    ((S.map fun x => X - C x).prod.reverse).roots = S.map fun x => x⁻¹ := by
  induction S using Multiset.induction_on with
  | empty => simp [reverse]
  | cons x S ih =>
    have hx : x ≠ 0 := fun h => hS (h ▸ Multiset.mem_cons_self _ _)
    have hS' : 0 ∉ S := fun h => hS (Multiset.mem_cons_of_mem h)
    have hm : (S.map fun x => X - C x).prod.Monic :=
      monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x
    have e : (X - C x).reverse = C (-x) * (X - C x⁻¹) := by
      have : (X - C x) = X + C (-x) := by simp [sub_eq_add_neg]
      rw [this, reverse_add_C, natDegree_X]
      have hX : (X : F[X]).reverse = 1 := by
        have := reverse_mul_X (1 : F[X])
        simpa [reverse] using this
      rw [hX, mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hx]
      simp; ring
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, roots_mul, ih hS', e,
      roots_C_mul _ (neg_ne_zero.2 hx), roots_X_sub_C, Multiset.map_cons, Multiset.singleton_add]
    exact mul_ne_zero (by rw [Ne, reverse_eq_zero]; exact X_sub_C_ne_zero x)
      (by rw [Ne, reverse_eq_zero]; exact hm.ne_zero)

theorem dual_spec {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (C (f.coeff 0)⁻¹ * f.reverse).Monic ∧ IsPowLabel (-1) f (C (f.coeff 0)⁻¹ * f.reverse) := by
  constructor
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0, inv_mul_cancel₀ h0]
  · have e : f.map (algebraMap (ZMod g) (Fbar g)) = ((rootsBar f).map fun x => X - C x).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hm.map _)
        (IsAlgClosed.card_roots_eq_natDegree)).symm
    have e2 : f.reverse.map (algebraMap (ZMod g) (Fbar g)) = (f.map (algebraMap (ZMod g) (Fbar g))).reverse := by
      rw [reverse, reverse, natDegree_map, reflect_map]
    unfold IsPowLabel
    simp only [zpow_neg_one]
    rw [← roots_reverse_prod _ (fun h => h0 ((zero_mem_rootsBar hm).1 h)), ← e, ← e2]
    unfold rootsBar
    rw [Polynomial.map_mul, map_C, roots_C_mul]
    exact (_root_.map_ne_zero _).2 (inv_ne_zero h0)

theorem teich_injective (t : Fbar g →* ℂ) (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) :
    Function.Injective t := by
  have hne : ∀ x, x ≠ 0 → t x ≠ 0 := fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero
  have h0 : t 0 = 0 := by
    classical
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Fbar g))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    by_contra h
    have : t 0 * t y = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
    exact hy.2 (ht _ _ hy.1 one_ne_zero (mul_left_cancel₀ h this))
  intro x y h
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · rw [hx, hy]
    · exact absurd (by rw [← h, hx, h0]) (hne y hy)
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, h0]) (hne x hx)
    · exact ht x y hx hy h

theorem teich_zpow (t : Fbar g →* ℂ) {x : Fbar g} (hx : x ≠ 0) (a : ℤ) : t (x ^ a) = t x ^ a := by
  have h1 : t ((Units.mk0 x hx ^ a : (Fbar g)ˣ) : Fbar g) = ((Units.map t (Units.mk0 x hx) ^ a : ℂˣ) : ℂ) := by
    rw [← map_zpow]; rfl
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val] at h1
  exact h1

end Roots

variable (D : D7)

theorem labAct_eq (k : Fin 2) (α : ℂ ≃+* ℂ) (a : ℤ)
    (ha : ∀ ζ : ℂ, ζ ^ rootExp D.R.r (D.host.g k) = 1 → α ζ = ζ ^ a)
    {f f' : (ZMod (D.host.g k))[X]} (hf : IsLabel D.R.r f) (hm : f'.Monic)
    (hp : haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; IsPowLabel a f f') :
    Formalism.MainNotions.ArithmeticCylinders.labAct D α k f = f' := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hinj := teich_injective (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
  have e : (rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (α (D.ntypes.teichC k x))) =
      (rootsBar f).map fun x => x ^ a := by
    apply Multiset.map_congr rfl
    intro x hx
    have hx0 : x ≠ 0 := fun h => hf.2.2 ((zero_mem_rootsBar hf.1).1 (h ▸ hx))
    rw [ha _ (by rw [← map_pow, root_pow_rootExp hf hx, map_one]), ← teich_zpow _ hx0]
    exact Function.leftInverse_invFun hinj _
  have hs := Classical.epsilon_spec (p := fun q : (ZMod (D.host.g k))[X] => q.Monic ∧
    rootsBar q = (rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (α (D.ntypes.teichC k x))))
    ⟨f', hm, hp.trans e.symm⟩
  exact IsPowLabel.unique (a := a) (f := f) (hs.2.trans e) hp hs.1 hm

end GlobalTheory.Compare.TeichmullerRoots

end
end

