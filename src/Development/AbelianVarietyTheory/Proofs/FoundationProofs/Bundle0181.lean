module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerIntertwinesHeckeOperators
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.CyclotomicNorms.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BadRowsShareBoundTwoPrimes
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.ShareThm

theorem real_step (ep x w₁ w₂ W₁ W₂ D D₀ D₁ D₂ : ℝ) (h0 : 0 ≤ ep) (h1 : ep < 1) (hD : 0 ≤ D)
    (hall : |D - x| ≤ ep * x) (h₁ : |D₁ - w₁ * x| ≤ ep * (w₁ * x)) (h₂ : |D₂ - w₂ * x| ≤ ep * (w₂ * x))
    (hw₁ : w₁ ≤ W₁) (hw₂ : w₂ ≤ W₂) (hs : D ≤ D₀ + D₁ + D₂) :
    (1 - (1 + ep) / (1 - ep) * (max 0 W₁ + max 0 W₂)) * D ≤ D₀ := by
  obtain ⟨ha, hb⟩ := abs_le.mp hall
  have hc := (abs_le.mp h₁).2
  have hd := (abs_le.mp h₂).2
  have hx : 0 ≤ x := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hpos : 0 < 1 - ep := by linarith
  have hxD : x ≤ D / (1 - ep) := by
    rw [le_div_iff₀ hpos]; nlinarith
  have m₁ : w₁ ≤ max 0 W₁ := hw₁.trans (le_max_right _ _)
  have m₂ : w₂ ≤ max 0 W₂ := hw₂.trans (le_max_right _ _)
  have p₁ : 0 ≤ max 0 W₁ := le_max_left _ _
  have p₂ : 0 ≤ max 0 W₂ := le_max_left _ _
  set A := max 0 W₁
  set B := max 0 W₂
  have e₁ : D₁ + D₂ ≤ (1 + ep) * ((w₁ + w₂) * x) := by nlinarith
  have e₂ : (w₁ + w₂) * x ≤ (A + B) * (D / (1 - ep)) :=
    (mul_le_mul_of_nonneg_right (add_le_add m₁ m₂) hx).trans
      (mul_le_mul_of_nonneg_left hxD (add_nonneg p₁ p₂))
  have e₃ : D₁ + D₂ ≤ (1 + ep) * ((A + B) * (D / (1 - ep))) :=
    e₁.trans (mul_le_mul_of_nonneg_left e₂ (by linarith))
  have e₄ : (1 - (1 + ep) / (1 - ep) * (A + B)) * D = D - (1 + ep) * ((A + B) * (D / (1 - ep))) := by
    ring
  rw [e₄]; linarith

theorem abstract_step (H₁ H₂ : Type) [Group H₁] [Fintype H₁] [Group H₂] [Fintype H₂]
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (H₁ × H₂) M)
    (U₁ : H₁ → Prop) (U₂ : H₂ → Prop) (E₁ A₁ : H₁ → ℂ) (E₂ A₂ : H₂ → ℂ)
    (hE₁ : IsProj E₁) (hE₂ : IsProj E₂) (hA₁ : IsProj A₁) (hA₂ : IsProj A₂)
    (c₁ : ∀ a, conv A₁ a = conv a A₁) (c₂ : ∀ a, conv A₂ a = conv a A₂)
    (u₁ : ∀ γ, E₁ γ ≠ 0 → U₁ γ) (u₂ : ∀ γ, E₂ γ ≠ 0 → U₂ γ)
    (w₁ w₂ W₁ W₂ : ℝ) (hw₁ : conv (dirac - A₁) E₁ 1 = (w₁ : ℂ) * E₁ 1) (hw₂ : conv (dirac - A₂) E₂ 1 = (w₂ : ℂ) * E₂ 1)
    (hW₁ : w₁ ≤ W₁) (hW₂ : w₂ ≤ W₂) (ep c : ℝ) (h0 : 0 ≤ ep) (h1 : ep < 1)
    (hc : ∀ e : H₁ × H₂ → ℂ, IsProj e → ((∀ γ, e γ ≠ 0 → U₁ γ.1) ∨ ∀ γ, e γ ≠ 0 → U₂ γ.2) →
      |(rk ρ e : ℝ) - c * (e 1).re| ≤ ep * (c * (e 1).re)) :
    (1 - (1 + ep) / (1 - ep) * (max 0 W₁ + max 0 W₂)) * (rk ρ (tens2 E₁ E₂) : ℝ)
      ≤ (rk ρ (conv (tens2 A₁ A₂) (tens2 E₁ E₂)) : ℝ) := by
  obtain ⟨hop, hone, -, -, -, -, -⟩ := _root_.GlobalTheory.BadShare.convCalc (H₁ × H₂) M ρ
  obtain ⟨-, -, has₁, hd₁, hp₁, hq₁, -⟩ := _root_.GlobalTheory.BadShare.convCalc H₁ ℂ 1
  obtain ⟨-, -, has₂, hd₂, hp₂, hq₂, -⟩ := _root_.GlobalTheory.BadShare.convCalc H₂ ℂ 1
  obtain ⟨-, -, tc, tp, td, ts⟩ := _root_.GlobalTheory.BadShare.tens_calculus Unit H₁ H₂
  have P₁ : IsProj (conv (dirac - A₁) E₁) := hp₁ _ _ (hq₁ _ hA₁) hE₁ (by
    rw [(has₁ dirac A₁ E₁).2.1, (has₁ dirac A₁ E₁).2.2, (hd₁ E₁).1, (hd₁ E₁).2, c₁])
  have P₂ : IsProj (conv (dirac - A₂) E₂) := hp₂ _ _ (hq₂ _ hA₂) hE₂ (by
    rw [(has₂ dirac A₂ E₂).2.1, (has₂ dirac A₂ E₂).2.2, (hd₂ E₂).1, (hd₂ E₂).2, c₂])
  have kall := hc (tens2 E₁ E₂) (tp _ _ hE₁ hE₂) (Or.inr fun γ h => u₂ _ (right_ne_zero_of_mul h))
  have k₁ := hc (tens2 (conv (dirac - A₁) E₁) E₂) (tp _ _ P₁ hE₂) (Or.inr fun γ h => u₂ _ (right_ne_zero_of_mul h))
  have k₂ := hc (tens2 E₁ (conv (dirac - A₂) E₂)) (tp _ _ hE₁ P₂) (Or.inl fun γ h => u₁ _ (left_ne_zero_of_mul h))
  have v₁ : c * (tens2 (conv (dirac - A₁) E₁) E₂ 1).re = w₁ * (c * (tens2 E₁ E₂ 1).re) := by
    simp only [tens2, Prod.fst_one, Prod.snd_one, hw₁, mul_assoc, Complex.re_ofReal_mul]; ring
  have v₂ : c * (tens2 E₁ (conv (dirac - A₂) E₂) 1).re = w₂ * (c * (tens2 E₁ E₂ 1).re) := by
    simp only [tens2, Prod.fst_one, Prod.snd_one, hw₂]
    rw [mul_left_comm (E₁ 1), Complex.re_ofReal_mul]; ring
  rw [v₁] at k₁
  rw [v₂] at k₂
  have hs := _root_.GlobalTheory.BadShare.finrank_range_le_three M (op ρ (tens2 E₁ E₂)) (op ρ (tens2 A₁ dirac)) (op ρ (tens2 dirac A₂))
  have r₀ : op ρ (tens2 A₁ dirac) * op ρ (tens2 dirac A₂) * op ρ (tens2 E₁ E₂)
      = op ρ (conv (tens2 A₁ A₂) (tens2 E₁ E₂)) := by
    rw [← (hop _ _).1, ← (hop _ _).1, tc A₁ dirac, (hd₁ A₁).2, (hd₂ A₂).1]
  have r₁ : (1 - op ρ (tens2 A₁ dirac)) * op ρ (tens2 E₁ E₂) = op ρ (tens2 (conv (dirac - A₁) E₁) E₂) := by
    rw [← hone, ← td, ← (hop _ _).2.1, ← (ts dirac A₁ dirac dirac).1, ← (hop _ _).1, tc, (hd₂ E₂).1]
  have r₂ : (1 - op ρ (tens2 dirac A₂)) * op ρ (tens2 E₁ E₂) = op ρ (tens2 E₁ (conv (dirac - A₂) E₂)) := by
    rw [← hone, ← td, ← (hop _ _).2.1, ← (ts dirac dirac dirac A₂).2, ← (hop _ _).1, tc, (hd₁ E₁).1]
  rw [r₀, r₁, r₂] at hs
  refine real_step ep _ w₁ w₂ W₁ W₂ _ _ _ _ h0 h1 (Nat.cast_nonneg _) kall k₁ k₂ hW₁ hW₂ ?_
  unfold rk
  exact_mod_cast hs

theorem level_proj (g : ℕ) [Fact g.Prime] (N : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) :
    IsProj (tens fun v => (L v).e) ∧ ∀ γ, (tens fun v => (L v).e) γ ≠ 0 → AllUnip γ := by
  constructor
  · refine (_root_.GlobalTheory.BadShare.tens_calculus ι (GG g N) Unit).2.1 _ fun v => ?_
    obtain ⟨a, b, c, d, -⟩ := _root_.GlobalTheory.BadShare.LevGroup.lev_group g N (L v)
    exact (_root_.GlobalTheory.BadShare.EpsProj.eps_spec (GG g N) ℂ 1 _ _ a b c d).1
  · intro γ h v
    apply (_root_.GlobalTheory.BadShare.LevGroup.lev_group g N (L v)).2.2.2.2
    have h' : (L v).e (γ v) ≠ 0 := Finset.prod_ne_zero_iff.mp h v (Finset.mem_univ v)
    by_contra hn
    exact h' (by simp [Lev.e, eps, hn])

theorem bad_share : ∀ (g₁ g₂ : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (N m q d : ℕ) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂], 100000 ≤ N → PrimeOK g₁ q d → PrimeOK g₂ q d → ∀ (L₁ : ι₁ → Lev g₁ N) (L₂ : ι₂ → Lev g₂ N) (τ₁ : ι₁ → (ZMod g₁)[X] → GG g₁ N → ℂ) (τ₂ : ι₂ → (ZMod g₂)[X] → GG g₂ N → ℂ), (∀ v, IsSeries (τ₁ v)) → (∀ v, IsSeries (τ₂ v)) → ∀ (ch₁ : ι₁ → Fin m → (ZMod g₁)ˣ) (ch₂ : ι₂ → Fin m → (ZMod g₂)ˣ) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) (ep : ℝ), 0 ≤ ep → ep < 1 → CountAt ρ ep → (1 - (1 + ep) / (1 - ep) * (max 0 (badBound g₁ (Fintype.card ι₁) m N ((min q d : ℕ) : ℝ)) + max 0 (badBound g₂ (Fintype.card ι₂) m N ((min q d : ℕ) : ℝ)))) * (rk ρ (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e)) : ℝ) ≤ (rk ρ (conv (tens2 (eGood τ₁ ch₁) (eGood τ₂ ch₂)) (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e))) : ℝ) := by
  intro g₁ g₂ _ _ N m q d ι₁ ι₂ _ _ hN ok₁ ok₂ L₁ L₂ τ₁ τ₂ s₁ s₂ ch₁ ch₂ M _ _ _ ρ ep h0 h1 hc
  obtain ⟨c, -, hc⟩ := hc
  obtain ⟨pE₁, u₁⟩ := level_proj g₁ N ι₁ L₁
  obtain ⟨pE₂, u₂⟩ := level_proj g₂ N ι₂ L₂
  obtain ⟨pA₁, c₁⟩ := _root_.GlobalTheory.BadShare.eGood_isProj_central g₁ N m ι₁ τ₁ ch₁ s₁
  obtain ⟨pA₂, c₂⟩ := _root_.GlobalTheory.BadShare.eGood_isProj_central g₂ N m ι₂ τ₂ ch₂ s₂
  obtain ⟨w₁, hw₁, hW₁⟩ := _root_.GlobalTheory.BadShare.badWeight_le g₁ N m q d ι₁ L₁ τ₁ ch₁ hN ok₁ s₁
  obtain ⟨w₂, hw₂, hW₂⟩ := _root_.GlobalTheory.BadShare.badWeight_le g₂ N m q d ι₂ L₂ τ₂ ch₂ hN ok₂ s₂
  exact abstract_step _ _ M ρ AllUnip AllUnip _ _ _ _ pE₁ pE₂ pA₁ pA₂ c₁ c₂ u₁ u₂ w₁ w₂ _ _ hw₁ hw₂ hW₁ hW₂
    ep c h0 h1 hc

end GlobalTheory.BadShare.ShareThm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigenfunctionalAllCharactersOfAtkinLehner
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lam_add' (B : ℕ) (c a b : ℕ → ℂ) : lam B c (a + b) = lam B c a + lam B c b := by
  simp only [lam, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem lam_smul' (B : ℕ) (c a : ℕ → ℂ) (z : ℂ) : lam B c (z • a) = z * lam B c a := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem slz_add' (k : ℕ) (δ : M2) (f g : ℍ → ℂ) : slz k δ (f + g) = slz k δ f + slz k δ g := by
  funext τ; simp only [slz, Pi.add_apply]; ring

theorem slz_smul' (k : ℕ) (δ : M2) (z : ℂ) (f : ℍ → ℂ) : slz k δ (z • f) = z • slz k δ f := by
  funext τ; simp only [slz, Pi.smul_apply, smul_eq_mul]; ring

theorem eigAll_of_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ)
    (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N →
    EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c → ∃ (B' : ℕ) (c' : ℕ → ℂ), EigAll k N l χ g (χ l * α) B' c' ∧
    ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' →
      qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a' := by
  intro k N l χ g α B c a₀ b₀ c₀ d₀ hdet hk hN hl hlN hE
  set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδ
  have hL : 0 < N * l := Nat.mul_pos hN hl.pos
  obtain ⟨hz1, hadd1, hsm1, -, -, -⟩ := mf_linear k (N * l) (ch χ)
  obtain ⟨hz2, hadd2, hsm2, -, -, -⟩ := mf_linear k (N * l) (ch χ⁻¹)

  have uniq : ∀ x y, MF k (N * l) (ch χ⁻¹) x → MF k (N * l) (ch χ⁻¹) y → qs x = qs y → x = y :=
    fun x y hx hy h => qs_injective x y hx.1 hy.1 h
  let S : Set (ℕ → ℂ) := {a | MF k (N * l) (ch χ) a}
  classical
  let φ : (ℕ → ℂ) → ℂ := fun a =>
    if h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) then lam B c h.choose else 0
  have hφ : ∀ a a', MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) → φ a = lam B c a' := by
    intro a a' h1 h2
    have h : ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) := ⟨a', h1, h2⟩
    simp only [φ, dif_pos h]
    rw [uniq _ _ h.choose_spec.1 h1 (h.choose_spec.2.trans h2.symm)]
  have hex : ∀ a, MF k (N * l) (ch χ) a → ∃ a', MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k δ (qs a) :=
    fun a ha => _root_.GlobalTheory.EisM.atkinLehner_MF k N l χ a a₀ b₀ c₀ d₀ hdet hk hN ha
  obtain ⟨B₀, hB₀⟩ := sturm_coef_zero k (N * l) N χ hL (dvd_mul_right N l)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.func_eq_lam S B₀ φ hz1
    (by
      intro a ha b hb
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨b', hb', eb⟩ := hex b hb
      obtain ⟨hab, hqab⟩ := hadd1 a b ha hb
      obtain ⟨hab', hqab'⟩ := hadd2 a' b' ha' hb'
      refine ⟨hab, ?_⟩
      rw [hφ a a' ha' ea, hφ b b' hb' eb, hφ (a + b) (a' + b') hab' (by rw [hqab', hqab, slz_add', ea, eb]),
        lam_add'])
    (by
      intro z a ha
      obtain ⟨a', ha', ea⟩ := hex a ha
      obtain ⟨hza, hqza⟩ := hsm1 z a ha
      obtain ⟨hza', hqza'⟩ := hsm2 z a' ha'
      refine ⟨hza, ?_⟩
      rw [hφ a a' ha' ea, hφ (z • a) (z • a') hza' (by rw [hqza', hqza, slz_smul', ea]), lam_smul'])
    (fun a ha h => hB₀ a ha h)
  obtain ⟨B', c', hagree, hkill⟩ := _root_.GlobalTheory.lam_extend_by_zero k (N * l) N χ B₀ c₁ hL (dvd_mul_right N l)
  have key : ∀ a a', MF k (N * l) (ch χ) a → MF k (N * l) (ch χ⁻¹) a' → qs a' = slz k δ (qs a) →
      lam B' c' a = lam B c a' := by
    intro a a' ha ha' e
    rw [hagree a ha, ← hc₁ a ha, hφ a a' ha' e]
  refine ⟨B', c', ⟨⟨?_, ?_⟩, hkill⟩, key⟩
  · intro a ha q hq hqNl
    obtain ⟨a', ha', ea⟩ := hex a ha
    have hqN : ¬ q ∣ N := fun h => hqNl (dvd_mul_of_dvd_left h l)
    obtain ⟨hT, -⟩ := _root_.GlobalTheory.EisM.AtkinLehner.alHecke k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hTa : MF k (N * l) (ch χ) (To k (ch χ q) q a) :=
      _root_.GlobalTheory.EisM.To_MF k (N * l) N q χ a hk (dvd_mul_right N l) hq hqNl ha
    have hTa' : MF k (N * l) (ch χ⁻¹) (To k (ch χ⁻¹ q) q a') :=
      _root_.GlobalTheory.EisM.To_MF k (N * l) N q χ⁻¹ a' hk (dvd_mul_right N l) hq hqNl ha'
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ q) _ hTa'
    rw [key _ _ hTa hs (by rw [hqs, hT q hq hqNl]), lam_smul', hE.T a' ha' q hq hqNl, key a a' ha ha' ea]
    have hunit : IsUnit ((q : ℕ) : ZMod N) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
    have h1 : χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = 1 := by
      rw [show χ (q : ZMod N) * χ⁻¹ (q : ZMod N) = (χ * χ⁻¹) (q : ZMod N) by rw [MulChar.coeToFun_mul]; rfl,
        mul_inv_cancel, MulChar.one_apply hunit]
    simp only [ch, Int.cast_natCast]
    linear_combination (g q * lam B c a') * h1
  · intro a ha
    obtain ⟨a', ha', ea⟩ := hex a ha
    obtain ⟨-, hU⟩ := _root_.GlobalTheory.EisM.AtkinLehner.alHecke k N l χ a a' a₀ b₀ c₀ d₀ hdet hk hN hl hlN ha ha' ea
    have hper : ∀ (ε : DirichletCharacter ℂ N) (d : ℤ), ch ε (d + (N * l : ℕ)) = ch ε d := by
      intro ε d
      simp [ch]
    have hUa := (_root_.GlobalTheory.depletion_mf k (N * l) l (ch χ) a hk hl (dvd_mul_left l N) (hper χ) ha).1
    have hUa' := (_root_.GlobalTheory.depletion_mf k (N * l) l (ch χ⁻¹) a' hk hl (dvd_mul_left l N) (hper χ⁻¹) ha').1
    obtain ⟨hs, hqs⟩ := hsm2 (ch χ l) _ hUa'
    rw [key _ _ hUa hs (by rw [hqs, hU]), lam_smul', hE.U a' ha', key a a' ha ha' ea]
    simp only [ch, Int.cast_natCast]
    ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularForm
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisPer

theorem per_val {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (n : ℤ) :
    a n = a (((n : ZMod N).val : ℕ) : ℤ) := by
  have hp : Function.Periodic a (N : ℤ) := ha
  rw [ZMod.val_intCast]
  have := hp.int_mul (n / N) (n % N)
  simp only [Int.cast_id] at this
  rw [← this]
  congr 1
  have := Int.mul_ediv_add_emod n N
  linarith [mul_comm (N : ℤ) (n / N)]

theorem sum_range_zmod {N : ℕ} [NeZero N] (g : ZMod N → ℂ) :
    ∑ y ∈ Finset.range N, g (y : ZMod N) = ∑ z : ZMod N, g z := by
  refine Finset.sum_bij' (fun y _ => (y : ZMod N)) (fun z _ => z.val) (by simp)
    (fun z _ => by simpa using ZMod.val_lt z) (fun y hy => ZMod.val_cast_of_lt (Finset.mem_range.1 hy))
    (fun z _ => ZMod.natCast_zmod_val z) (fun _ _ => rfl)

def invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (y : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ x : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y))

theorem hat_invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) :
    hat (invF (N := N) a) d = a d := by
  unfold hat
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have e1 : ∀ y : ℕ, cexp (2 * π * Complex.I * (y * d) / N) = ZMod.stdAddChar ((y : ZMod N) * (d : ZMod N)) := by
    intro y
    have := ZMod.stdAddChar_coe (N := N) ((y : ℤ) * d)
    push_cast at this
    rw [← this]
  simp_rw [e1]
  rw [sum_range_zmod (fun z => invF a z * ZMod.stdAddChar (z * (d : ZMod N)))]
  unfold invF
  simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e2 : ∀ x y : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y)) * ZMod.stdAddChar (y * (d : ZMod N))
      = a (x.val : ℤ) * ZMod.stdAddChar (y * ((d : ZMod N) - x)) := by
    intro x y
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [e2]
  simp_rw [← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp_rw [ZMod.card, Nat.cast_ite, Nat.cast_zero, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (d : ZMod N) (fun x => a (x.val : ℤ) * (N : ℂ))]
  simp only [Finset.mem_univ, if_true]
  rw [← per_val a ha d]
  field_simp

theorem invF_twist {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) (c : ℂ)
    (hd : IsCoprime d (N : ℤ)) (hmul : ∀ x, a (x * d) = c * a x) (y : ZMod N) :
    invF (N := N) a y = c * invF (N := N) a (y * (d : ZMod N)) := by
  obtain ⟨u, v, huv⟩ := hd
  have hu : (u : ZMod N) * (d : ZMod N) = 1 := by
    have := congrArg (fun t : ℤ => (t : ZMod N)) huv
    simpa using this
  let U : (ZMod N)ˣ := ⟨(d : ZMod N), (u : ZMod N), by rw [mul_comm]; exact hu, hu⟩
  unfold invF
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have e : ∀ x : ZMod N, c * ((N : ℂ)⁻¹ * (a (x.val : ℤ) * ZMod.stdAddChar (-(x * (y * (d : ZMod N))))))
      = (N : ℂ)⁻¹ * (a ((x * (d : ZMod N)).val : ℤ) * ZMod.stdAddChar (-((x * (d : ZMod N)) * y))) := by
    intro x
    have h1 : a ((x * (d : ZMod N)).val : ℤ) = c * a (x.val : ℤ) := by
      rw [← hmul, per_val a ha ((x.val : ℤ) * d)]
      congr 3
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h1]
    have h2 : -(x * (y * (d : ZMod N))) = -((x * (d : ZMod N)) * y) := by ring
    rw [h2]; ring
  exact (Fintype.sum_equiv (Units.mulRight U) _ _ e).symm

end GlobalTheory.EisPer

end

open GlobalTheory.EisPer in
theorem GlobalTheory.eis_periodic_weights : ∀ (j L₁ L₂ : ℕ) (a b χ₁ χ₂ : ℤ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → a 0 = 0 → (∀ x, a (x + L₁) = a x) → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ x, a (x * d) = χ₁ d * a x) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c a b) := by
  intro j L₁ L₂ a b χ₁ χ₂ hj hL₁ hL₂ ha0 ha hb hχ hpar
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  have hhat : hat (invF (N := L₁) a) = a := funext (hat_invF a ha)
  obtain ⟨c, hc, -⟩ := _root_.GlobalTheory.EisForm.eis_latF_mf j L₁ L₂ b χ₁ χ₂ (invF (N := L₁) a) hj hL₁ hL₂
    (by rw [hhat]; exact ha0) hb
    (fun d hd => ⟨fun y => invF_twist a ha d (χ₁ d)
      (by
        have : IsCoprime d ((L₁ : ℤ) * (L₂ : ℤ)) := by exact_mod_cast hd
        exact this.of_mul_right_left) (hχ d hd).1 y, (hχ d hd).2⟩) hpar
  exact ⟨c, by rw [hhat] at hc; exact hc⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteLevelApproxOfGeometricInvariantModPoStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteLevel_approx_of_geometric_invariant_modPow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ x : Ω, IsInt (p := p) x →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (g x) x) →
  ∃ y : Ω, IsInt (p := p) y ∧ (∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) ∧
    Cong (p := p) k ((T.ζ j - 1) * x) y := by
  intro p _ hp2 Ω _ _ hClo T k j hj x hx hfix
  obtain ⟨y₀, E, hy₀, hEH, huniq, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hClo T
      (Ggeo p Ω ⊓ ⨅ n, Gn T n) inf_le_right {x} j hj
  have hgi (g : Gal p Ω) (z : Ω) (hz : IsInt (p := p) z) : IsInt (p := p) (g z) :=
    hz.map (g : Ω →ₐ[O0 p] Ω)
  have hlevel := GlobalTheory.K5.GeoLevel.exists_level_of_fixed hClo T _
    (GlobalTheory.K5.FinLevel.sum_fixed _ E y₀ x hEH huniq)
  refine ⟨∑ g ∈ E, g (y₀ * x), IsIntegral.sum _ (fun g _ => hgi g _ (hy₀.mul hx)), hlevel, ?_⟩
  have hz : ∀ g ∈ E, ∃ z : Ω, IsInt (p := p) z ∧ g x - x = (p : Ω) ^ k * z :=
    fun g hg => hfix g (hEH g hg)
  choose! z hzi hzx using hz
  refine ⟨-∑ g ∈ E, g y₀ * z g, ?_, ?_⟩
  · exact (IsIntegral.sum _ fun g hg => (hgi g _ hy₀).mul (hzi g hg)).neg
  · rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [map_mul]
    linear_combination (-(g y₀)) * hzx g hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup
section
noncomputable section

namespace GlobalTheory.PointIrredCompare

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open scoped Pointwise

section Galois

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem mem_smul_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem valuation_smul_lt_one_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_smul_iff, mem_smul_iff, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]

theorem conj_mem_Ine_of_smul {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, mem_smul_iff]
      have : (g⁻¹ : G F Ω) (g x) = x := by
        show (g⁻¹ * g) x = x
        simp
      rw [this]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (valuation_smul_lt_one_iff A g _).1 (hσ.2 _ hx')
    have e : (g⁻¹ : G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      rw [map_sub]
      congr 1
      show (g⁻¹ * g) x = x
      simp
    rwa [e] at h

theorem Ine_le_of_normal [IsAlgClosure F Ω] {A B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A w) (hB : IsPlaceOver B w) (Hs : Subgroup (G F Ω)) [hn : Hs.Normal]
    (h : Ine (F := F) A ≤ Hs) : Ine (F := F) B ≤ Hs := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver hA hB
  intro σ hσ
  have := hn.conj_mem _ (h (conj_mem_Ine_of_smul hσ)) g
  simpa [mul_assoc] using this

end Galois

section Hyps

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpDim_spehLoc (p : Part A.CG) (w : PlE H) : A.lpDim (spehLoc N A p w) = p.a * p.d := by
  have h : ∀ l : List ℝ, A.lpDim (l.foldr
      (fun k acc => A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) acc) (A.lpZero w)) =
      p.a * l.length := by
    intro l
    induction l with
    | nil => simp [A.lpDim_zero]
    | cons a l ih => simp only [List.foldr_cons, A.lpDim_sum, A.lpDim_tw, A.locG_dim, ih, List.length_cons]; ring
  unfold spehLoc
  rw [h]
  simp

theorem lpDim_isoLoc (P : List (Part A.CG)) (w : PlE H) : A.lpDim (isoLoc N A P w) = rankIso N A P := by
  induction P with
  | nil => simp [isoLoc, rankIso, A.lpDim_zero]
  | cons p P ih =>
    have : isoLoc N A (p :: P) w = A.lpSum (spehLoc N A p w) (isoLoc N A P w) := rfl
    rw [this, A.lpDim_sum, ih, lpDim_spehLoc]
    simp [rankIso]

theorem rank_of_hasParamX {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso N A Sig = R.r := by
  obtain ⟨P, -, h1, -, h3, -⟩ := h
  refine ⟨fun p hp => ?_, ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · simp only [rankIso, twistIso, muPart, List.map_map, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Ranks.nV] at h3 ⊢
    have e : List.map ((fun p : Part A.CG => p.a * p.d) ∘
        fun p : Part A.CG => (⟨p.a, A.tw p.π A.etaTinv, p.d⟩ : Part A.CG)) Sig =
        List.map (fun p : Part A.CG => p.a * p.d) Sig := rfl
    rw [e] at h3
    omega

def FullLabels (Sig : List (Part A.CG)) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    (A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))).natDegree = A.lpDim (isoLoc N A Sig (A.plGw k v))

theorem fullLabels_of_good {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig)
    (hg : goodSig N A Sig) : FullLabels N A Sig := fun k v => by
  rw [lpDim_isoLoc, (rank_of_hasParamX N A h).2]
  exact ((hg k).1.1 v).2.1


end Hyps

end GlobalTheory.PointIrredCompare

end
end

