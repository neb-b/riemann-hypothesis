module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsProportionalOfSqLaw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralHarmonicNeZeroAndIsHomogeneousStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralHarmonic_ne_zero_and_isHomogeneous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (Dom a n → Dw.p + Dw.q ≤ n → ∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) ∧ ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P.IsHomogeneous (Formalism.L2.Pj.DF Dw a) := by
  first | exact @GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous | exact GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous | (intros; apply GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExpNsmulEqPowVt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

private theorem AnFr.exp_nsmul_eq_pow_vt {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (z : Fin g → ℂ) (n : ℕ) : Φ.e (n • z) = Φ.e z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [succ_nsmul, Φ.e_add, ih, pow_succ]

theorem rd_vt_and_uu : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (N : ℕ), Odd N → ∀ (s : LB.Sec (LPow A L.L 1 (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Φ.Rd 1 s θ → (∀ (ok : (Over.mk x0 ⟶ A) → Prop) (t : Over.mk x0 ⟶ A) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))), IsVtOver A L N ok s t F → (∀ t', ok t' → t' ^ N = t → t' ^ (N ^ 2) = 1) → ∃ x δ : Fin g → ℂ, δ ∈ Φ.lat ∧ ((N : ℂ) ^ 2) • x = (2 : ℂ) • δ ∧ ok (Φ.e x) ∧ Φ.e x ^ N = t ∧ Φ.Rd ((N : ℤ) ^ 2) F (fock Φ.Hm ((N : ℤ) ^ 2) x fun z => θ ((N : ℂ) • z))) ∧ ∀ (x₁ δ₁ x₂ δ₂ : Fin g → ℂ) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))), δ₁ ∈ Φ.lat → ((N : ℂ) ^ 2) • x₁ = (2 : ℂ) • δ₁ → δ₂ ∈ Φ.lat → ((N : ℂ) ^ 2) • x₂ = (2 : ℂ) • δ₂ → IsUUOver A L N s (Φ.e x₁) (Φ.e x₂) F → Φ.Rd ((N : ℤ) ^ 2) F (fock Φ.Hm ((N : ℤ) ^ 2) x₂ (fock Φ.Hm ((N : ℤ) ^ 2) x₁ fun z => θ ((N : ℂ) • z))) := by
  intro S A _ _ L x0 g Φ hχ N hN s θ hs
  have hN2 : Odd (N ^ 2) := hN.pow
  refine ⟨?_, ?_⟩
  · rintro ok t F ⟨t', α₀, α, s₁, U, ht, hok, h1, h2, h3, h4, h5, h6⟩ hkill
    obtain ⟨x', rfl⟩ := Φ.e_onto t'
    have hl : (N ^ 2) • x' ∈ Φ.lat := by
      rw [← Φ.e_ker, Φ.exp_nsmul_eq_pow_vt]; exact hkill _ hok ht
    obtain ⟨m, hm⟩ := hN2
    have he : Φ.e (x' + (N ^ 2) • x') = Φ.e x' := by
      rw [Φ.e_add, (Φ.e_ker _).2 hl, _root_.mul_one]
    have hx : ((N ^ 2 : ℕ) : ℂ) • (x' + (N ^ 2) • x') = (2 : ℂ) • ((m + 1) • (N ^ 2) • x') := by
      rw [hm]
      ext i
      simp only [Pi.smul_apply, Pi.add_apply]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    refine ⟨x' + (N ^ 2) • x', (m + 1) • (N ^ 2) • x', Φ.lat.nsmul_mem hl _, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hx
    · rw [he]; exact hok
    · rw [he]; exact ht
    · refine _root_.GlobalTheory.AnVal.rd_fock_of_symLift S A L x0 g Φ hχ _ (N ^ 2) U _ _ s₁ F _ ⟨m, hm⟩ (Φ.lat.nsmul_mem hl _) hx ?_ h6
        (GlobalTheory.T.normalisedPullbackMulN_reads_theta S A L x0 g Φ N α₀ α s s₁ θ h1 h2 h3 h4 hs)
      rw [he]; exact h5
  · rintro x₁ δ₁ x₂ δ₂ F hδ₁ hx₁ hδ₂ hx₂ ⟨α₀, α, s₁, s₂, U₁, U₂, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine _root_.GlobalTheory.AnVal.rd_fock_of_symLift S A L x0 g Φ hχ _ (N ^ 2) U₂ x₂ δ₂ s₂ F _ hN2 hδ₂ (by simpa only [Nat.cast_pow] using hx₂) h7 h8 ?_
    exact _root_.GlobalTheory.AnVal.rd_fock_of_symLift S A L x0 g Φ hχ _ (N ^ 2) U₁ x₁ δ₁ s₁ s₂ _ hN2 hδ₁ (by simpa only [Nat.cast_pow] using hx₁) h5 h6
      (GlobalTheory.T.normalisedPullbackMulN_reads_theta S A L x0 g Φ N α₀ α s s₁ θ h1 h2 h3 h4 hs)

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormPowMulProdTranslConst
section
open NumberField Matrix Complex
open scoped ComplexConjugate Real
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (thetaChar omegaStd hermForm)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory.CanTh (canTh canMult translConst)

namespace GlobalTheory.ThFr

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
  (idx : Fin g ≃ X.Ψ × Fin r)

section Coord

variable (bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)

end Coord

section Series

variable {idx} {bas bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {q0 : ℕ} (hr : X.p0 + q0 = r) {n : ℕ}

theorem polyDeriv_prod_canFn_eq_mul (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {a b a' b' : Fin n → Fin g → ℝ} {c : Fin n → ℂ}
    (h : ∀ k z, canFn X bas' idx (a' k) (b' k) x z = c k * canFn X bas idx (a k) (b k) x z)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (letterDir X hr idx) (fun z => ∏ k, canFn X bas' idx (a' k) (b' k) x (z k)) 0 =
      (∏ k, c k) *
        ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (letterDir X hr idx) (fun z => ∏ k, canFn X bas idx (a k) (b k) x (z k)) 0 := by
  have hF : (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas' idx (a' k) (b' k) x (z k)) =
      fun z => (∏ k, c k) * ∏ k, canFn X bas idx (a k) (b k) x (z k) := by
    funext z
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => h k (z k)
  have hd : Differentiable ℂ
      (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas idx (a k) (b k) x (z k)) := by
    have he : (fun z : Fin n → Fin g → ℂ => ∏ k, canFn X bas idx (a k) (b k) x (z k)) =
        ∏ k, fun z : Fin n → Fin g → ℂ => canFn X bas idx (a k) (b k) x (z k) := by
      funext z; simp [Finset.prod_apply]
    rw [he]
    exact Finset.prod_induction _ (fun f => Differentiable ℂ f) (fun f1 f2 h1 h2 => h1.mul h2)
      (differentiable_const 1)
      fun k _ => (canFn_entire idx hs hx (a k) (b k)).comp (differentiable_apply k)
  rw [hF]
  exact GlobalTheory.CanTh.polyDeriv_const_mul P _ isOpen_univ hd.differentiableOn _ (Set.mem_univ _)

variable (hs : IsSympl X bas) (hs' : IsSympl X bas') (hn : Even n)
include hs hs' hn

theorem IsProportional.thFr_eq {κ : ℂ} {a₀ b₀ a₀' b₀' : Fin g → ℝ}
    (h : IsProportional X idx κ bas a₀ b₀ bas' a₀' b₀') {u u' : Fin n → Fin g ⊕ Fin g → ℝ}
    (hu : ∀ k, IsSamePt X bas bas' (u k) (u' k)) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    thFr X hr bas' idx n (fun k => a₀' + u' k ∘ Sum.inr) (fun k => b₀' + u' k ∘ Sum.inl) P x =
      κ ^ (n / 2) * (∏ k, translConst b₀ (u k ∘ Sum.inr) (u k ∘ Sum.inl) /
        translConst b₀' (u' k ∘ Sum.inr) (u' k ∘ Sum.inl)) *
      thFr X hr bas idx n (fun k => a₀ + u k ∘ Sum.inr) (fun k => b₀ + u k ∘ Sum.inl) P x := by
  obtain ⟨μ, hμ, hμz⟩ := h x hx
  have hc : ∀ k z, canFn X bas' idx (a₀' + u' k ∘ Sum.inr) (b₀' + u' k ∘ Sum.inl) x z =
      (translConst b₀ (u k ∘ Sum.inr) (u k ∘ Sum.inl) /
        translConst b₀' (u' k ∘ Sum.inr) (u' k ∘ Sum.inl) * μ) *
        canFn X bas idx (a₀ + u k ∘ Sum.inr) (b₀ + u k ∘ Sum.inl) x z := fun k z =>
    canFn_translate_eq_mul hs hs' hx hμz (hu k) z
  have halg : ∀ {A B D : ℂ} (t : Fin n → ℂ), μ ^ 2 * A = κ * B →
      A ^ (n / 2) * ((∏ k, (t k * μ)) * D) = κ ^ (n / 2) * (∏ k, t k) * (B ^ (n / 2) * D) := by
    intro A B D t hAB
    obtain ⟨m, rfl⟩ := hn
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (m + m) / 2 = m by omega]
    have key : (μ ^ 2 * A) ^ m = (κ * B) ^ m := by rw [hAB]
    linear_combination (∏ k, t k) * D * key
  simp only [thFr]
  rw [polyDeriv_prod_canFn_eq_mul hr hs hx hc P]
  exact halg _ hμ


omit hs hs' hn in
theorem norm_pow_mul_prod_translConst {κ : ℂ} (hκ : ‖κ‖ = 1) (j : ℕ) (b b' : Fin g → ℝ)
    (s t s' t' : Fin n → Fin g → ℝ) :
    ‖κ ^ j * ∏ k, translConst b (s k) (t k) / translConst b' (s' k) (t' k)‖ = 1 := by
  rw [norm_mul, norm_pow, hκ, one_pow, one_mul, norm_prod]
  exact Finset.prod_eq_one fun k _ => by
    rw [norm_div, GlobalTheory.CanTh.norm_translConst, GlobalTheory.CanTh.norm_translConst, div_one]


variable (idx) in
theorem exists_thFr_eq_mul (a b : Fin n → Fin g → ℝ) :
    ∃ (a' b' : Fin n → Fin g → ℝ) (c : ℂ), ‖c‖ = 1 ∧
      ((∀ k i, a k i ∈ Set.range (Rat.cast : ℚ → ℝ)) → (∀ k i, b k i ∈ Set.range (Rat.cast : ℚ → ℝ)) →
        (∀ k i, a' k i ∈ Set.range (Rat.cast : ℚ → ℝ)) ∧
          ∀ k i, b' k i ∈ Set.range (Rat.cast : ℚ → ℝ)) ∧
      ∀ (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), ∀ x ∈ X.dom,
        thFr X hr bas idx n a b P x = c * thFr X hr bas' idx n a' b' P x := by
  obtain ⟨k, k', hk⟩ := exists_isProportional idx hs' hs
  obtain ⟨κ, hκ, hprop⟩ := hk 0 0 (Matrix.mulVec_zero _).symm
  set w' : Fin n → Fin g ⊕ Fin g → ℝ := fun j =>
    Sum.elim (b j - fun i => (k' i : ℝ) / 2) (a j - fun i => (k i : ℝ) / 2) with hw'
  set w : Fin n → Fin g ⊕ Fin g → ℝ := fun j =>
    (chgMat X bas' bas).map (Int.cast : ℤ → ℝ) *ᵥ w' j with hw
  have hu : ∀ j, IsSamePt X bas' bas (w j) (w' j) := fun j => rfl
  refine ⟨fun j => (0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inr + w j ∘ Sum.inr,
    fun j => (0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inl + w j ∘ Sum.inl,
    κ ^ (n / 2) * ∏ j, translConst ((0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inl) (w j ∘ Sum.inr)
      (w j ∘ Sum.inl) / translConst ((fun i => (k' i : ℝ) / 2) + (0 : Fin g ⊕ Fin g → ℝ) ∘ Sum.inl)
      (w' j ∘ Sum.inr) (w' j ∘ Sum.inl),
    norm_pow_mul_prod_translConst hκ _ _ _ _ _ _ _, ?_, ?_⟩
  · intro ha hb
    have hw'r : ∀ j s, w' j s ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      intro j s
      rcases s with i | i
      · obtain ⟨q, hq⟩ := hb j i
        exact ⟨q - (k' i : ℚ) / 2, by simp [hw', hq]⟩
      · obtain ⟨q, hq⟩ := ha j i
        exact ⟨q - (k i : ℚ) / 2, by simp [hw', hq]⟩
    have hwr : ∀ j s, w j s ∈ Set.range (Rat.cast : ℚ → ℝ) := by
      intro j s
      choose q hq using hw'r j
      refine ⟨((chgMat X bas' bas).map (Int.cast : ℤ → ℚ) *ᵥ q) s, ?_⟩
      simp [hw, Matrix.mulVec, dotProduct, hq]
    exact ⟨fun j i => by simpa using hwr j (Sum.inr i), fun j i => by simpa using hwr j (Sum.inl i)⟩
  · intro P x hx
    have h := IsProportional.thFr_eq hr hs' hs hn hprop hu P hx
    convert h using 2 <;> funext j <;> simp [hw']

end Series

end

end GlobalTheory.ThFr
end

