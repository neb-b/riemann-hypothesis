module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumSphericalFunctionDoublingLength
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

noncomputable section

namespace GlobalTheory.DoublingLength

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem int_mul_of_mem_KO {g x : GL (Fin n) k} (hg : ∀ i j, g.1 i j ∈ 𝒪[k]) (hx : x ∈ KO k (Fin n)) :
    ∀ i j, (g * x).1 i j ∈ 𝒪[k] := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hg i l) (((SplitFlip.mem_KO_iff x).1 hx).1 l j)

theorem ord_det_of_mem_KO {x : GL (Fin n) k} (hx : x ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det x) = 0 := by
  obtain ⟨g, rfl⟩ := hx
  apply ord_eq_zero
  have h1 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)


variable (k n) in
def pairEquiv : ((GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) ≃
    ((GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) where
  toFun p := (p.2, (QuotientGroup.mk (p.2.out⁻¹ * p.1.out) : GL (Fin n) k ⧸ KO k (Fin n)))
  invFun p := ((QuotientGroup.mk (p.1.out * p.2.out) : GL (Fin n) k ⧸ KO k (Fin n)), p.1)
  left_inv p := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (p.2.out⁻¹ * p.1.out)
    refine Prod.ext ?_ rfl
    show (QuotientGroup.mk (p.2.out * (QuotientGroup.mk (p.2.out⁻¹ * p.1.out) : GL (Fin n) k ⧸ KO k (Fin n)).out) : GL (Fin n) k ⧸ KO k (Fin n)) = p.1
    rw [hx, mul_assoc, mul_inv_cancel_left, QuotientGroup.mk_mul_of_mem _ x.2, QuotientGroup.out_eq']
  right_inv p := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (p.1.out * p.2.out)
    refine Prod.ext rfl ?_
    show (QuotientGroup.mk (p.1.out⁻¹ * (QuotientGroup.mk (p.1.out * p.2.out) : GL (Fin n) k ⧸ KO k (Fin n)).out) : GL (Fin n) k ⧸ KO k (Fin n)) = p.2
    rw [hx, mul_assoc, inv_mul_cancel_left, QuotientGroup.mk_mul_of_mem _ x.2, QuotientGroup.out_eq']

theorem pairEquiv_apply (p : (GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) :
    pairEquiv k n p = (p.2, (QuotientGroup.mk (p.2.out⁻¹ * p.1.out) : GL (Fin n) k ⧸ KO k (Fin n))) := rfl


open scoped Classical in
def pairTerm (X : ℂ) (φ : GL (Fin n) k → ℂ)
    (p : (GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) : ℂ :=
  if (∀ i j, (p.1.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧ (∀ i j, (p.2.out : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
    X ^ ((-ord k (Matrix.GeneralLinearGroup.det p.1.out)).toNat +
      (ord k (Matrix.GeneralLinearGroup.det p.2.out)).toNat) * φ (p.1.out * p.2.out)
  else 0

theorem hasSum_of_subtype {β : Type} {P : β → Prop} (f : β → ℂ) {g : β → ℂ} {a b : ℂ} (c : ℂ)
    (h : HasSum (fun x : {x // P x} => f x.1) a) (h1 : ∀ x, P x → g x = f x * c) (h0 : ∀ x, ¬ P x → g x = 0)
    (hb : b = a * c) : HasSum g b := by
  have h2 : HasSum (fun x => Set.indicator {x | P x} f x * c) (a * c) :=
    ((hasSum_subtype_iff_indicator (s := {x | P x}) (f := f)).1 h).mul_right c
  have h3 : g = fun x => Set.indicator {x | P x} f x * c := funext fun x => by
    by_cases hx : P x
    · rw [h1 x hx, Set.indicator_of_mem (by exact hx)]
    · rw [h0 x hx, Set.indicator_of_notMem (by exact hx), zero_mul]
  rw [h3, hb]
  exact h2


open scoped Classical in
theorem hasSum_pairTerm_fiber {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1)
    (h : GL (Fin n) k ⧸ KO k (Fin n)) :
    HasSum (fun c => pairTerm X φ (h, c))
      (if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ (-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat * φ h.out *
          ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹ else 0) := by
  by_cases hA : ∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]
  · rw [if_pos hA]
    refine hasSum_of_subtype (P := fun c : GL (Fin n) k ⧸ KO k (Fin n) => ∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])
      (fun c => X ^ (ord k (Matrix.GeneralLinearGroup.det c.out)).toNat * φ (h.out * c.out))
      (X ^ (-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat)
      (_root_.GlobalTheory.HeckeShift.hasSum_hecke_shift k n γ φ hφ hγ X hX h.out) (fun c hB => ?_) (fun c hB => ?_) (by ring)
    · rw [pairTerm, if_pos ⟨hA, hB⟩]
      ring
    · rw [pairTerm, if_neg fun H => hB H.2]
  · rw [if_neg hA]
    have : (fun c => pairTerm X φ (h, c)) = fun _ => 0 := funext fun c => by
      rw [pairTerm, if_neg fun H => hA H.1]
    rw [this]
    exact hasSum_zero


open scoped Classical in
theorem hasSum_pairTerm_total {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) (a : ℂ) :
    HasSum (fun h : GL (Fin n) k ⧸ KO k (Fin n) =>
      if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ (-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat * φ h.out * a else 0)
      (a * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  exact hasSum_of_subtype
    (P := fun c : GL (Fin n) k ⧸ KO k (Fin n) => ∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])
    (fun c => X ^ (-ord k (Matrix.GeneralLinearGroup.det c.out)).toNat * φ c.out) a
    (GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse k n γ φ hφ hγ X hX) (fun c hB => if_pos hB) (fun c hB => if_neg hB) (mul_comm _ _)

theorem norm_pairTerm (X : ℂ) (φ : GL (Fin n) k → ℂ)
    (p : (GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) :
    ((‖pairTerm X φ p‖ : ℝ) : ℂ) = pairTerm (‖X‖ : ℂ) (fun g => (‖φ g‖ : ℂ)) p := by
  unfold pairTerm
  split_ifs
  · rw [norm_mul, norm_pow, Complex.ofReal_mul, Complex.ofReal_pow]
  · simp

theorem isBorelSph_norm {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (h : IsBorelSph k γ φ) :
    IsBorelSph k (fun i => (‖γ i‖ : ℂ)) (fun g => (‖φ g‖ : ℂ)) := by
  refine ⟨fun g x hx => by simp only [h.1 g x hx], fun b hb t ht => ?_⟩
  simp only [h.2 b hb t ht, norm_prod, norm_zpow, Complex.ofReal_prod, Complex.ofReal_zpow]

theorem summable_pairTerm {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {X : ℂ} (hX1 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1)
    (hX2 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) : Summable (pairTerm X φ) := by
  have hψ := isBorelSph_norm hφ
  have hγ' : ∀ i, (‖γ i‖ : ℂ) ≠ 0 := fun i => by simpa using hγ i
  have hX1' : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * (‖γ i‖ : ℂ) * (‖X‖ : ℂ)‖ < 1 := fun i => by
    simpa using hX1 i
  have hX2' : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * ((‖γ i‖ : ℂ))⁻¹ * (‖X‖ : ℂ)‖ < 1 := fun i => by
    simpa using hX2 i
  refine Summable.of_norm ((summable_prod_of_nonneg fun _ => norm_nonneg _).2 ⟨fun h => ?_, ?_⟩)
  · have := (hasSum_pairTerm_fiber hψ hγ' hX1' h).summable
    simp_rw [← norm_pairTerm] at this
    exact Complex.summable_ofReal.1 this
  · refine Complex.summable_ofReal.1 ((hasSum_pairTerm_total hψ hγ' hX2'
      (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * (‖γ i‖ : ℂ) * (‖X‖ : ℂ))⁻¹)).summable.congr
        fun h => ?_)
    rw [Complex.ofReal_tsum]
    simp_rw [norm_pairTerm]
    exact (hasSum_pairTerm_fiber hψ hγ' hX1' h).tsum_eq.symm


open scoped Classical in
theorem pairTerm_pairEquiv {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (X : ℂ)
    (g h : GL (Fin n) k ⧸ KO k (Fin n)) :
    pairTerm X φ (pairEquiv k n (g, h)) =
      if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
          (∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat +
          (ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out))).toNat) * φ g.out
      else 0 := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (h.out⁻¹ * g.out)
  have hiff : (∀ i j, (h.out⁻¹ * g.out * x : GL (Fin n) k).1 i j ∈ 𝒪[k]) ↔
      ∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k] :=
    ⟨fun H => by
      have := int_mul_of_mem_KO H (inv_mem x.2)
      rwa [mul_inv_cancel_right] at this, fun H => int_mul_of_mem_KO H x.2⟩
  have hord : ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out * x : GL (Fin n) k)) =
      ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out)) := by
    rw [map_mul, ord_mul, ord_det_of_mem_KO x.2, add_zero]
  have hval : φ (h.out * (h.out⁻¹ * g.out * x)) = φ g.out := by
    rw [mul_assoc, mul_inv_cancel_left, hφ.1 _ _ x.2]
  rw [pairEquiv_apply, pairTerm]
  dsimp only
  rw [hx, hord, hval]
  exact if_congr (and_congr Iff.rfl hiff) rfl rfl

theorem hasSum_pairTerm_pairEquiv {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ)
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {len : GL (Fin n) k → ℕ}
    (hlen : ∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat)
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) (g : GL (Fin n) k ⧸ KO k (Fin n)) :
    HasSum (fun h => pairTerm X φ (pairEquiv k n (g, h)))
      (X ^ len g.out * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) * φ g.out) := by
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 (show g.out ∈ ⋃ e : {e : Fin n → ℤ // Antitone e}, cell k (Fin n) ϖ e by
    rw [iUnion_cell hϖ]; trivial)
  rw [hlen e.1 e.2 g.out he]
  refine hasSum_of_subtype
    (P := fun h : GL (Fin n) k ⧸ KO k (Fin n) => (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
      (∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k]))
    (fun h => X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat +
      (ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out))).toNat)) (φ g.out)
    (GlobalTheory.T.hecke_series_cell_has_sum k n ϖ hϖ e.1 g.out he X hX) (fun h hB => ?_) (fun h hB => ?_) rfl
  · rw [pairTerm_pairEquiv hφ, if_pos hB]
  · rw [pairTerm_pairEquiv hφ, if_neg hB]

theorem exists_small (q : ℝ) (hq0 : 0 ≤ q) (γ : Fin n → ℂ) : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x < δ → ∀ i : Fin n,
    q ^ (n - 1 - (i : ℕ)) * ‖γ i‖ * x < 1 ∧ q ^ (i : ℕ) * ‖γ i‖⁻¹ * x < 1 ∧ q ^ (i : ℕ) * x ^ 2 < 1 := by
  obtain ⟨S, hS, hS0⟩ : ∃ S : ℝ, (∀ i, ‖γ i‖ + ‖γ i‖⁻¹ ≤ S) ∧ 0 ≤ S :=
    ⟨∑ i, (‖γ i‖ + ‖γ i‖⁻¹), fun i => Finset.single_le_sum (f := fun i => ‖γ i‖ + ‖γ i‖⁻¹)
      (fun j _ => by positivity) (Finset.mem_univ i), Finset.sum_nonneg fun j _ => by positivity⟩
  have hq1 : 1 ≤ q + 1 := by linarith
  have hM1 : 1 ≤ (q + 1) ^ n * (1 + S) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq1) (by linarith)
  have hM0 : 0 < (q + 1) ^ n * (1 + S) := by linarith
  have hpow : ∀ m ≤ n, q ^ m ≤ (q + 1) ^ n := fun m hm =>
    (pow_le_pow_left₀ hq0 (by linarith) m).trans (pow_le_pow_right₀ hq1 hm)
  have key : ∀ m ≤ n, ∀ c : ℝ, 0 ≤ c → c ≤ 1 + S → ∀ x : ℝ, 0 ≤ x → x < ((q + 1) ^ n * (1 + S))⁻¹ →
      q ^ m * c * x < 1 := by
    intro m hm c hc0 hc x hx0 hx
    have h1 : q ^ m * c ≤ (q + 1) ^ n * (1 + S) := mul_le_mul (hpow m hm) hc hc0 (by positivity)
    calc q ^ m * c * x ≤ (q + 1) ^ n * (1 + S) * x := mul_le_mul_of_nonneg_right h1 hx0
      _ < (q + 1) ^ n * (1 + S) * ((q + 1) ^ n * (1 + S))⁻¹ := mul_lt_mul_of_pos_left hx hM0
      _ = 1 := mul_inv_cancel₀ hM0.ne'
  refine ⟨_, inv_pos.2 hM0, fun x hx0 hx i => ⟨?_, ?_, ?_⟩⟩
  · exact key _ (by omega) _ (norm_nonneg _) (by linarith [hS i, inv_nonneg.2 (norm_nonneg (γ i))]) x hx0 hx
  · exact key _ i.2.le _ (by positivity) (by linarith [hS i, norm_nonneg (γ i)]) x hx0 hx
  · have hx1 : x ≤ 1 := hx.le.trans (inv_le_one_of_one_le₀ hM1)
    rw [sq, ← mul_assoc]
    exact key _ i.2.le _ hx0 (by linarith) x hx0 hx

theorem hasSum_doublingLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k → ∀ len : GL (Fin n) k → ℕ, (∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℂ, ‖X‖ < δ → HasSum (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)) := by
  intro k _ _ _ _ n γ φ hφ hγ ϖ hϖ len hlen
  obtain ⟨δ, hδ, hsm⟩ := exists_small (resCard k : ℝ) (Nat.cast_nonneg _) γ
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have hX1 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1 := fun i => by
    simpa using (hsm _ (norm_nonneg X) hX i).1
  have hX2 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1 := fun i => by
    simpa using (hsm _ (norm_nonneg X) hX i).2.1
  have hX3 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1 := fun i => by
    simpa using (hsm _ (norm_nonneg X) hX i).2.2
  have hsum := (summable_pairTerm hφ hγ hX1 hX2).hasSum
  rw [(hsum.prod_fiberwise (hasSum_pairTerm_fiber hφ hγ hX1)).unique (hasSum_pairTerm_total hφ hγ hX2 _)] at hsum
  have hmain := ((pairEquiv k n).hasSum_iff.2 hsum).prod_fiberwise (hasSum_pairTerm_pairEquiv hφ hϖ hlen hX3)
  have hR : ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ H => by
      have := hX3 i
      rw [← sub_eq_zero.1 H, norm_one] at this
      exact lt_irrefl _ this
  have hfun : (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) = fun c =>
      X ^ len c.out * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) * φ c.out *
        ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2) := funext fun c => by
    rw [Finset.prod_inv_distrib, mul_right_comm _ _ (φ c.out), inv_mul_cancel_right₀ hR]
  rw [hfun]
  exact hmain.mul_right _

end GlobalTheory.DoublingLength
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PositionOneOfSymmetricDoubleIntegralFinite
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem GlobalTheory.PosOne.exUp_bilPos : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (μ : kˣ →* ℂˣ) (b : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ p σ b → ∃ B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ Ψ v, B Ψ v = exUp ν p σ (b Ψ) v) ∧ BilPos ψ μ (p + 1) σ B := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ μ b hb
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have E := GlobalTheory.RootEx.Exchange.exchange_isPos k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  refine ⟨GlobalTheory.RootEx.Exchange.avg₂ ν (fun u => σ (rowE c p u)) b fun Ψ v => ((H (b Ψ) v).1 (hb.1 Ψ)).1,
    fun Ψ v => rfl, fun Ψ => ?_, fun g Ψ Ψ₁ v hΨ => ?_⟩
  · obtain ⟨l', hl', hN⟩ := E.1 (b Ψ) (hb.1 Ψ)
    have : (⇑((GlobalTheory.RootEx.Exchange.avg₂ ν (fun u => σ (rowE c p u)) b
        fun Ψ v => ((H (b Ψ) v).1 (hb.1 Ψ)).1) Ψ) : A → ℂ) = ⇑l' := by
      funext v; rw [hl']; rfl
    rw [this]; exact hN
  · change ∫ u, b Ψ₁ (σ (rowE c p u) (σ (embX c g) v)) ∂(Measure.pi fun _ => ν) =
      _ * ∫ u, b Ψ (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)
    let m : GL n k := ⟨g.valᵀ, (g⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    have hm : Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det g := by
      ext; simp [m]
    have step : ∀ u, b Ψ₁ (σ (rowE c p u) (σ (embX c g) v)) =
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
          b Ψ (σ (rowE c p (m.val.mulVec u)) v) := fun u => by
      rw [← Module.End.mul_apply, ← map_mul, GlobalTheory.RootEx.Exchange.rowE_mul_embX, map_mul, Module.End.mul_apply,
        hb.2 g Ψ Ψ₁ _ hΨ]
    simp only [step]
    rw [integral_const_mul, (GlobalTheory.SplitWeil.linear_change_of_variables k n n ν).1 m
      (fun u => b Ψ (σ (rowE c p u) v)), hm, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_neg_one, ← Real.rpow_add (GlobalTheory.SplitWeil.nabs_pos k _)]
    congr 3
    push_cast; ring

theorem GlobalTheory.PosOne.exUp_represents : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (P : Type) [AddCommGroup P] [Module ℂ P] (b B : P →ₗ[ℂ] A →ₗ[ℂ] ℂ), (∀ φ, IsNEquiv ψ p σ (b φ)) → (∀ φ v, B φ v = exUp ν p σ (b φ) v) → ∃ fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ, Represents ψ ν p σ fj B ∧ ∀ φ v (Φ₀ : SB (n → k)), fj φ v Φ₀ = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ : (n → k) → ℂ) u * b φ (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ P _ _ b B hbN hB
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have E := GlobalTheory.RootEx.Exchange.exchange_isPos k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have hBN : ∀ φ, IsNEquiv ψ (p + 1) σ (B φ) := fun φ => by
    obtain ⟨l', hl', hN⟩ := E.1 (b φ) (hbN φ)
    have : (⇑(B φ) : A → ℂ) = ⇑l' := by funext v; rw [hl', hB]
    rw [this]; exact hN
  have integ : ∀ φ v (Φ₀ : SB (n → k)), Integrable (fun β => (Φ₀ : (n → k) → ℂ) β *
      B φ (σ (colE c (p + 1) β) v)) (Measure.pi fun _ => ν) := fun φ v Φ₀ => by
    have hS := ((H (B φ) v).2 (hBN φ)).1
    exact GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν ⟨Φ₀.2.1.mul hS.1, Φ₀.2.2.mul_right⟩
  let fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => LinearMap.mk₂ ℂ
        (fun v Φ₀ => ∫ β, (Φ₀ : (n → k) → ℂ) β * B φ (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν))
        (fun v₁ v₂ Φ₀ => by
          simp only [map_add (f := _), mul_add]
          exact integral_add (integ φ v₁ Φ₀) (integ φ v₂ Φ₀))
        (fun a v Φ₀ => by
          simp only [map_smul, smul_eq_mul, mul_left_comm _ a]
          exact integral_const_mul a _)
        (fun v Φ₀ Φ₀' => by
          simp only [Submodule.coe_add, Pi.add_apply, add_mul]
          exact integral_add (integ φ v Φ₀) (integ φ v Φ₀'))
        (fun a v Φ₀ => by
          simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
          exact integral_const_mul a _)
      map_add' := fun φ φ' => by
        ext v Φ₀
        simp only [LinearMap.mk₂_apply, LinearMap.add_apply, map_add (f := _), mul_add]
        exact integral_add (integ φ v Φ₀) (integ φ' v Φ₀)
      map_smul' := fun a φ => by
        ext v Φ₀
        simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply,
          mul_left_comm _ a]
        exact integral_const_mul a _ }
  refine ⟨fj, ⟨hBN, fun φ v Φ₀ => ⟨integ φ v Φ₀, rfl⟩⟩, fun φ v Φ₀ => ?_⟩
  have hg := (H (b φ) v).1 (hbN φ)
  change ∫ β, (Φ₀ : (n → k) → ℂ) β * B φ (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν) = _
  simp only [hB, hg.2.2]
  simp only [← integral_const_mul]
  rw [integral_integral_swap]
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, ← integral_mul_const]
    congr 1; funext u; congr 1; funext β; ring
  · have h1 := GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν Φ₀.2
    have h2 := GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν hg.1
    refine (h1.mul_prod h2).norm.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · apply Continuous.aestronglyMeasurable
      exact (Φ₀.2.1.continuous.comp continuous_fst).mul
        (((continuous_induced_dom.comp hψ).comp
          ((continuous_snd.dotProduct continuous_fst))).mul (hg.1.1.continuous.comp continuous_snd))
    · obtain ⟨β, u⟩ := z
      simp only [Function.uncurry_apply_pair, norm_mul, Circle.norm_coe, one_mul, norm_norm, le_refl]

noncomputable section
namespace GlobalTheory.PosOne

theorem om_one_comp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g : GL a k)
    (h : GL b k) (Φ : Matrix b a k → ℂ) : om μ 1 h (om μ g 1 Φ) = om μ g h Φ := by
  funext x
  simp only [om, map_one, inv_one, Units.val_one, mul_one, one_mul, Matrix.mul_one, Matrix.one_mul]
  have : nabs k (1 : kˣ) = 1 := by simp [nabs]
  simp only [this, Real.one_rpow, Complex.ofReal_one, mul_one, one_mul, Matrix.mul_assoc]
  ring


open Classical in
theorem app_eq_dite {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V] (l : SB X →ₗ[ℂ] V)
    (f : X → ℂ) : app l f = l (if h : f ∈ SB X then ⟨f, h⟩ else 0) := by
  unfold app; split_ifs <;> simp

theorem oneDbl_of_symDbl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₀ : Representation ℂ (GL (n₀ ⊕ Fin (c + 1 + 1)) k) (SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k))) (_ : IsSrc μ₁ ρ₀) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (e : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ) (_ : SrcComb ψ ν (ρ + 1) ρ₀ Φ₁ e) (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ), (∀ g ∈ e.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F (om μ₁ g 1 Φ₁.1) Φ₂.1 (z g)) → OneDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁.1 Φ₂.1 (comb e z) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ _ G₁ _ m₂ _ G₂ _ A _ _ σ hσ T hT
    F ρ₀ hρ₀ Φ₁ Φ₂ e he z hz
  haveI : ν.IsAddHaarMeasure := hν.1
  have hρ1 : 1 ≤ ρ := by omega
  obtain ⟨⟨ρ₁, hρ₁⟩, hsm⟩ := _root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂
  have hρ₁s : IsSmoothRep ρ₁ := hsm ρ₁ hρ₁
  obtain ⟨b, hb, hb2, hb3⟩ := _root_.GlobalTheory.PosOne.MidVertex.exists_bilPos_mid k n₀ n₁ n₂ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ G₁ m₂ G₂ A σ hσ T hT
    F ρ₁ hρ₁
  obtain ⟨B, hB, hBpos⟩ := GlobalTheory.PosOne.exUp_bilPos k n₁ n₀ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s μ₁ b hb
  obtain ⟨fj, hrep, hfj⟩ := GlobalTheory.PosOne.exUp_represents k n₁ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s _ b B hb.1 hB
  obtain ⟨-, hpos⟩ := _root_.GlobalTheory.PosOne.toOne_isPosOne k n₁ n₀ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s
  obtain ⟨B₁, hB₁, -⟩ := hpos μ₁ hμ₁ b hb
  have hstep : ∀ g ∈ e.support, IsQuotInt ν m₁ G₁ (ρ + 1)
      (tInt ψ ν μ₁ (ρ + 1) ρ₁ B Φ₂ (om μ₁ g 1 Φ₁.1)) (z g) := by
    intro g hg
    obtain ⟨w', hw', hFJ⟩ := hz g hg
    have hΦ' : ((ρ₀ g Φ₁ : SB _) : Matrix _ _ k → ℂ) = om μ₁ g 1 Φ₁.1 := hρ₀ g Φ₁
    have key : w' = fun h Ψ Φ₀ => fj Ψ (ρ₁ h Φ₂) Φ₀ := by
      funext h Ψ Φ₀
      have hV : ((ρ₁ h Φ₂ : SB _) : Matrix _ _ k → ℂ) = om μ₂ h 1 Φ₂.1 := hρ₁ h Φ₂
      obtain ⟨-, hav⟩ := _root_.GlobalTheory.PosOne.avg_self_and_props k n₂ n₁ c ρ hρ1 (by omega) ψ hψ hψ1 ν hν μ₂ hμ₂ (ρ₁ h Φ₂)
      obtain ⟨hmem, hE, hL⟩ := hav Φ₀
      have h1 := hb2 Ψ ⟨_, hmem⟩
      have h2 := hw' h Ψ Φ₀
      have hf : tInt ψ ν μ₂ ρ σ (T Ψ) F (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ₂ ρ Φ₀.1 (ρ₁ h Φ₂).1) =
          fun h' => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ h h' Φ₂.1)) (σ h' F) := by
        funext h'
        simp only [tInt]
        rw [hE h', hV, om_one_comp]
      rw [hf] at h1
      have heq := (GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c ρ hρ1 (by omega) ν m₂ G₂ _).1 _ _ h2 h1
      rw [heq, hfj, ← GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (b Ψ) ⟨_, hmem⟩]
      exact hL ρ₁ hρ₁ (b Ψ)
    rw [key, ← hΦ'] at hFJ
    have := (_root_.GlobalTheory.PosOne.FJTarget.target_bilinear k n₁ n₀ (c + 1) ρ hρ1 hcρ ψ hψ hψ1 ν hν μ₁ hμ₁ m₁ G₁ _ ρ₁ hρ₁s fj B hrep hBpos Φ₂
      (ρ₀ g Φ₁) (z g)).2 hFJ
    rwa [hΦ'] at this
  have hone := _root_.GlobalTheory.PosOne.quotInt_one_comb k n₁ n₀ (c + 1) (ρ + 1) (by omega) (by omega) ψ hψ hψ1 ν hν μ₁ hμ₁ m₁ G₁ ρ₀ hρ₀ Φ₁ e he
    _ ρ₁ hρ₁s B hBpos Φ₂ z hstep
  refine ⟨fun h => B₁.flip (ρ₁ h Φ₂), fun h Ψ => ?_, ?_⟩
  · have := hb3 Ψ (ρ₁ h Φ₂)
    rw [hρ₁ h Φ₂] at this
    simpa [hB₁] using this
  · convert hone using 1
    funext h
    obtain ⟨q, rfl⟩ : ∃ q, ρ = q + 1 := ⟨ρ - 1, by omega⟩
    simp only [tIntOne, app_eq_dite]
    rw [toOne_succ]
    classical
    set Ψf := (if hf : opE ψ ν 1 (om μ₁ 1 h Φ₁.1) ∈ SB (Matrix n₁ n₀ k) then ⟨_, hf⟩ else 0 : SB (Matrix n₁ n₀ k))
    have hd : exDown ν (q + 1) ρ₁ (fun v => B Ψf v) = fun v => b Ψf v := by
      funext v
      simp only [exDown, hB]
      exact (GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n₁ (c + 1) (q + 1) hρ1 (by omega) ψ hψ hψ1 ν hν _ ρ₁ hρ₁s
        (b Ψf) v).1 (hb.1 Ψf)
    rw [hd, LinearMap.flip_apply, hB₁]

end GlobalTheory.PosOne
end
end

