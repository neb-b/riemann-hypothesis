module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfMemInvMem
section
open Polynomial

namespace GlobalTheory.K4

theorem kum_congr_base {K₁ K₂ Ω : Type*} [Field K₁] [Field K₂] [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω] {N : ℕ}
    (ζ θ : Ω) (g : Ω ≃ₐ[K₁] Ω) (g' : Ω ≃ₐ[K₂] Ω) (h : ∀ x, g x = g' x) :
    GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum (N := N) ζ θ g' := by
  have e : g θ = g' θ := h θ
  unfold GlobalTheory.NeedB.kum
  rw [e]

theorem valuation_eq_one_of_mem_inv_mem {Ω : Type*} [Field Ω] (B : ValuationSubring Ω) {x : Ω} (hx : x ∈ B)
    (hx' : x⁻¹ ∈ B) (h0 : x ≠ 0) : B.valuation x = 1 := by
  have h1 : B.valuation x ≤ 1 := (B.valuation_le_one_iff x).2 hx
  have h2 : B.valuation x⁻¹ ≤ 1 := (B.valuation_le_one_iff _).2 hx'
  have h3 : B.valuation x * B.valuation x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = B.valuation x * B.valuation x⁻¹ := h3.symm
    _ ≤ B.valuation x * 1 := by gcongr
    _ = B.valuation x := mul_one _

theorem mem_of_isIntegral_of_le {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω] (B : ValuationSubring Ω)
    (hB : ∀ p : R, algebraMap R Ω p ∈ B) {x : Ω} (hx : IsIntegral R x) : x ∈ B := by
  obtain ⟨p, hpm, hp⟩ := hx
  let φ : R →+* B := (algebraMap R Ω).codRestrict B hB
  have hcomp : (algebraMap B Ω).comp φ = algebraMap R Ω := by
    ext r
    rfl
  have hB' : IsIntegral B x := ⟨p.map φ, hpm.map φ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := Ω)).1 hB'
  rw [← hy]
  exact y.2

theorem thmA_on_open_geo : GlobalTheory.NeedB.ThmA → ∀ (k F Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field Ω] [Algebra F (RatFunc k)] [Algebra (RatFunc k) Ω] [Algebra F Ω] [IsScalarTower F (RatFunc k) Ω] [Algebra k[X] Ω] [IsScalarTower k[X] (RatFunc k) Ω] [IsAlgClosure (RatFunc k) Ω] [Algebra.IsAlgebraic F Ω] (N : ℕ) [NeZero N] (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (U : Subgroup (Ω ≃ₐ[F] Ω)), IsOpen (U : Set (Ω ≃ₐ[F] Ω)) → ∀ α β : Ω, α ≠ 0 → β ≠ 0 → IsIntegral k[X] α → IsIntegral k[X] α⁻¹ → IsIntegral k[X] β → IsIntegral k[X] β⁻¹ →
 (∀ g ∈ U, g (α ^ N) = α ^ N ∧ g (β ^ N) = β ^ N) →
 ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N, IsLocallyConstant (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) ∧
  (∀ g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ h ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, GlobalTheory.NeedB.kum (N := N) ζ α g * GlobalTheory.NeedB.kum ζ β h = η₀ h - η₀ (g * h) + η₀ g) ∧
  ∀ r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ B : ValuationSubring Ω, (∀ p : k[X], algebraMap k[X] Ω p ∈ B) → GlobalTheory.NeedB.Inert B r → η₀ r = 0 ∧ r α = α ∧ r β = β := by
  intro hA k F Ω _ _ _ _ _ _ _ _ _ _ _ _ _ N _ ζ hζ U hU α β hα0 hβ0 hαi hαi' hβi hβi' hUfix
  classical
  obtain ⟨-, ⟨e, he, hec, -⟩, -, -, -⟩ := _root_.GlobalTheory.K4.geo_facts F (RatFunc k) Ω
  let U' : Subgroup (Ω ≃ₐ[RatFunc k] Ω) :=
    U.comap ((GlobalTheory.K4.geo F (RatFunc k) Ω).subtype.comp e.toMonoidHom)
  have hU'mem : ∀ g, g ∈ U' ↔ ((e g : GlobalTheory.K4.geo F (RatFunc k) Ω) : Ω ≃ₐ[F] Ω) ∈ U := fun g => Iff.rfl
  have hU'open : IsOpen (U' : Set (Ω ≃ₐ[RatFunc k] Ω)) :=
    (continuous_subtype_val.comp hec).isOpen_preimage _ hU
  let K' : IntermediateField (RatFunc k) Ω := IntermediateField.fixedField U'
  have hfixle : U' ≤ K'.fixingSubgroup := (IntermediateField.le_iff_le U' K').1 le_rfl
  haveI : FiniteDimensional (RatFunc k) K' :=
    (InfiniteGalois.isOpen_iff_finite K').1 (Subgroup.isOpen_mono hfixle hU'open)
  haveI : IsScalarTower F K' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k[X] K' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAlgClosure K' Ω :=
    ⟨IsAlgClosure.isAlgClosed (RatFunc k), Algebra.IsAlgebraic.tower_top (K := RatFunc k) K'⟩
  obtain ⟨-, ⟨e', he', -, hesc'⟩, -, -, -⟩ := _root_.GlobalTheory.K4.geo_facts F K' Ω
  have hφ : ∀ g (hg : g ∈ GlobalTheory.K4.geo F K' Ω) x, (e'.symm ⟨g, hg⟩) x = g x := by
    intro g hg x
    have := he' (e'.symm ⟨g, hg⟩) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hsub : ∀ g, g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U → g ∈ GlobalTheory.K4.geo F K' Ω := by
    intro g hg
    rw [Subgroup.mem_inf] at hg
    rw [GlobalTheory.K4.TopW.mem_geo]
    intro x
    have h1 : e.symm ⟨g, hg.1⟩ ∈ U' := by
      rw [hU'mem, MulEquiv.apply_symm_apply]
      exact hg.2
    have h2 := (IntermediateField.mem_fixedField_iff U' (x : Ω)).1 x.2 _ h1
    have h3 : (e.symm ⟨g, hg.1⟩) (x : Ω) = g x := by
      have := he (e.symm ⟨g, hg.1⟩) (x : Ω)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [IntermediateField.algebraMap_apply, ← h3]
    exact h2
  have hfixK' : ∀ z : Ω, (∀ g ∈ U, g z = z) → z ∈ K' := by
    intro z hz
    refine (IntermediateField.mem_fixedField_iff U' z).2 fun f hf => ?_
    have := hz _ ((hU'mem f).1 hf)
    rw [he] at this
    exact this
  have hαK : α ^ N ∈ K' := hfixK' _ fun g hg => (hUfix g hg).1
  have hβK : β ^ N ∈ K' := hfixK' _ fun g hg => (hUfix g hg).2
  have hint : ∀ {θ : Ω} (hθ : θ ^ N ∈ K'), IsIntegral k[X] θ → IsIntegral k[X] θ⁻¹ →
      (⟨θ ^ N, hθ⟩ : K') ∈ FunctionField.ringOfIntegers k K' ∧
        (⟨θ ^ N, hθ⟩ : K')⁻¹ ∈ FunctionField.ringOfIntegers k K' := by
    intro θ hθ h1 h2
    constructor
    · refine (mem_integralClosure_iff _ _).2 ?_
      refine (isIntegral_algebraMap_iff (B := Ω)).1 ?_
      exact h1.pow N
    · refine (mem_integralClosure_iff _ _).2 ?_
      refine (isIntegral_algebraMap_iff (B := Ω)).1 ?_
      rw [map_inv₀, IntermediateField.algebraMap_apply, ← inv_pow]
      exact h2.pow N
  have hne : ∀ {θ : Ω} (hθ : θ ^ N ∈ K'), θ ≠ 0 → (⟨θ ^ N, hθ⟩ : K') ≠ 0 := by
    intro θ hθ h0 h
    exact pow_ne_zero N h0 (congrArg Subtype.val h)
  obtain ⟨-, -, -, -, η, hηlc, hηco, hηin⟩ :=
    hA k K' Ω N ζ (Nat.pos_of_ne_zero (NeZero.ne N)) hζ ⟨α ^ N, hαK⟩ ⟨β ^ N, hβK⟩ α β (hne hαK hα0) (hne hβK hβ0)
      (hint hαK hαi hαi').1 (hint hαK hαi hαi').2 (hint hβK hβi hβi').1 (hint hβK hβi hβi').2 rfl rfl
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N,
      ∀ g (hg : g ∈ GlobalTheory.K4.geo F K' Ω), η₀ g = η (e'.symm ⟨g, hg⟩) :=
    ⟨fun g => if hg : g ∈ GlobalTheory.K4.geo F K' Ω then η (e'.symm ⟨g, hg⟩) else 0, fun g hg => dif_pos hg⟩
  refine ⟨η₀, ?_, ?_, ?_⟩
  · have hfun : (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) =
        η ∘ e'.symm ∘ (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => (⟨g.1, hsub _ g.2⟩ : GlobalTheory.K4.geo F K' Ω)) := by
      funext g
      exact hη₀ _ _
    rw [hfun]
    exact hηlc.comp_continuous (hesc'.comp (continuous_subtype_val.subtype_mk _))
  · intro g hg h hh
    have hgh := mul_mem hg hh
    rw [hη₀ _ (hsub _ hg), hη₀ _ (hsub _ hh), hη₀ _ (hsub _ hgh),
      kum_congr_base ζ α g (e'.symm ⟨g, hsub _ hg⟩) (fun x => (hφ _ _ x).symm),
      kum_congr_base ζ β h (e'.symm ⟨h, hsub _ hh⟩) (fun x => (hφ _ _ x).symm)]
    have hm : e'.symm ⟨g * h, hsub _ hgh⟩ = e'.symm ⟨g, hsub _ hg⟩ * e'.symm ⟨h, hsub _ hh⟩ := by
      rw [← map_mul]
      rfl
    rw [hm]
    exact hηco _ _
  · intro r hr B hB hinert
    have hmemB : ∀ {x : Ω}, IsIntegral k[X] x → x ∈ B := fun hx => mem_of_isIntegral_of_le B hB hx
    have hNk : (N : k) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    have hk : (N : k[X]) * C ((N : k)⁻¹) = 1 := by
      rw [← map_natCast C N, ← C_mul, mul_inv_cancel₀ hNk, C_1]
    have h1 : (N : Ω) * algebraMap k[X] Ω (C ((N : k)⁻¹)) = 1 := by
      rw [← map_natCast (algebraMap k[X] Ω) N, ← map_mul, hk, map_one]
    have hNΩ : (N : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hvN : B.valuation (N : Ω) = 1 := by
      refine valuation_eq_one_of_mem_inv_mem B ?_ ?_ hNΩ
      · rw [← map_natCast (algebraMap k[X] Ω) N]
        exact hB _
      · rw [← eq_inv_of_mul_eq_one_right h1]
        exact hB _
    have hroot : ∀ θ : Ω, θ ≠ 0 → IsIntegral k[X] θ → IsIntegral k[X] θ⁻¹ → r (θ ^ N) = θ ^ N → r θ = θ := by
      intro θ h0 hi hi' hfix
      refine _root_.GlobalTheory.inert_fixes_root_of_unit_ratio F Ω B r N 1 θ (Nat.pos_of_ne_zero (NeZero.ne N)) hvN hinert (map_one r) one_ne_zero hfix ?_
      rw [one_pow, div_one]
      refine valuation_eq_one_of_mem_inv_mem B (hmemB (hi.pow N)) ?_ (pow_ne_zero N h0)
      rw [← inv_pow]
      exact hmemB (hi'.pow N)
    rw [Subgroup.mem_inf] at hr
    refine ⟨?_, hroot α hα0 hαi hαi' (hUfix r hr.2).1, hroot β hβ0 hβi hβi' (hUfix r hr.2).2⟩
    have hr' : r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U := Subgroup.mem_inf.2 hr
    rw [hη₀ _ (hsub _ hr')]
    refine hηin B ?_ _ ?_
    · intro x hx
      refine hmemB ?_
      exact ((mem_integralClosure_iff _ _).1 hx).algebraMap
    · intro x hx
      rw [hφ]
      exact hinert x hx

end GlobalTheory.K4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.XMulMemSpanOfColemanLevels
section
noncomputable section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col.Interp

variable {R : Type} [CommRing R]

theorem coeff_one_add_X_pow (n k : ℕ) : coeff k ((1 + X : PowerSeries R) ^ n) = (n.choose k : R) := by
  have : ((1 + X : PowerSeries R) ^ n) = (((1 + Polynomial.X : Polynomial R) ^ n : Polynomial R) : PowerSeries R) := by
    simp
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem one_add_X_pow_sub_one_ne_zero [Nontrivial R] (N : ℕ) (hN : 1 ≤ N) :
    ((1 + X : PowerSeries R) ^ N - 1) ≠ 0 := by
  intro h
  have := congrArg (coeff N) h
  rw [map_sub, coeff_one_add_X_pow, Nat.choose_self, coeff_one, if_neg (by omega)] at this
  simp at this

theorem cyc_succ (p n : ℕ) (hp : p.Prime) :
    cyc R p (n + 1) = ∑ i ∈ Finset.range p, ((1 + X : PowerSeries R) ^ (p ^ n)) ^ i := by
  unfold cyc
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
  simp [Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow, Polynomial.eval₂_X]

theorem om_succ (p n : ℕ) (hp : p.Prime) :
    (1 + X : PowerSeries R) ^ (p ^ (n + 1)) - 1 = cyc R p (n + 1) * ((1 + X : PowerSeries R) ^ (p ^ n) - 1) := by
  rw [cyc_succ p n hp, geom_sum_mul, ← pow_mul, ← pow_succ]

theorem cyc_sub_p (p n : ℕ) (hp : p.Prime) :
    ∃ u : PowerSeries R, cyc R p (n + 1) - (p : PowerSeries R) = u * ((1 + X : PowerSeries R) ^ (p ^ n) - 1) := by
  refine ⟨∑ i ∈ Finset.range p, ∑ l ∈ Finset.range i, ((1 + X : PowerSeries R) ^ (p ^ n)) ^ l, ?_⟩
  rw [cyc_succ p n hp, Finset.sum_mul]
  have : (p : PowerSeries R) = ∑ i ∈ Finset.range p, (1 : PowerSeries R) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [geom_sum_mul]

theorem cancel_prime [IsDomain R] {q : R} (hq : Prime q) {f : PowerSeries R}
    (hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) f ≠ 0)
    {B s t : PowerSeries R} (m : ℕ)
    (h : C q * B = C q ^ (m + 1) * s + f * t) : ∃ t', B = C q ^ m * s + f * t' := by
  haveI : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).2 hq
  have hCq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) (C q) = 0 := by
    rw [PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self q), map_zero]
  have ht : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) t = 0 := by
    have h2 : f * t = C q * (B - C q ^ m * s) := by rw [mul_sub, ← mul_assoc, ← pow_succ', h]; ring
    have h3 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q}))) h2
    rw [map_mul, map_mul, hCq, zero_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left hf
  have hd : ∀ n, ∃ a, coeff n t = q * a := by
    intro n
    have := congrArg (coeff n) ht
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this
  choose a ha using hd
  have ht' : t = C q * PowerSeries.mk a := by
    ext n; rw [coeff_C_mul, coeff_mk, ha]
  refine ⟨PowerSeries.mk a, ?_⟩
  have hq0 : (C q : PowerSeries R) ≠ 0 := by
    intro h0; exact hq.ne_zero (by simpa using congrArg (constantCoeff) h0)
  apply mul_left_cancel₀ hq0
  rw [h, ht']; ring

end GlobalTheory.Col.Interp

namespace GlobalTheory.Col


open Interp in
theorem X_mul_mem_span_of_levels (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (hR : IsDomain R)
    (hpR : Prime (p : R)) (_hc : IsAdicComplete (Ideal.span {(p : R)}) R)
    (h : PowerSeries R) (k c : ℕ)
    (hyp : ∀ r, 1 ≤ r → r ≤ k → ∃ y : PowerSeries R, ev R p r h = ev R p r ((p : PowerSeries R) ^ c * y)) :
    ∀ j, j ≤ k → j ≤ c → X * h ∈ Ideal.span {(p : PowerSeries R) ^ (c - j), (1 + X) ^ (p ^ j) - 1} := by
  intro j
  induction j with
  | zero =>
    intro _ _
    refine Ideal.mem_span_pair.2 ⟨0, h, ?_⟩
    simp [mul_comm]
  | succ n ih =>
    intro hk hcn
    obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.1 (ih (by omega) (by omega))
    obtain ⟨y, hy⟩ := hyp (n + 1) (by omega) hk
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hy)
    obtain ⟨u, hu⟩ := cyc_sub_p (R := R) p n hp.out
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 + n := ⟨c - (n + 1), by omega⟩
    have e1 : m + 1 + n - n = m + 1 := by omega
    have e2 : m + 1 + n - (n + 1) = m := by omega
    rw [e1] at hAB
    rw [e2]
    set P : PowerSeries R := (p : PowerSeries R) with hP
    set om : PowerSeries R := (1 + X : PowerSeries R) ^ (p ^ n) - 1 with hom
    have key : C (p : R) * B = C (p : R) ^ (m + 1) * (u * A - u * X * P ^ n * y)
        + cyc R p (n + 1) * (B - u * X * g) := by
      rw [map_natCast]
      linear_combination (-B) * hu - u * hAB + (u * X) * hg
    have hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (cyc R p (n + 1)) ≠ 0 := by
      haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hpR.ne_zero).2 hpR
      intro h0
      have h1 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))) (om_succ (R := R) p n hp.out)
      rw [map_mul, h0, zero_mul] at h1
      refine one_add_X_pow_sub_one_ne_zero (R := R ⧸ Ideal.span {(p : R)}) (p ^ (n + 1))
        (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) ?_
      simpa using h1
    obtain ⟨t', ht'⟩ := cancel_prime hpR hf m key
    rw [map_natCast] at ht'
    refine Ideal.mem_span_pair.2 ⟨A * P + (u * A - u * X * P ^ n * y) * om, t', ?_⟩
    rw [om_succ (R := R) p n hp.out]
    linear_combination hAB - om * ht'

end GlobalTheory.Col
end
end

