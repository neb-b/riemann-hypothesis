module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharacterEntrySumEisensteinProduct
section
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

namespace GlobalTheory.KummerEisensteinGalois.UnitPieceMu

variable {K : Type} [Field K] [CharZero K]

theorem isUnit_iff_not_dvd_val (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (c : ZMod (p ^ m)) :
    IsUnit c ↔ ¬ p ∣ c.val := by
  have hp : p.Prime := Fact.out
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm, hp.coprime_iff_not_dvd]

theorem isUnit_natCast_of_not_dvd (p m N : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) : IsUnit (N : ZMod (p ^ m)) := by
  have hp : p.Prime := Fact.out
  rw [ZMod.isUnit_iff_coprime]
  exact (hp.coprime_iff_not_dvd.mpr hpN).symm.pow_right m


omit [CharZero K] in
theorem sum_pick (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (x z : ℤ) (F : ZMod (p ^ m) → K) :
    ∑ u ∈ primeTo p m, (if z ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] then F u else 0) =
    if ¬ (p : ℤ) ∣ z ∧ z ≡ (p : ℤ) ^ m * x [ZMOD N] then
      F ((z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))) else 0 := by
  have hp : p.Prime := Fact.out
  have hU := isUnit_natCast_of_not_dvd p m N hpN
  have h1 : (N : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) = 1 := Ring.mul_inverse_cancel _ hU
  have hP : (p : ZMod (p ^ m)) ^ m = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hcop : (N : ℤ).natAbs.Coprime ((p ^ m : ℕ) : ℤ).natAbs := by
    simp only [Int.natAbs_natCast]
    exact (hp.coprime_iff_not_dvd.mpr hpN).symm.pow_right m
  have key : ∀ u : ZMod (p ^ m), z ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] ↔
      (u = (z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) ∧ z ≡ (p : ℤ) ^ m * x [ZMOD N]) := by
    intro u
    rw [Nat.cast_mul, ← Int.modEq_and_modEq_iff_modEq_mul hcop, and_comm]
    refine and_congr ?_ ?_
    · rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, hP, zero_mul, add_zero]
      constructor
      · intro h; rw [h]; linear_combination (-u) * h1
      · intro h; rw [h]; linear_combination (-(z : ZMod (p ^ m))) * h1
    · rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd, add_sub_assoc]
      exact dvd_add_right (dvd_mul_right _ _)
  have hmem : (z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) ∈ primeTo p m ↔ ¬ (p : ℤ) ∣ z := by
    rw [primeTo, mem_filter, ← isUnit_iff_not_dvd_val p m hm, ← dvd_val_iff p m hm, ← isUnit_iff_not_dvd_val p m hm,
      IsUnit.mul_iff]
    simp [hU.ringInverse]
  simp only [key]
  by_cases hx : z ≡ (p : ℤ) ^ m * x [ZMOD N]
  · simp only [hx, and_true, sum_ite_eq', hmem]
  · simp [hx]

theorem row_sum (p m N j : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hpN : ¬ p ∣ N) (ζ : K) (x : ℤ) (s : ZMod (p ^ m) → ℤ)
    (Φ : ZMod (p ^ m) → ZMod (p ^ m) → K) (n : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m),
      Φ u a * coefPos j (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (s a) n =
    ∑ q ∈ (n : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ (p : ℤ) ^ m * x [ZMOD N] then
      (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
        ∑ a : ZMod (p ^ m), Φ ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))) a * ζ ^ (s a * q.2)
      else 0 := by
  have e : ∀ u : ZMod (p ^ m),
      ∑ a : ZMod (p ^ m), Φ u a * coefPos j (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * x) (s a) n =
      ∑ q ∈ (n : ℤ).divisorsAntidiag, if q.1 ≡ N * u.val + (p : ℤ) ^ m * x [ZMOD (N * p ^ m : ℕ)] then
        (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
          ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2) else 0 := by
    intro u
    simp_rw [coefPos_eq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    split_ifs
    · exact sum_congr rfl fun a _ => by ring
    · simp
  rw [sum_congr rfl fun u _ => e u, sum_comm]
  refine sum_congr rfl fun q _ => ?_
  exact sum_pick p m N hm hpN x q.1 (fun u => (q.2.sign : K) * ((q.1 : K) / (N * p ^ m : ℕ)) ^ (j - 1) *
    ∑ a : ZMod (p ^ m), Φ u a * ζ ^ (s a * q.2))

theorem col_sum_div (p m N : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ m))
    (n₁ n₂ d d' : ℤ) (h₁ : ¬ (p : ℤ) ∣ n₁) (h₂ : ¬ (p : ℤ) ∣ n₂) :
    ∑ a : ZMod (p ^ m), (∑ b : ZMod (p ^ m),
      ψ ((n₁ : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)) * b -
        a * ((n₂ : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
        ζ ^ ((N : ℤ) * b.val * d')) * ζ ^ ((N : ℤ) * a.val * d) =
      if (p : ℤ) ^ m ∣ n₁ * d + n₂ * d' ∧ ¬ (p : ℤ) ∣ d ∧ ¬ (p : ℤ) ∣ d' then
        (p : K) ^ m * gaussS p m ψ (ζ ^ N) * (ψ (n₁ : ZMod (p ^ m)) * ψ⁻¹ (N : ZMod (p ^ m))) *
          ψ⁻¹ (d' : ZMod (p ^ m)) else 0 := by
  have hU := isUnit_natCast_of_not_dvd p m N hpN
  have hI := hU.ringInverse
  have hval : ∀ z : ℤ, ¬ (p : ℤ) ∣ z →
      ¬ (p : ℤ) ∣ ((((z : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m))).val : ℕ) : ℤ) := by
    intro z hz
    rw [Int.natCast_dvd_natCast, ← isUnit_iff_not_dvd_val p m hm]
    refine IsUnit.mul ?_ hI
    rwa [isUnit_iff_not_dvd_val p m hm, dvd_val_iff p m hm]
  have hdvd : ∀ z : ℤ, (p : ℤ) ^ m ∣ z ↔ (z : ZMod (p ^ m)) = 0 := by
    intro z; rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl
  have h := col_sum p m N hm hN ψ hψ ζ hζ 0 0 _ _ d d' (hval n₁ h₁) (hval n₂ h₂)
  simp only [mul_zero, add_zero, zero_mul, zpow_zero, mul_one, hdvd, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val] at h
  rw [h, map_mul, ← MulChar.inv_apply]
  refine if_congr (and_congr_left' ?_) rfl rfl
  rw [hdvd, ← hI.mul_left_eq_zero (a := ((n₁ * d + n₂ * d' : ℤ) : ZMod (p ^ m)))]
  push_cast
  constructor <;> intro h <;> linear_combination h

theorem entry_sum (p m N k : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (hm : 1 ≤ m) (hN : 0 < N)
    (hpN : ¬ p ∣ N) (_hk : 3 ≤ k) (ψ : DirichletCharacter K (p ^ m)) (hψ : ψ.IsPrimitive) (ζ : K)
    (hζ : IsPrimitiveRoot ζ (N * p ^ m)) (a₀ b₀ t : ℤ) (ht : (p : ℤ) ^ m * t ≡ 1 [ZMOD N]) (i j : ℕ) :
    ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) =
    if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) *
      (((N * p ^ m : ℕ) : K) ^ (k - 2))⁻¹ * (ffMu N p m k ψ a₀ i * eeMu N p m ψ b₀ j) else 0 := by
  have hx : ∀ c z : ℤ, z ≡ (p : ℤ) ^ m * (c * t) [ZMOD N] ↔ z ≡ c [ZMOD N] := by
    intro c z
    have h : (p : ℤ) ^ m * (c * t) ≡ c [ZMOD N] := by
      have := ht.mul_left c
      rwa [mul_one, mul_left_comm] at this
    exact ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩
  have e1 : ∀ u a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) *
      (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i *
        coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) =
      (∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ b₀ [ZMOD N] then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
          ζ ^ ((N : ℤ) * b.val * q.2) else 0) *
      coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i := by
    intro u a
    have := row_sum p m N 1 hm hpN ζ (b₀ * t) (fun b => (N : ℤ) * b.val) (fun v b => ψ (u * b - a * v)) j
    simp only [Nat.sub_self, pow_zero, mul_one, hx] at this
    rw [← this]
    simp only [sum_mul]
    exact sum_congr rfl fun v _ => sum_congr rfl fun b _ => by ring
  simp only [e1]
  rw [row_sum p m N (k - 1) hm hpN ζ (a₀ * t) (fun a => (N : ℤ) * a.val)
    (fun u a => ∑ q ∈ (j : ℤ).divisorsAntidiag, if ¬ (p : ℤ) ∣ q.1 ∧ q.1 ≡ b₀ [ZMOD N] then (q.2.sign : K) *
        ∑ b : ZMod (p ^ m), ψ (u * b - a * ((q.1 : ZMod (p ^ m)) * Ring.inverse (N : ZMod (p ^ m)))) *
          ζ ^ ((N : ℤ) * b.val * q.2) else 0) i]
  have e2 : ∀ (c : Prop) [Decidable c] (C : K) (A B : ℤ × ℤ → K),
      (if c then C * ((∑ q ∈ (i : ℤ).divisorsAntidiag, A q) * ∑ q ∈ (j : ℤ).divisorsAntidiag, B q) else 0) =
      ∑ q ∈ (i : ℤ).divisorsAntidiag, ∑ q' ∈ (j : ℤ).divisorsAntidiag, if c then C * (A q * B q') else 0 := by
    intro c _ C A B
    split_ifs
    · rw [sum_mul_sum]; simp only [mul_sum]
    · simp
  rw [ffMu_eq, eeMu_eq, e2]
  refine sum_congr rfl fun q hq => ?_
  simp only [hx]
  by_cases h₁ : (p : ℤ) ∣ q.1
  · simp [h₁]
  by_cases g₁ : q.1 ≡ a₀ [ZMOD N]
  swap
  · simp [g₁]
  rw [if_pos ⟨h₁, g₁⟩]
  simp only [sum_mul (j : ℤ).divisorsAntidiag]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun q' hq' => ?_
  by_cases h₂ : (p : ℤ) ∣ q'.1
  · simp [h₂]
  by_cases g₂ : q'.1 ≡ b₀ [ZMOD N]
  swap
  · simp [g₂]
  simp only [if_pos (And.intro h₂ g₂), mul_assoc (q'.2.sign : K)]
  rw [← mul_sum, col_sum_div p m N hm hN hpN ψ hψ ζ hζ q.1 q'.1 q.2 q'.2 h₁ h₂,
    (Int.mem_divisorsAntidiag.mp hq).1, (Int.mem_divisorsAntidiag.mp hq').1]
  have hc : (p : ℤ) ^ m ∣ (i : ℤ) + j ↔ p ^ m ∣ i + j := by norm_cast
  simp only [hc]
  rw [show k - 1 - 1 = k - 2 from rfl, div_pow, div_eq_mul_inv]
  by_cases a1 : p ^ m ∣ i + j <;> by_cases a2 : (p : ℤ) ∣ q.2 <;> by_cases a3 : (p : ℤ) ∣ q'.2 <;>
    simp only [a1, a2, a3, h₁, h₂, g₁, g₂, not_true, not_false_iff, and_true, and_false, and_self, if_true, if_false,
      mul_zero, zero_mul, false_and]
  ring

end GlobalTheory.KummerEisensteinGalois.UnitPieceMu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterTriangular
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem minor_of_triangular (g : GL (Fin n) k) (m : Fin n)
    (h : (∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) :
    minor g m = ∏ i ∈ Finset.univ.filter (fun i => i ≤ m), g.val i i := by
  unfold minor
  have hdet : (g.val.toSquareBlockProp fun i => i ≤ m).det = ∏ i : {i : Fin n // i ≤ m}, g.val i i := by
    rcases h with h | h
    · rw [Matrix.det_of_lowerTriangular]
      · rfl
      · intro i j hij
        exact h i j (OrderDual.toDual_lt_toDual.1 hij)
    · rw [Matrix.det_of_upperTriangular]
      · rfl
      · intro i j hij
        exact h i j hij
  rw [hdet]
  exact (Finset.prod_subtype (Finset.univ.filter (fun i => i ≤ m)) (p := fun i => i ≤ m)
    (fun x => by simp) (fun i => g.val i i)).symm

theorem prod_div_nxt (ψ : Fin n → kˣ →* ℂˣ) (a : Fin n) (u : kˣ) :
    ∏ m ∈ Finset.univ.filter (fun m => a ≤ m), (ψ m / nxt ψ m) u = ψ a u := by
  let f : ℕ → ℂˣ := fun j => if h : j < n then ψ ⟨j, h⟩ u else 1
  have hf : ∀ m : Fin n, f m = ψ m u := fun m => by
    show (if h : (m : ℕ) < n then ψ ⟨m, h⟩ u else 1) = ψ m u
    rw [dite_eq_left m.isLt]
  have hnx : ∀ m : Fin n, nxt ψ m u = f (m + 1) := by
    intro m
    unfold nxt
    split_ifs with h
    · simp [f, h]
    · simp [f, h]
  let G : ℕ → ℂˣ := fun j => if (a : ℕ) ≤ j then (f (j + 1))⁻¹ / (f j)⁻¹ else 1
  rw [Finset.prod_filter]
  have hterm : ∀ m : Fin n, (if a ≤ m then (ψ m / nxt ψ m) u else 1) = G m := by
    intro m
    simp only [G, Fin.le_def, MonoidHom.div_apply, hnx, ← hf m, inv_div_inv]
  rw [Finset.prod_congr rfl fun m _ => hterm m, Fin.prod_univ_eq_prod_range G n, ← Finset.prod_filter]
  have hs : (Finset.range n).filter (fun j => (a : ℕ) ≤ j) = Finset.Ico (a : ℕ) n := by
    ext j; simp; omega
  rw [hs, Finset.prod_Ico_div (f := fun j => (f j)⁻¹) a.isLt.le]
  simp [f, hf a]

theorem theta_of_triangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (t : Fin n → kˣ), (∀ i, valuation k (t i : k) = 1) → (∀ i, g.val i i = t i) → ((∀ i j : Fin n, i < j → g.val i j = 0) ∨ ∀ i j : Fin n, j < i → g.val i j = 0) → theta ψ g = ∏ i, (ψ i (t i) : ℂ) := by
  intro k _ _ _ _ n ψ g t ht hd htri
  have hmin : ∀ m, minor g m = ((∏ i ∈ Finset.univ.filter (fun i => i ≤ m), t i : kˣ) : k) := by
    intro m
    rw [minor_of_triangular g m htri, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => hd i
  have hev : ∀ (χ : kˣ →* ℂˣ) (u : kˣ), valuation k (u : k) = 1 → ev χ u = χ u := by
    intro χ u hu
    unfold ev
    rw [dite_eq_left hu]
    congr 2
    ext
    rfl
  have hval : ∀ s : Finset (Fin n), valuation k ((∏ i ∈ s, t i : kˣ) : k) = 1 := by
    intro s
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_eq_one fun i _ => ht i
  unfold theta
  rw [Finset.prod_congr rfl fun m _ => by rw [hmin m, hev _ _ (hval _)]]
  rw [← Units.coe_prod, ← Units.coe_prod]
  congr 1
  simp only [map_prod]
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun i => Finset.univ.filter (fun m => i ≤ m))
    (by intro x y; simp)]
  exact Finset.prod_congr rfl fun i _ => prod_div_nxt ψ i (t i)

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeDataDependOnlyOnUnits
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem agree_div_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : (ψ i / ψ j) u = (ω i / ω j) u := by
  simp only [MonoidHom.div_apply, h i u hu, h j u hu]

theorem agree_triv_iff {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (i j : Fin n) (x : k) :
    Triv (ψ i / ψ j) x ↔ Triv (ω i / ω j) x := by
  constructor
  · intro H u hu hx
    rw [← agree_div_apply h i j u hu]
    exact H u hu hx
  · intro H u hu hx
    rw [agree_div_apply h i j u hu]
    exact H u hu hx

theorem agree_nxt_apply {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (u : kˣ)
    (hu : valuation k (u : k) = 1) : nxt ψ m u = nxt ω m u := by
  unfold nxt
  split_ifs
  · exact h _ u hu
  · rfl

theorem agree_ev {ψ ω : Fin n → kˣ →* ℂˣ} (h : Agree ψ ω) (m : Fin n) (x : k) :
    ev (ψ m / nxt ψ m) x = ev (ω m / nxt ω m) x := by
  unfold ev
  split_ifs with hx
  · have hv : valuation k ((Units.mk0 x fun h0 => by simp [h0] at hx : kˣ) : k) = 1 := by
      simpa using hx
    rw [MonoidHom.div_apply, MonoidHom.div_apply, h m _ hv, agree_nxt_apply h m _ hv]
  · rfl

theorem agree_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ ω : Fin n → kˣ →* ℂˣ), Agree ψ ω → grp ψ = grp ω ∧ theta ψ = theta ω ∧ (Ordered ψ → Ordered ω) ∧
      ∀ r, Cut ψ r → Cut ω r := by
  intro k _ _ _ _ n ψ ω h
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext g
    simp only [grp, Set.mem_setOf_eq, agree_triv_iff h]
  · funext g
    unfold theta
    exact Finset.prod_congr rfl fun m _ => agree_ev h m _
  · intro H i a b j hi ha hb x hT
    rw [← agree_triv_iff h]
    exact H i a b j hi ha hb x ((agree_triv_iff h i j x).2 hT)
  · intro r H i j hi hj hT
    exact H i j hi hj ((agree_triv_iff h i j 1).2 hT)

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelDatumIdempotentEqOfSameShape
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.CoDiag

theorem rk_eq_of_conj {G : Type} [Group G] [Fintype G] {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G M) (e e' : G → ℂ) (t : G) (h : ∀ u, e' (t * u * t⁻¹) = e u) :
    rk ρ e = rk ρ e' := by
  have h1 : op ρ e' = ρ t * op ρ e * ρ t⁻¹ := by
    unfold op
    rw [Finset.mul_sum, Finset.sum_mul, ← Equiv.sum_comp (MulAut.conj t).toEquiv]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [h]
  let T : M ≃ₗ[ℂ] M := LinearEquiv.ofLinear (ρ t) (ρ t⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
  have h2 : LinearMap.range (op ρ e') = (LinearMap.range (op ρ e)).map (T : M →ₗ[ℂ] M) := by
    have : op ρ e' = (T : M →ₗ[ℂ] M) ∘ₗ (op ρ e ∘ₗ (T.symm : M →ₗ[ℂ] M)) := by
      rw [h1]; rfl
    rw [this, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  unfold rk
  rw [h2, LinearEquiv.finrank_map_eq]

theorem exists_potential {N : ℕ} {A : Type} [Group A] (E : Fin N → Fin N → Prop)
    (hlt : ∀ a b, E a b → a < b) (huniq : ∀ a a' b, E a b → E a' b → a = a') (r : Fin N → A) :
    ∃ t : Fin N → A, ∀ a b, E a b → t b = t a * r a := by
  let F : ∀ b : Fin N, (∀ a, a < b → A) → A := fun b rec =>
    if h : ∃ a, E a b then rec h.choose (hlt _ _ h.choose_spec) * r h.choose else 1
  refine ⟨wellFounded_lt.fix F, fun a b hab => ?_⟩
  have h : ∃ a, E a b := ⟨a, hab⟩
  have ha : h.choose = a := huniq _ _ _ h.choose_spec hab
  rw [WellFounded.fix_eq]
  have : F b (fun y _ => wellFounded_lt.fix F y) = wellFounded_lt.fix F h.choose * r h.choose := dif_pos h
  rw [this, ha]

theorem exists_unit_shift (g : ℕ) [Fact g.Prime] (ψ ψ' : AddChar (ZMod g) ℂ) (h : ψ ≠ 1) (h' : ψ' ≠ 1) :
    ∃ c : (ZMod g)ˣ, ∀ x, ψ' x = ψ (c * x) := by
  have hp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one h
  have hinj := AddChar.to_mulShift_inj_of_isPrimitive hp
  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, (AddChar.card_eq (α := ZMod g)).symm⟩
  obtain ⟨c, hc⟩ := hbij.2 ψ'
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact h' (by rw [← hc, AddChar.mulShift_zero])
  exact ⟨Units.mk0 c hc0, fun x => by rw [← hc]; simp⟩

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

def diagUnit (t : Fin N → (ZMod g)ˣ) : GG g N where
  val := Matrix.diagonal fun a => (t a : ZMod g)
  inv := Matrix.diagonal fun a => (((t a)⁻¹ : (ZMod g)ˣ) : ZMod g)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.mul_inv, Matrix.diagonal_one]
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.inv_mul, Matrix.diagonal_one]

theorem conj_diagUnit_apply (t : Fin N → (ZMod g)ˣ) (u : GG g N) (a b : Fin N) :
    (diagUnit t * u * (diagUnit t)⁻¹).val a b = (t a : ZMod g) * u.val a b * ((t b)⁻¹ : (ZMod g)ˣ) := by
  have : (diagUnit t * u * (diagUnit t)⁻¹).val
      = Matrix.diagonal (fun a => (t a : ZMod g)) * u.val * Matrix.diagonal (fun a => (((t a)⁻¹ : (ZMod g)ˣ) : ZMod g)) := rfl
  rw [this, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_conj_diagUnit (L : Lev g N) (t : Fin N → (ZMod g)ˣ) (u : GG g N) :
    L.Mem (diagUnit t * u * (diagUnit t)⁻¹) ↔ L.Mem u := by
  have h0 : ∀ a b, (diagUnit t * u * (diagUnit t)⁻¹).val a b = 0 ↔ u.val a b = 0 := by
    intro a b
    rw [conj_diagUnit_apply, Units.mul_left_eq_zero, Units.mul_right_eq_zero]
  have h1 : ∀ a, (diagUnit t * u * (diagUnit t)⁻¹).val a a = u.val a a := by
    intro a
    rw [conj_diagUnit_apply, mul_right_comm, Units.mul_inv, one_mul]
  unfold Lev.Mem IsUp
  simp only [h0, h1]

theorem edge_lt (L : Lev g N) (a b : Fin N) (h : L.Edge a b) : a < b := by
  unfold Lev.Edge at h
  rw [Fin.lt_def]
  split_ifs at h <;> omega

theorem edge_unique (L : Lev g N) (a a' b : Fin N) (h : L.Edge a b) (h' : L.Edge a' b) : a = a' := by
  unfold Lev.Edge at h h'
  apply Fin.ext
  split_ifs at h h' <;> omega

theorem rk_e_eq : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = L'.sharp → L.s = L'.s → L.k = L'.k →
    rk ρ L.e = rk ρ L'.e := by
  intro g _ N M _ _ _ ρ L L' h1 h2 h3
  have hM : L'.Mem = L.Mem := by
    funext u
    unfold Lev.Mem
    rw [h1, h2, h3]
  have hE : L'.Edge = L.Edge := by
    funext a b
    unfold Lev.Edge
    rw [h1, h2, h3]
  obtain ⟨c, hc⟩ := exists_unit_shift g L.ψ L'.ψ L.hψ L'.hψ
  obtain ⟨t, ht⟩ := exists_potential L.Edge (edge_lt L) (edge_unique L) (fun a => c * L'.co a * (L.co a)⁻¹)
  refine rk_eq_of_conj ρ _ _ (diagUnit t) fun u => ?_
  have hchi : L'.chi (diagUnit t * u * (diagUnit t)⁻¹) = L.chi u := by
    unfold Lev.chi
    rw [hc, hE, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · rw [conj_diagUnit_apply, ht a b hab]
      simp only [Units.val_inv_eq_inv_val, Units.val_mul]
      have := (t a).ne_zero
      have := c.ne_zero
      have := (L.co a).ne_zero
      have := (L'.co a).ne_zero
      field_simp
    · simp
  unfold Lev.e eps
  rw [hchi, hM]
  simp only [mem_conj_diagUnit]

end GlobalTheory.BadShare.CoDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisActionPreservesGammaLevel
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem Tower.gal_level {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ)
    (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) (hM : 0 < M) (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic M Ω) (Polynomial.degree_cyclotomic_pos M Ω hM).ne'
  rw [Polynomial.isRoot_cyclotomic_iff] at hζ
  have hsζ : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hsζ.pow_eq_one
  intro γ hγ
  have hγ' := hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ'
  obtain ⟨-, h01, h10, -⟩ := hγ'
  have key := X.recip M f hM hf ζ hζ s (i : ℤ) (by rw [zpow_natCast, hi]) γ γ
    ⟨rfl, by simp [en, h01], by simp [en, h10], rfl⟩
  rw [hf γ hγ] at key
  exact key.symm

end GlobalTheory
end

