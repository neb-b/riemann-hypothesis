module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormIntCastLeOfDvd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.PowCong

variable {l : ℕ} [Fact l.Prime]

theorem norm_intCast_eq (k : ℤ) : ‖(k : Qbar l)‖ = ‖(k : ℚ_[l])‖ := by
  rw [show (k : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (k : ℚ_[l]) from (map_intCast _ k).symm]
  exact PadicAlgCl.norm_extends l _

theorem norm_natCast_eq (n : ℕ) : ‖(n : Qbar l)‖ = ‖(n : ℚ_[l])‖ := by
  have := norm_intCast_eq (l := l) (n : ℤ)
  simpa using this

theorem norm_l_pow (r : ℕ) : ‖((l : ℕ) : Qbar l) ^ r‖ = (l : ℝ) ^ (-(r : ℤ)) := by
  rw [norm_pow, norm_natCast_eq, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]

theorem norm_intCast_le_of_dvd (r : ℕ) (k : ℤ) (h : ((l : ℤ) ^ r) ∣ k) : ‖(k : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  rw [norm_intCast_eq, norm_l_pow]
  exact (Padic.norm_int_le_pow_iff_dvd k r).mpr h

theorem norm_natCast_eq_one {n : ℕ} (h : ¬ l ∣ n) : ‖(n : Qbar l)‖ = 1 := by
  rw [norm_natCast_eq, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

theorem key (r e a b : ℕ) (ha : ¬ l ∣ a) (hb : b = a % l ^ r) (hb' : 1 ≤ r → ¬ l ∣ b) :
    ‖((a : Qbar l) ^ e)⁻¹ - ((b : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧
      ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hcong : ((l : ℤ) ^ r) ∣ (((a ^ e : ℕ) : ℤ) - ((b ^ e : ℕ) : ℤ)) := by
    have h1 := (Nat.mod_modEq a (l ^ r)).pow e
    have h2 := (Nat.modEq_iff_dvd.mp h1)
    rw [hb]
    push_cast at h2 ⊢
    exact h2
  have hsub : ‖(a : Qbar l) ^ e - (b : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    have := norm_intCast_le_of_dvd (l := l) r _ hcong
    push_cast at this
    exact this
  refine ⟨?_, hsub⟩
  have hna : ‖(a : Qbar l)‖ = 1 := norm_natCast_eq_one ha
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hb0 : b = 0 := by rw [hb, pow_zero, Nat.mod_one]
    subst hb0
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · rw [Nat.cast_zero, zero_pow he.ne', inv_zero, sub_zero, norm_inv, norm_pow, hna]
      simp
  · have hnb : ‖(b : Qbar l)‖ = 1 := norm_natCast_eq_one (hb' hr)
    have ha0 : ((a : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hna] at this; simp at this
    have hb0 : ((b : Qbar l) ^ e) ≠ 0 := by
      intro h; have := congrArg norm h; rw [norm_pow, hnb] at this; simp at this
    rw [inv_sub_inv ha0 hb0, norm_div, norm_mul, norm_pow, norm_pow, hna, hnb, one_pow, mul_one, div_one,
      norm_sub_rev]
    exact hsub

theorem powCong : ∀ (l : ℕ) [Fact l.Prime] (e r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ), ‖(((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e)⁻¹ - (((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ ∧ ‖((x : ZMod (l ^ (r + 1))).val : Qbar l) ^ e - ((((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : Qbar l) ^ e‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l hl e r x
  have hp : l.Prime := hl.out
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have notdvd : ∀ {k : ℕ}, 1 ≤ k → (u : (ZMod (l ^ k))ˣ) → ¬ l ∣ (u : ZMod (l ^ k)).val := by
    intro k hk u hd
    have hc := ZMod.val_coe_unit_coprime u
    have : l ∣ Nat.gcd (u : ZMod (l ^ k)).val (l ^ k) := Nat.dvd_gcd hd (dvd_pow_self l (by omega))
    rw [hc] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  refine key (l := l) r e _ _ (notdvd (by omega) x) ?_ (fun hr => notdvd hr _)
  rw [Units.coe_map]
  simp only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, ZMod.castHom_apply]
  rw [ZMod.cast_eq_val, ZMod.val_natCast]

end GlobalTheory.PowCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastOfCoprime
section
noncomputable section

namespace GlobalTheory.PadicNormCastBounds

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_le_one_of_isIntegral {x : PadicAlgCl l} (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hz : ∀ a : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
    intro a
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact a.2
  let v := NormedField.valuation (K := PadicAlgCl l)
  let φ : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer fun a => by
      rw [Valuation.mem_integer_iff]
      exact_mod_cast hz a
  have h1 : IsIntegral v.integer x := hx.map_of_comp_eq φ (RingHom.id _) (by ext a; rfl)
  have h2 := (Valuation.integer.integers v).mem_of_integral h1
  rw [Valuation.mem_integer_iff] at h2
  exact_mod_cast h2

theorem norm_natCast_of_coprime {a : ℕ} (ha : a.Coprime l) : ‖(a : PadicAlgCl l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact ha.symm

theorem norm_inv_pow_val_le (r e : ℕ) (u : (ZMod (l ^ r))ˣ) :
    ‖((((u : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (u : ZMod (l ^ 0)).val = 0 := by
      have := ZMod.val_lt (u : ZMod (l ^ 0))
      simpa using this
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp
    · simp [he.ne']
  · have hc : (u : ZMod (l ^ r)).val.Coprime l :=
      (ZMod.val_coe_unit_coprime u).coprime_dvd_right (dvd_pow_self l hr.ne')
    rw [norm_inv, norm_pow, norm_natCast_of_coprime hc]
    simp

theorem norm_inv_pow_sub_le {a b r : ℕ} (e : ℕ) (ha : a.Coprime l) (hb : b.Coprime l) (h : a ≡ b [MOD l ^ r]) :
    ‖((a : PadicAlgCl l) ^ e)⁻¹ - ((b : PadicAlgCl l) ^ e)⁻¹‖ ≤ ‖(l : PadicAlgCl l) ^ r‖ := by
  have na := norm_natCast_of_coprime ha
  have nb := norm_natCast_of_coprime hb
  have a0 : (a : PadicAlgCl l) ^ e ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [na]; exact one_ne_zero))
  have b0 : (b : PadicAlgCl l) ^ e ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [nb]; exact one_ne_zero))
  obtain ⟨k, hk⟩ := (h.pow e).dvd
  have hk' : (b : PadicAlgCl l) ^ e - (a : PadicAlgCl l) ^ e = (l : PadicAlgCl l) ^ r * (k : PadicAlgCl l) := by
    exact_mod_cast congrArg (Int.cast : ℤ → PadicAlgCl l) hk
  rw [inv_sub_inv a0 b0, hk', norm_div, norm_mul, norm_mul, norm_pow (a : PadicAlgCl l), norm_pow (b : PadicAlgCl l),
    na, nb, one_pow, one_mul, div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ k)

theorem twist_compat (l : ℕ) [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e : ℕ)
    (χ : (r : ℕ) → (ZMod (l ^ r))ˣ → Formalism.ConjugateSelfDual.Qbar l)
    (hO : ∀ (r : ℕ) (x : (ZMod (l ^ r))ˣ), χ r x ∈ c.O)
    (hχ : ∀ (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r
      (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) : ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x)‖ ≤
        ‖(l : Formalism.ConjugateSelfDual.Qbar l) ^ r‖)
    (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ) :
    ‖(fun x : (ZMod (l ^ (r + 1)))ˣ => (((ZMod.val (x : ZMod (l ^ (r + 1))) : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ * χ (r + 1) x) x -
      (fun x : (ZMod (l ^ r))ˣ => (((ZMod.val (x : ZMod (l ^ r)) : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ * χ r x)
        (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) :
          ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x)‖ ≤ ‖(l : Formalism.ConjugateSelfDual.Qbar l) ^ r‖ := by
  have h1 := hχ r x
  generalize hy : Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) :
    ZMod (l ^ Nat.succ r) →* ZMod (l ^ r)) x = y at h1 ⊢
  have hint : ‖χ r y‖ ≤ 1 :=
    norm_le_one_of_isIntegral
      ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨χ r y, hO r y⟩ : c.O)).map c.O.val)
  have hA := norm_inv_pow_val_le (r + 1) e x
  have hB := norm_inv_pow_val_le r e y
  have hAB : ‖((((x : ZMod (l ^ (r + 1))).val : ℕ) : PadicAlgCl l) ^ e)⁻¹ -
      ((((y : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹‖ ≤ ‖(l : PadicAlgCl l) ^ r‖ := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [pow_zero (l : PadicAlgCl l), norm_one, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA ?_)
      rwa [norm_neg]
    · refine norm_inv_pow_sub_le e
        ((ZMod.val_coe_unit_coprime x).coprime_dvd_right (dvd_pow_self l r.succ_ne_zero))
        ((ZMod.val_coe_unit_coprime y).coprime_dvd_right (dvd_pow_self l hr.ne')) ?_
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val, ← hy]
      rfl
  dsimp only
  set A := ((((x : ZMod (l ^ (r + 1))).val : ℕ) : PadicAlgCl l) ^ e)⁻¹
  set B := ((((y : ZMod (l ^ r)).val : ℕ) : PadicAlgCl l) ^ e)⁻¹
  have hsplit : A * χ (r + 1) x - B * χ r y = A * (χ (r + 1) x - χ r y) + (A - B) * χ r y := by ring
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hA).trans h1
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hint).trans hAB

end GlobalTheory.PadicNormCastBounds

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotCongruentZeroIntCastMulPrimePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.IntNorm

theorem norm_intCast_qbar (l : ℕ) [Fact l.Prime] (d : ℤ) :
    ‖(d : Qbar l)‖ = ‖(d : ℚ_[l])‖ := by
  have h : (d : Qbar l) = ((d : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends]

theorem norm_l_qbar (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
  have h : ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : PadicAlgCl l) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem not_cg_int_mul_pow (l : ℕ) [Fact l.Prime] (t k : ℕ) (d : ℤ) (hd : d ≠ 0)
    (hlt : |d| < (l : ℤ) ^ t) : ¬ Cg (t + k) ((d : Qbar l) * ((l : ℕ) : Qbar l) ^ k) 0 := by
  intro h
  unfold Cg at h
  rw [sub_zero, norm_mul, norm_pow, norm_pow, pow_add] at h
  have hlpos : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ := by
    rw [norm_l_qbar]; have := (Fact.out : l.Prime).pos; positivity
  have hk : (0 : ℝ) < ‖((l : ℕ) : Qbar l)‖ ^ k := pow_pos hlpos k
  have h1 : ‖(d : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l)‖ ^ t := le_of_mul_le_mul_right h hk
  rw [norm_intCast_qbar, norm_l_qbar] at h1
  have h2 : ‖(d : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(t : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact h1
  have h3 : ((l : ℤ) ^ t) ∣ d := (Padic.norm_int_le_pow_iff_dvd d t).mp h2
  have h4 : ((l : ℤ) ^ t) ≤ |d| := by
    have := Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs _ _).mpr h3)
    exact this
  omega

end GlobalTheory.Ord2.IntNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RatUnramToIntUnram
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory


open Polynomial in
theorem coefO_dvd_pow_l {l : ℕ} [Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ∈ c.O)
    (h0 : x ≠ 0) : ∃ k : ℕ, ∃ u ∈ c.O, x * u = ((l : ℕ) : Qbar l) ^ k := by
  haveI := c.fin
  haveI := c.dvr
  set x' : c.O := ⟨x, hx⟩
  have hx0 : x' ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hint : IsIntegral ℤ_[l] x' := Algebra.IsIntegral.isIntegral x'
  obtain ⟨p, hpm, hp⟩ := hint
  rw [← aeval_def] at hp
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hq
  rw [X_dvd_iff] at hq
  have hqx : aeval x' q = 0 := by
    rw [hpq, map_mul, map_pow, aeval_X] at hp
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hx0)
  obtain ⟨r, hr⟩ := (X_dvd_sub_C : X ∣ q - C (q.coeff 0))
  have hrel : algebraMap ℤ_[l] c.O (q.coeff 0) = x' * (-(aeval x' r)) := by
    have := congrArg (aeval x') hr
    rw [map_sub, aeval_C, map_mul, aeval_X, hqx] at this
    linear_combination -this
  set a := q.coeff 0 with ha
  set w : ℤ_[l]ˣ := PadicInt.unitCoeff hq
  have hspec : a = (w : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation := PadicInt.unitCoeff_spec hq
  have haw : a * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = (l : ℤ_[l]) ^ a.valuation := by
    calc a * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
        = ((w : ℤ_[l]) * (l : ℤ_[l]) ^ a.valuation) * ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := by rw [← hspec]
      _ = (l : ℤ_[l]) ^ a.valuation := by
        rw [mul_comm, ← mul_assoc]; simp
  refine ⟨a.valuation, (((-(aeval x' r)) * algebraMap ℤ_[l] c.O ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : c.O) : Qbar l),
    Subtype.property _, ?_⟩
  have h2 : x' * ((-(aeval x' r)) * algebraMap ℤ_[l] c.O ((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]))
      = algebraMap ℤ_[l] c.O ((l : ℤ_[l]) ^ a.valuation) := by
    rw [← mul_assoc, ← hrel, ← map_mul, haw]
  have h3 := congrArg Subtype.val h2
  simpa using h3

end GlobalTheory

namespace GlobalTheory

theorem rat_unram_to_int_unram : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → ∃ m : ℕ, ∀ (Y : G ℚ Ω → Fin 2 → Qbar l) (v : Fin 2 → Qbar l), (∀ s i, Y s i ∈ c.O) → (∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ v - v) → ∃ t : Fin 2 → Qbar l, (∀ i, t i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, (((l : ℕ) : Qbar l) ^ m) • Y s = mat W s *ᵥ t - t := by
  intro l _ Ω _ _ W c B _hW hWO
  let A : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l) := fun s => mat W s - 1
  have hAO : ∀ s i j, A s i j ∈ c.O := by
    intro s i j
    simp only [A, Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact sub_mem (hWO s i j) (one_mem _)
    · simpa using hWO s i j
  have hmv : ∀ s (w : Fin 2 → Qbar l) i,
      (mat W s *ᵥ w - w) i = A s i 0 * w 0 + A s i 1 * w 1 := by
    intro s w i
    rw [show mat W s *ᵥ w - w = A s *ᵥ w by simp [A, Matrix.sub_mulVec]]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  by_cases h2 : ∃ s ∈ Ine (F := ℚ) B, ∃ s' ∈ Ine (F := ℚ) B, ∃ i i' : Fin 2,
      A s i 0 * A s' i' 1 - A s i 1 * A s' i' 0 ≠ 0
  · obtain ⟨s, hs, s', hs', i, i', hd⟩ := h2
    obtain ⟨k, u, hu, hdu⟩ := coefO_dvd_pow_l c
      (sub_mem (mul_mem (hAO s i 0) (hAO s' i' 1)) (mul_mem (hAO s i 1) (hAO s' i' 0))) hd
    refine ⟨k, fun Y v hY hYv => ⟨((l : ℕ) : Qbar l) ^ k • v, ?_, ?_⟩⟩
    · have hP := hY s i
      have hQ := hY s' i'
      rw [hYv s hs, hmv] at hP
      rw [hYv s' hs', hmv] at hQ
      intro j
      fin_cases j
      · have e : ((l : ℕ) : Qbar l) ^ k • v 0 = u * (A s' i' 1 * (A s i 0 * v 0 + A s i 1 * v 1)
            - A s i 1 * (A s' i' 0 * v 0 + A s' i' 1 * v 1)) := by
          rw [smul_eq_mul]; linear_combination (-(v 0)) * hdu
        simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply]
        rw [e]
        exact mul_mem hu (sub_mem (mul_mem (hAO _ _ _) hP) (mul_mem (hAO _ _ _) hQ))
      · have e : ((l : ℕ) : Qbar l) ^ k • v 1 = u * (A s i 0 * (A s' i' 0 * v 0 + A s' i' 1 * v 1)
            - A s' i' 0 * (A s i 0 * v 0 + A s i 1 * v 1)) := by
          rw [smul_eq_mul]; linear_combination (-(v 1)) * hdu
        simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply]
        rw [e]
        exact mul_mem hu (sub_mem (mul_mem (hAO _ _ _) hQ) (mul_mem (hAO _ _ _) hP))
    · intro s₀ hs₀
      rw [hYv s₀ hs₀, smul_sub, Matrix.mulVec_smul]
  · push_neg at h2
    by_cases h1 : ∃ s ∈ Ine (F := ℚ) B, ∃ i j, A s i j ≠ 0
    · obtain ⟨s, hs, i, j, hα⟩ := h1
      obtain ⟨k, u, hu, hαu⟩ := coefO_dvd_pow_l c (hAO s i j) hα
      refine ⟨k, fun Y v hY hYv => ⟨Pi.single j (u * Y s i), ?_, ?_⟩⟩
      · intro j'
        rcases eq_or_ne j' j with rfl | h
        · simpa using mul_mem hu (hY s i)
        · simp [h]
      · intro s' hs'
        have hc : Y s i = A s i 0 * v 0 + A s i 1 * v 1 := by rw [hYv s hs, hmv]
        ext i'
        rw [Pi.smul_apply, hmv, hYv s' hs', hmv, hc]
        have hdet := h2 s hs s' hs' i i'
        fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue] at hαu ⊢
          simp [Pi.single_apply]
          linear_combination (-(A s' i' 0 * v 0 + A s' i' 1 * v 1)) * hαu + u * v 1 * hdet
        · simp only [Fin.mk_one, Fin.isValue] at hαu ⊢
          simp [Pi.single_apply]
          linear_combination (-(A s' i' 0 * v 0 + A s' i' 1 * v 1)) * hαu - u * v 0 * hdet
    · push_neg at h1
      refine ⟨0, fun Y v _ hYv => ⟨0, fun _ => zero_mem _, fun s hs => ?_⟩⟩
      ext i
      rw [Pi.smul_apply, hYv s hs, hmv, hmv]
      simp [h1 s hs]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducibleStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forall_ad_invariant_eq_zero_of_isIrr : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ → ∀ v : Fin 3 → K, (∀ g, ad (ρ g) *ᵥ v = v) → v = 0 := by
  first | exact @GlobalTheory.ad_invariant_eq_zero_of_isIrr | exact GlobalTheory.ad_invariant_eq_zero_of_isIrr | (intros; apply GlobalTheory.ad_invariant_eq_zero_of_isIrr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ

theorem toGQ_mul_of_pos (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dite_eq_left hmm, dite_eq_left h, dite_eq_left h']
  apply Subtype.ext
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul] at *
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

theorem mZl_mul (l : ℕ) [Fact l.Prime] (m m' : Matrix (Fin 2) (Fin 2) ℤ) :
    mZl l (m * m') = mZl l m * mZl l m' := by
  unfold mZl; rw [Matrix.map_mul]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.kmap_kmap (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) (x : X.Khat l) :
    X.kmap l ψ (X.kmap l φ x) = X.kmap l (φ.trans ψ) x := by
  unfold Tower.kmap
  simp only [LinearMap.restrictScalars_apply]
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp]
  congr 3

theorem Tower.sl_mul_toRingEquiv (X : Tower Ω ε) (g h : GQ) :
    (X.sl (g * h)).toRingEquiv = (X.sl g).toRingEquiv.trans (X.sl h).toRingEquiv := by
  ext f; exact X.sl_mul g h f

theorem Tower.act_act (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (m m' : Matrix (Fin 2) (Fin 2) ℤ) (hm : 0 < m.det) (hm' : 0 < m'.det) (b : X.Fn l) :
    X.act l m' (X.act l m b) = X.act l (m * m') b := by
  funext u
  simp only [Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap, toGQ_mul_of_pos m m' hm hm', Tower.sl_mul_toRingEquiv, mZl_mul, Matrix.mulVec_mulVec]

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecApproxCocycle
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA

theorem spec_approx_cocycle (l : ℕ) [Fact l.Prime] {Γ X : Type} [Group Γ] [CommGroup X] [Fintype X] (r : ℕ)
    (ρ : Γ → Matrix (Fin 2) (Fin 2) (Qbar l)) (κ : Γ →* X) (Y : Γ → X → Fin 2 → Qbar l) (η : X → Qbar l)
    (τ : Γ → Qbar l) (hY : ShCoc ρ κ Y) (hρ : ∀ s i j, ‖ρ s i j‖ ≤ 1) (hYi : ∀ s x i, ‖Y s x i‖ ≤ 1)
    (hη : ∀ x, ‖η x‖ ≤ 1) (happ : ∀ s x, ‖η (x * (κ s)⁻¹) - η x * τ s‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) :
    ∀ s t i, ‖spec η Y (s * t) i - (spec η Y s + τ s • (ρ s *ᵥ spec η Y t)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro s t i
  have hre : (∑ x, η x • Y t (x * κ s)) = ∑ x, η (x * (κ s)⁻¹) • Y t x := by
    exact Fintype.sum_equiv (Equiv.mulRight (κ s)) _ _ (fun x => by simp)
  have key : spec η Y (s * t) - (spec η Y s + τ s • (ρ s *ᵥ spec η Y t))
      = ρ s *ᵥ ∑ x, (η (x * (κ s)⁻¹) - η x * τ s) • Y t x := by
    have h1 : spec η Y (s * t) = spec η Y s + ρ s *ᵥ ∑ x, η x • Y t (x * κ s) := by
      simp only [spec, hY s t, smul_add, Finset.sum_add_distrib, Matrix.mulVec_sum, Matrix.mulVec_smul]
    rw [h1, hre, ← Matrix.mulVec_smul, add_sub_add_left_eq_sub, ← Matrix.mulVec_sub]
    congr 1
    simp only [spec, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, sub_smul, mul_comm (τ s)]
  have hC : (0 : ℝ) ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := norm_nonneg _
  rw [← Pi.sub_apply, key]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
  intro j _
  rw [norm_mul]
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (hρ s i j)) ?_
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC
  intro x _
  rw [norm_mul]
  exact le_trans (mul_le_of_le_one_right (norm_nonneg _) (hYi t x j)) (happ s x)

end GlobalTheory.KA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecCauchy
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KA

theorem spec_cauchy : ∀ (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] (Y : ∀ r : ℕ, Γ → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l), (∀ r s x i, ‖Y r s x i‖ ≤ 1) → (∀ r x, ‖η r x‖ ≤ 1) → (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖η (r + 1) x - η r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∀ r s i, ‖spec (η (r + 1)) (Y (r + 1)) s i - spec (η r) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  intro l _ Γ _ Y η hY hη hYp hηc r s i
  set red := (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) with hred
  have hpush : spec (η r) (Y r) s i = ∑ x', η r (red x') * Y (r + 1) s x' i := by
    simp only [spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hYp r s]
    simp only [push, Finset.sum_apply, Finset.mul_sum]
    rw [← Finset.sum_fiberwise (Finset.univ) red (fun x' => η r (red x') * Y (r + 1) s x' i)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' hx' => ?_
    rw [(Finset.mem_filter.mp hx').2]
  have hspec : spec (η (r + 1)) (Y (r + 1)) s i = ∑ x', η (r + 1) x' * Y (r + 1) s x' i := by
    simp only [spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpush, hspec, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x' _ => ?_
  rw [← sub_mul, norm_mul]
  calc ‖η (r + 1) x' - η r (red x')‖ * ‖Y (r + 1) s x' i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ * 1 :=
        mul_le_mul (hηc r x') (hY _ _ _ _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := mul_one _

end GlobalTheory.KA
end

