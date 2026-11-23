module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
section
noncomputable section

open Finset

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def ffMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ a [ZMOD N] then ψ ((s / d : ℕ) : ZMod (p ^ m)) * ((s / d : ℕ) : K) ^ (k - 2) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ a [ZMOD N] then ψ (-((s / d : ℕ) : ZMod (p ^ m))) * (-((s / d : ℕ) : K)) ^ (k - 2) else 0))
    else 0

def eeMu (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (b : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ b [ZMOD N] then ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ b [ZMOD N] then ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) else 0))
    else 0

def coPtMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a b : ℤ) : ℕ → K :=
  cmul (ffMu N p m k ψ a) (eeMu N p m ψ b)

def coPtS (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * coPtMu N p m k ψ x 1 s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * coPtMu N p m k ψ (c * x) 1 s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ x d s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ (c * x) d s

end GlobalTheory.KummerEisensteinGalois
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
section
noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.CyclotomicQExpansion

open GlobalTheory.KZ

section Ops

variable {R : Type*} [CommRing R]

def cm (c : ℚ → R) (φ : HahnSeries ℚ R) : HahnSeries ℚ R where
  coeff r := c r * φ.coeff r
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

def qD [Algebra ℚ R] (φ : HahnSeries ℚ R) : HahnSeries ℚ R := cm (fun r => algebraMap ℚ R r) φ

def scale (a : ℚ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R :=
  if h : 0 < a then HahnSeries.embDomain (OrderIso.mulLeft₀ a h).toOrderEmbedding φ else φ

def latPart (N : ℕ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R :=
  cm (fun r => if ((N : ℚ) * r).den = 1 then 1 else 0) φ

def uqN (N q : ℕ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R := latPart N (scale ((q : ℚ)⁻¹) φ)

def uq (q : ℕ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R := uqN 1 q φ

def vq (q : ℕ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R := scale (q : ℚ) φ

def IsLat (N : ℕ) (φ : HahnSeries ℚ R) : Prop := ∀ r : ℚ, φ.coeff r ≠ 0 → ((N : ℚ) * r).den = 1

namespace Api

@[local simp] theorem coeff_cm (c : ℚ → R) (φ : HahnSeries ℚ R) (r : ℚ) : (cm c φ).coeff r = c r * φ.coeff r := rfl

theorem cm_add (c : ℚ → R) (φ ψ : HahnSeries ℚ R) : cm c (φ + ψ) = cm c φ + cm c ψ := by
  ext r; simp [mul_add]

theorem cm_smul (c : ℚ → R) (t : R) (φ : HahnSeries ℚ R) : cm c (t • φ) = t • cm c φ := by
  ext r; simp [mul_left_comm]

@[local simp] theorem coeff_qD [Algebra ℚ R] (φ : HahnSeries ℚ R) (r : ℚ) :
    (qD φ).coeff r = algebraMap ℚ R r * φ.coeff r := rfl

theorem coeff_scale_mul {a : ℚ} (ha : 0 < a) (φ : HahnSeries ℚ R) (r : ℚ) :
    (scale a φ).coeff (a * r) = φ.coeff r := by
  unfold scale
  rw [dif_pos ha]
  exact HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ a ha).toOrderEmbedding) (x := φ) (a := r)

theorem coeff_scale {a : ℚ} (ha : 0 < a) (φ : HahnSeries ℚ R) (r : ℚ) :
    (scale a φ).coeff r = φ.coeff (r / a) := by
  rw [← coeff_scale_mul ha φ (r / a), mul_div_cancel₀ _ ha.ne']

theorem scale_add (a : ℚ) (φ ψ : HahnSeries ℚ R) : scale a (φ + ψ) = scale a φ + scale a ψ := by
  by_cases ha : 0 < a
  · ext r; simp [coeff_scale ha]
  · simp [scale, ha]

theorem scale_smul (a : ℚ) (t : R) (φ : HahnSeries ℚ R) : scale a (t • φ) = t • scale a φ := by
  by_cases ha : 0 < a
  · ext r; simp [coeff_scale ha]
  · simp [scale, ha]

theorem scale_mul (a : ℚ) (φ ψ : HahnSeries ℚ R) : scale a (φ * ψ) = scale a φ * scale a ψ := by
  by_cases ha : 0 < a
  · simp only [scale, dif_pos ha]
    exact HahnSeries.embDomain_mul _ (fun x y => mul_add a x y) φ ψ
  · simp [scale, ha]

theorem coeff_latPart (N : ℕ) (φ : HahnSeries ℚ R) (r : ℚ) :
    (latPart N φ).coeff r = if ((N : ℚ) * r).den = 1 then φ.coeff r else 0 := by
  simp [latPart]

theorem coeff_uqN (N : ℕ) {q : ℕ} (hq : 0 < q) (φ : HahnSeries ℚ R) (r : ℚ) :
    (uqN N q φ).coeff r = if ((N : ℚ) * r).den = 1 then φ.coeff (q * r) else 0 := by
  have h : (0 : ℚ) < (q : ℚ)⁻¹ := by positivity
  rw [uqN, coeff_latPart, coeff_scale h, div_inv_eq_mul, mul_comm r]

theorem coeff_uq {q : ℕ} (hq : 0 < q) (φ : HahnSeries ℚ R) (r : ℚ) :
    (uq q φ).coeff r = if r.den = 1 then φ.coeff (q * r) else 0 := by
  rw [uq, coeff_uqN 1 hq]; simp

theorem coeff_vq {q : ℕ} (hq : 0 < q) (φ : HahnSeries ℚ R) (r : ℚ) : (vq q φ).coeff r = φ.coeff (r / q) :=
  coeff_scale (by exact_mod_cast hq) φ r

end Api

end Ops

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def sub (ε : Ω →+* ℂ) (a b d : ℚ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω :=
  scale (a / d) (cm (fun r => eOm ε (r * b / d)) φ)

def hq (ε : Ω →+* ℂ) (q : ℕ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω :=
  ((q : Ω)⁻¹) • ∑ j ∈ Finset.range q, sub ε 1 (j : ℚ) (q : ℚ) φ

namespace Api

attribute [local simp] coeff_cm coeff_qD


omit [Algebra ℚ Ω] in
theorem coeff_sub_upper {a d : ℚ} (h : 0 < a / d) (b : ℚ) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (sub ε a b d φ).coeff (r * a / d) = eOm ε (r * b / d) * φ.coeff r := by
  rw [sub, mul_div_assoc, mul_comm r, coeff_scale_mul h, coeff_cm]


omit [Algebra ℚ Ω] in
theorem sub_map_add (a b d : ℚ) (φ ψ : HahnSeries ℚ Ω) : sub ε a b d (φ + ψ) = sub ε a b d φ + sub ε a b d ψ := by
  simp only [sub, cm_add, scale_add]


omit [Algebra ℚ Ω] in
theorem sub_map_smul (a b d : ℚ) (t : Ω) (φ : HahnSeries ℚ Ω) : sub ε a b d (t • φ) = t • sub ε a b d φ := by
  simp only [sub, cm_smul, scale_smul]

theorem ent_div_pos (g : GQ) (hg : ent g 1 0 = 0) : 0 < ent g 0 0 / ent g 1 1 := by
  have h : 0 < ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := g.2
  rw [Matrix.det_fin_two] at h
  change 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 at h
  rw [hg, mul_zero, sub_zero] at h
  exact div_pos_iff.2 (mul_pos_iff.1 h)

theorem exp_sl_upper (X : Tower Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : X.K) :
    X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  have h := ent_div_pos g hg
  ext s
  obtain ⟨r, rfl⟩ : ∃ r, s = r * ent g 0 0 / ent g 1 1 :=
    ⟨s / (ent g 0 0 / ent g 1 1), by rw [mul_div_assoc, div_mul_cancel₀ _ h.ne']⟩
  rw [X.exp_upper g hg, coeff_sub_upper h]


omit [Algebra ℚ Ω] in
theorem eOm_eq_of {x : ℚ} {c : Ω} (h : ε c = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) : eOm ε x = c := by
  rw [eOm, ← h]; exact Function.leftInverse_invFun ε.injective c


omit [Algebra ℚ Ω] in
theorem eOm_intCast_div {q : ℕ} {ζ : Ω} (hζ : ε ζ = Complex.exp (2 * Real.pi * Complex.I / q)) (n : ℤ) :
    eOm ε ((n : ℚ) / q) = ζ ^ n := by
  apply eOm_eq_of
  rw [map_zpow₀, hζ, ← Complex.exp_int_mul]
  congr 1; push_cast; ring


omit [Algebra ℚ Ω] in
theorem exists_root_of_isAlgClosed [IsAlgClosed Ω] (ε : Ω →+* ℂ) {q : ℕ} (hq : 0 < q) :
    ∃ ζ : Ω, ε ζ = Complex.exp (2 * Real.pi * Complex.I / q) := by
  haveI : CharZero Ω := ε.charZero
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  obtain ⟨i, -, hi⟩ := (hξ.map_of_injective ε.injective).eq_pow_of_pow_eq_one
    (Complex.isPrimitiveRoot_exp q hq.ne').pow_eq_one
  exact ⟨ξ ^ i, by rw [map_pow, hi]⟩


omit [Algebra ℚ Ω] in
theorem coeff_hq {q : ℕ} (hq0 : 0 < q) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (hq ε q φ).coeff r = (q : Ω)⁻¹ * (∑ j ∈ Finset.range q, eOm ε (r * j)) * φ.coeff (q * r) := by
  have h0 : (0 : ℚ) < q := by exact_mod_cast hq0
  rw [hq, HahnSeries.coeff_smul, HahnSeries.coeff_sum, smul_eq_mul, mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have := coeff_sub_upper (ε := ε) (a := 1) (d := q) (by positivity) j φ (q * r)
  rw [show (q : ℚ) * r * 1 / q = r by field_simp, show (q : ℚ) * r * j / q = r * j by field_simp] at this
  exact this


omit [Algebra ℚ Ω] in
theorem hq_eq_uq {q : ℕ} (hq0 : 0 < q) (hζ : ∃ ζ : Ω, ε ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    {φ : HahnSeries ℚ Ω} (hφ : IsLat 1 φ) : hq ε q φ = uq q φ := by
  obtain ⟨ζ, hζ⟩ := hζ
  haveI : CharZero Ω := ε.charZero
  have h0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
  have h1 : (q : Ω) ≠ 0 := by exact_mod_cast hq0.ne'
  have hp : IsPrimitiveRoot ζ q :=
    IsPrimitiveRoot.of_map_of_injective (f := ε) (hζ ▸ Complex.isPrimitiveRoot_exp q hq0.ne') ε.injective
  ext r
  rw [coeff_hq hq0, coeff_uq hq0]
  by_cases hc : φ.coeff (q * r) = 0
  · simp [hc]
  have hd := hφ _ hc
  rw [Nat.cast_one, one_mul] at hd
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (q : ℚ) * r = n := ⟨_, (Rat.coe_int_num_of_den_eq_one hd).symm⟩
  have hr : r = n / q := by rw [← hn]; field_simp
  have he : ∀ j : ℕ, eOm ε (r * j) = (ζ ^ n) ^ j := fun j => by
    rw [← zpow_natCast, ← zpow_mul, ← eOm_intCast_div hζ, hr]; congr 1; push_cast; ring
  simp only [he]
  split_ifs with hr1
  · have : ζ ^ n = 1 := by
      rw [hp.zpow_eq_one_iff_dvd]
      refine ⟨r.num, ?_⟩
      have : (n : ℚ) = q * r.num := by rw [Rat.coe_int_num_of_den_eq_one hr1, hn]
      exact_mod_cast this
    simp [this, h1]
  · have hne : ζ ^ n ≠ 1 := by
      rw [Ne, hp.zpow_eq_one_iff_dvd]
      rintro ⟨m, rfl⟩
      apply hr1
      have : r = m := by rw [hr]; push_cast; field_simp
      rw [this, Rat.den_intCast]
    have hq1 : (ζ ^ n) ^ q = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp.pow_eq_one, one_zpow]
    rw [geom_sum_eq hne, hq1]; simp


omit [Algebra ℚ Ω] in
theorem hq_eq_uq_of_isAlgClosed [IsAlgClosed Ω] {q : ℕ} (hq0 : 0 < q) {φ : HahnSeries ℚ Ω} (hφ : IsLat 1 φ) :
    hq ε q φ = uq q φ := hq_eq_uq hq0 (exists_root_of_isAlgClosed ε hq0) hφ

end Api

end GlobalTheory.CyclotomicQExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
section
noncomputable section

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4

open GlobalTheory.KZ

section Hahn

variable {Ω : Type} [Field Ω]

theorem hahn_pow_order_leadingCoeff (s : HahnSeries ℚ Ω) (hs : s ≠ 0) (n : ℕ) :
    (s ^ n).order = n • s.order ∧ (s ^ n).leadingCoeff = s.leadingCoeff ^ n := by
  refine ⟨HahnSeries.order_pow s n, ?_⟩
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]

private theorem hahnSeries_algebraMap_mul_coeff (c : Ω) (x : HahnSeries ℚ Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c * x).coeff r = c * x.coeff r := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem hahn_transcendental {s : HahnSeries ℚ Ω} (hs : s ≠ 0) (ho : s.order < 0) : Transcendental Ω s := by
  rintro ⟨P, hP, hPs⟩
  have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hP
  have hls : s.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.2 hs
  have key : (Polynomial.aeval s P).coeff (P.natDegree • s.order) =
      P.coeff P.natDegree * s.leadingCoeff ^ P.natDegree := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_range_succ, Finset.sum_eq_zero]
    · rw [zero_add]
      rw [Algebra.smul_def, hahnSeries_algebraMap_mul_coeff]
      rw [← (hahn_pow_order_leadingCoeff s hs P.natDegree).1,
        ← HahnSeries.leadingCoeff_eq, (hahn_pow_order_leadingCoeff s hs P.natDegree).2]
    · intro k hk
      rw [Algebra.smul_def, hahnSeries_algebraMap_mul_coeff]
      rw [HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [(hahn_pow_order_leadingCoeff s hs k).1, nsmul_eq_mul, nsmul_eq_mul]
      exact mul_lt_mul_of_neg_right (by exact_mod_cast Finset.mem_range.1 hk) ho
  rw [hPs] at key
  exact mul_ne_zero hlead (pow_ne_zero _ hls) (by simpa using key.symm)

end Hahn

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem mem_lev_iff (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (f : X.K) :
    f ∈ lev X Γ' ↔ ∀ γ ∈ Γ', X.sl (ofSL γ) f = f := by
  unfold lev
  simp only [Subfield.mem_iInf, RingHom.mem_eqLocusField]
  rfl

theorem algebraMap_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (c : Ω) : algebraMap Ω X.K c ∈ lev X Γ' := (mem_lev_iff X Γ' _).2 fun γ _ => (X.sl (ofSL γ)).commutes c

theorem jK_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : X.jK ∈ lev X Γ' := (mem_lev_iff X Γ' _).2 fun γ _ => X.j_inv γ

theorem mdl_le_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : mdl X Γ' S ≤ lev X Γ' := by
  unfold mdl
  exact inf_le_left

theorem jK_transcendental (X : Tower Ω ε) : Transcendental Ω X.jK := by
  have h1 : (X.exp X.jK).coeff (-1) ≠ 0 := by rw [X.j_exp.1]; exact one_ne_zero
  have hne : X.exp X.jK ≠ 0 := fun h => h1 (by rw [h]; rfl)
  have hord : (X.exp X.jK).order < 0 :=
    lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero h1) (by norm_num)
  exact fun h => hahn_transcendental hne hord (h.algHom X.exp)

def levConst (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Ω →+* lev X Γ' :=
  (algebraMap Ω X.K).codRestrict (lev X Γ') (algebraMap_mem_lev X Γ')

def jPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Polynomial Ω →+* lev X Γ' :=
  Polynomial.eval₂RingHom (levConst X Γ') ⟨X.jK, jK_mem_lev X Γ'⟩

theorem coe_jPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (P : Polynomial Ω) :
    ((jPoly X Γ' P : lev X Γ') : X.K) = Polynomial.aeval X.jK P := by
  change (lev X Γ').subtype (Polynomial.eval₂ (levConst X Γ') ⟨X.jK, jK_mem_lev X Γ'⟩ P) = _
  rw [Polynomial.hom_eval₂, Polynomial.aeval_def]
  rfl

theorem jPoly_injective (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Function.Injective (jPoly X Γ') := by
  refine (injective_iff_map_eq_zero _).2 fun P hP => ?_
  have h : Polynomial.aeval X.jK P = 0 := by
    rw [← coe_jPoly, hP]; rfl
  by_contra hne
  exact jK_transcendental X ⟨P, hne, h⟩

def jRat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : RatFunc Ω →+* lev X Γ' :=
  RatFunc.liftRingHom (jPoly X Γ') (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (jPoly_injective X Γ'))

theorem jRat_algebraMap (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (P : Polynomial Ω) :
    jRat X Γ' (algebraMap (Polynomial Ω) (RatFunc Ω) P) = jPoly X Γ' P := RatFunc.liftRingHom_algebraMap _ _ P

theorem exp_injective (X : Tower Ω ε) : Function.Injective X.exp := (X.exp : X.K →+* HahnSeries ℚ Ω).injective

theorem exp_algebraMap_coeff (X : Tower Ω ε) (c : Ω) (r : ℚ) :
    (X.exp (algebraMap Ω X.K c)).coeff r = if r = 0 then c else 0 := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C]
  change (HahnSeries.single (0 : ℚ) c).coeff r = _
  split_ifs with h
  · rw [h]
    exact HahnSeries.coeff_single_same _ _
  · exact HahnSeries.coeff_single_of_ne h

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply exp_injective X
  ext r
  rw [X.gal_exp, exp_algebraMap_coeff, exp_algebraMap_coeff]
  split_ifs <;> simp

theorem gal_jK (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply exp_injective X
  ext r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [X.gal_exp, hn, map_intCast]

theorem mem_mdl_iff (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (f : X.K) :
    f ∈ mdl X Γ' S ↔ f ∈ lev X Γ' ∧ ∀ s ∈ S, X.gal s f = f := by
  unfold mdl
  simp only [Subfield.mem_inf, Subfield.mem_iInf, RingHom.mem_eqLocusField]
  rfl

theorem algebraMap_mem_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (c : Ω)
    (hc : ∀ s ∈ S, s c = c) : algebraMap Ω X.K c ∈ mdl X Γ' S := (mem_mdl_iff X Γ' S _).2 ⟨algebraMap_mem_lev X Γ' c, fun s hs => by rw [gal_algebraMap, hc s hs]⟩

theorem jK_mem_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : X.jK ∈ mdl X Γ' S := (mem_mdl_iff X Γ' S _).2 ⟨jK_mem_lev X Γ', fun s _ => gal_jK X s⟩

theorem coe_jRat_X (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : ((jRat X Γ' RatFunc.X : lev X Γ') : X.K) = X.jK := by
  rw [← RatFunc.algebraMap_X, jRat_algebraMap, coe_jPoly, Polynomial.aeval_X]

def algConst (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra Ω (lev X Γ') := (levConst X Γ').toAlgebra

def algPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra (Polynomial Ω) (lev X Γ') := (jPoly X Γ').toAlgebra

def algRat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra (RatFunc Ω) (lev X Γ') := (jRat X Γ').toAlgebra

def algMdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Algebra (mdl X Γ' S) (lev X Γ') :=
  (Subfield.inclusion (mdl_le_lev X Γ' S)).toAlgebra

section Instances

attribute [local instance] algConst algPoly algRat algMdl

theorem isScalarTower_poly_rat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    IsScalarTower (Polynomial Ω) (RatFunc Ω) (lev X Γ') := IsScalarTower.of_algebraMap_eq fun P => (jRat_algebraMap X Γ' P).symm

theorem isScalarTower_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
    IsScalarTower (mdl X Γ' S) (lev X Γ') X.K := IsScalarTower.of_algebraMap_eq fun _ => rfl

end Instances

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.RepL
section
noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) ℤ

def slz (k : ℕ) (δ : M2) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ((δ.det : ℤ) : ℂ) ^ (k - 1) * ((((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ)) ^ k)⁻¹ *
    f (ofComplex ((((δ 0 0 : ℤ) : ℂ) * τ + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * τ + ((δ 1 1 : ℤ) : ℂ))))

def LRep (L : ℕ) (Δ : Set M2) {ι : Type} (β : ι → M2) : Prop :=
  Set.BijOn (fun p : Gamma0 L × ι => ((p.1 : SL(2, ℤ)) : M2) * β p.2) Set.univ Δ

def RRep (L : ℕ) (Δ : Set M2) {κ : Type} (α : κ → M2) : Prop :=
  Set.BijOn (fun p : κ × Gamma0 L => α p.1 * ((p.2 : SL(2, ℤ)) : M2)) Set.univ Δ

def hsum (k : ℕ) (ε : ℤ → ℂ) {ι : Type} [Fintype ι] (β : ι → M2) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ∑ i, ε (β i 0 0) * slz k (β i) f τ

def DT (L q : ℕ) : Set M2 := {δ | δ.det = q ∧ (L : ℤ) ∣ δ 1 0}

def DU (L l : ℕ) : Set M2 := {δ | δ.det = l ∧ (L : ℤ) ∣ δ 1 0 ∧ ¬ (l : ℤ) ∣ δ 0 0}

def repU (q : ℕ) (j : Fin q) : M2 := !![1, (j : ℕ); 0, q]

def repT (q : ℕ) : Option (Fin q) → M2
  | some j => repU q j
  | none => !![q, 0; 0, 1]

def repL (L q : ℕ) : Option (Fin q) → M2
  | some j => !![q, 0; L * (j : ℕ), 1]
  | none => !![1, 0; 0, q]

def Mod (F : ℍ → ℂ) : Prop := ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ‖F τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)

def latF (L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) : ℤ × ℤ → ℂ := fun x => if (L : ℤ) ∣ x.1 then b (x.1 / L) * φ (x.2 : ZMod L) else 0

def Kills (L : ℕ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) : Prop := ∀ x, ∑ r ∈ Finset.range L, Φ (x - (r : ℤ) • v) = 0

def strip : Set ℍ := {τ | 0 ≤ τ.re ∧ τ.re < 1}

end GlobalTheory.EisM

end
end

