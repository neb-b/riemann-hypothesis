module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubOnePowEqPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionUpperTriangularAction
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.DlUp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem sub_coeff (ε : Ω →+* ℂ) {a b d : ℚ} (h : 0 < a / d) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε a b d φ).coeff s = eOm ε ((a / d)⁻¹ * s * b / d) * φ.coeff ((a / d)⁻¹ * s) := by
  have hs : s = (OrderIso.mulLeft₀ (a / d) h).toOrderEmbedding ((a / d)⁻¹ * s) := by
    show s = (a / d) * ((a / d)⁻¹ * s)
    rw [mul_inv_cancel_left₀ h.ne']
  unfold sub scale
  rw [dite_eq_left h]
  conv_lhs => rw [hs]
  rw [HahnSeries.embDomain_coeff]
  rfl

theorem theta_one (φ : HahnSeries ℚ Ω) : theta 1 φ = qD φ := by
  ext r
  simp [theta, qD, cm]

theorem mem_of_pow_eq_one (A : ValuationSubring Ω) {y : Ω} {k : ℕ} (hk : k ≠ 0) (hy : y ^ k = 1) : y ∈ A := by
  rw [← A.valuation_le_one_iff]
  by_contra hlt
  push_neg at hlt
  have h := one_lt_pow' hlt hk
  rw [← map_pow, hy, map_one] at h
  exact lt_irrefl _ h

theorem eOm_pow [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) : eOm ε x ^ x.den = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hy : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have h' : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x.num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * h'
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  haveI : NeZero x.den := ⟨x.den_nz⟩
  haveI : NeZero (x.den : Ω) := ⟨Nat.cast_ne_zero.2 x.den_nz⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic x.den Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos x.den Ω x.den_pos))
  have hζ : IsPrimitiveRoot z x.den := Polynomial.isRoot_cyclotomic_iff.1 hz
  have hεζ : IsPrimitiveRoot (ε z) x.den := hζ.map_of_injective ε.injective
  obtain ⟨i, -, hi⟩ := hεζ.eq_pow_of_pow_eq_one hy
  have hrange : ∃ w, ε w = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := ⟨z ^ i, by rw [map_pow, hi]⟩
  have hε : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := Function.invFun_eq hrange
  apply ε.injective
  rw [map_pow, hε, hy, map_one]

theorem eOm_unit [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (x : ℚ) :
    eOm ε x ≠ 0 ∧ eOm ε x ∈ A ∧ (eOm ε x)⁻¹ ∈ A := by
  have h := eOm_pow ε x
  refine ⟨fun h0 => ?_, mem_of_pow_eq_one A x.den_nz h, mem_of_pow_eq_one A x.den_nz (by rw [inv_pow, h, inv_one])⟩
  rw [h0, zero_pow x.den_nz] at h
  exact zero_ne_one h

theorem prim_sub [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) {a b d : ℚ} (h : 0 < a / d)
    {ψ : HahnSeries ℚ Ω} (hψ : Prim A ψ) : Prim A (sub ε a b d ψ) := by
  obtain ⟨h1, r, hr0, hr⟩ := hψ
  refine ⟨fun s => ?_, (a / d) * r, ?_, ?_⟩
  · rw [sub_coeff ε h]; exact mul_mem (eOm_unit ε A _).2.1 (h1 _)
  · rw [sub_coeff ε h, inv_mul_cancel_left₀ h.ne']; exact mul_ne_zero (eOm_unit ε A _).1 hr0
  · rw [sub_coeff ε h, inv_mul_cancel_left₀ h.ne', mul_inv]; exact mul_mem (eOm_unit ε A _).2.2 hr

theorem isDl_sl_upper : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ) (g : GQ), ent g 1 0 = 0 → 0 < ent g 0 0 → 0 < ent g 1 1 → algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) ∈ A →
  ∀ (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A l n 1 f φ →
    IsDl X A l n 1 (X.sl g f) (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ) := by
  intro Ω _ _ _ ε X A N l _ n g h10 ha hd hc f φ hdl
  obtain ⟨hφ, a₀, b₀, κ, hκ, hfb, hPa, hPb, hcg⟩ := hdl
  have hpos : 0 < ent g 0 0 / ent g 1 1 := div_pos ha hd
  have hexp : ∀ u, X.exp (X.sl g u) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp u) :=
    fun u => GlobalTheory.T.tower_exp_slash_upperTriangular_eq_subst Ω ε X g h10 u
  have hmul := _root_.GlobalTheory.CyclotomicQExpansion.sub_mul_and_one Ω ε (ent g 0 0) (ent g 0 1) (ent g 1 1) hpos
  have hqd := GlobalTheory.T.hahnSeriesQDerivative_substUpperTriangular Ω ε (ent g 0 0) (ent g 0 1) (ent g 1 1) hpos
  have hco := sub_coeff ε (b := ent g 0 1) hpos
  have hss : ∀ ψ χ : HahnSeries ℚ Ω, sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (ψ - χ) =
      sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) ψ - sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) χ := by
    intro ψ χ; ext s; simp [hco, mul_sub]
  simp only [theta_one] at hcg
  refine ⟨?_, X.sl g a₀, X.sl g b₀, κ, hκ, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hco, smul_eq_mul]
    exact mul_mem hc (mul_mem (eOm_unit ε A _).2.1 (hφ _))
  · rw [← map_mul, hfb, map_mul, AlgEquiv.commutes]
  · rw [hexp]; exact prim_sub ε A hpos hPa
  · rw [hexp]; exact prim_sub ε A hpos hPb
  · intro s
    simp only [theta_one]
    rw [hexp, hexp, hqd, hqd]
    have e1 : HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ *
        sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp a₀) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp b₀) =
        HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) *
          sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (φ * X.exp a₀ * X.exp b₀) := by
      rw [(hmul _ _).1, (hmul _ _).1]; ring
    have e2 : HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp a₀)) *
        sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp b₀) - sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp a₀) *
        (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp b₀))) =
        HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) *
          sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp a₀) * X.exp b₀ - X.exp a₀ * qD (X.exp b₀)) := by
      rw [hss, (hmul _ _).1, (hmul _ _).1]; ring
    rw [e1, e2]
    obtain ⟨z, hz, hzeq⟩ := hcg ((ent g 0 0 / ent g 1 1)⁻¹ * s)
    refine ⟨algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) *
      eOm ε ((ent g 0 0 / ent g 1 1)⁻¹ * s * ent g 0 1 / ent g 1 1) * z,
      mul_mem (mul_mem hc (eOm_unit ε A _).2.1) hz, ?_⟩
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul, hco, hco,
      smul_eq_mul, smul_eq_mul, ← mul_sub, ← mul_sub, hzeq]
    ring

end GlobalTheory.DlUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiag
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES


open GlobalTheory.KroneckerCongruence in
theorem kron_frob_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a →
    SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  intro Ω _ _ _ ε X q hq V s hs a ha r
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hε : Function.Injective ε := ε.injective
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hs.1)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs.2 x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs.2 x x.2).2.2
  set c := X.exp a with hc
  have hdq : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hA : (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a)).coeff r = c.coeff (r / q) := by
    have h := X.exp_upper (toGQ !![(q : ℤ), 0; 0, 1]) (by rw [ent_toGQ _ hdq]; simp) a (r / q)
    rw [ent_toGQ _ hdq, ent_toGQ _ hdq, ent_toGQ _ hdq] at h
    simp [eOm_zero hε, hq0] at h
    rw [← h]
  set B := X.exp (X.gal s.symm a) with hB
  have hBc : ∀ t, B.coeff t = s.symm (c.coeff t) := fun t => by rw [hB, X.gal_exp]
  have hBV : ∀ t, B.coeff t ∈ V := fun t => by rw [hBc]; exact (hs.2 _ (ha t)).2.1
  have hBq : X.exp ((X.gal s.symm a) ^ q) = hahnSeriesCoeffRingHomMap V.subtype (liftV V B hBV ^ q) := by
    rw [map_pow, map_pow, map_liftV]
  set y : V := (liftV V B hBV ^ q).coeff r with hy_def
  have hy : (X.exp ((X.gal s.symm a) ^ q)).coeff r = (y : Ω) := by rw [hBq, hahnSeriesCoeffRingHomMap_coeff]; rfl
  have hρy : ρ y = ρ ⟨c.coeff (r / q), ha _⟩ := by
    have h1 : ρ y = (hahnSeriesCoeffRingHomMap ρ (liftV V B hBV ^ q)).coeff r := by rw [hahnSeriesCoeffRingHomMap_coeff]
    rw [h1, map_pow, coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff]
    have h2 : (liftV V B hBV).coeff (r / q) = ⟨s.symm (c.coeff (r / q)), (hs.2 _ (ha _)).2.1⟩ :=
      Subtype.ext (hBc _)
    rw [h2, ← hfrob]
    congr 1
    apply Subtype.ext
    simp
  rw [map_sub, HahnSeries.coeff_sub, hA, hy]
  have hmem : c.coeff (r / q) - (y : Ω) = ((⟨c.coeff (r / q), ha _⟩ - y : V) : Ω) := rfl
  rw [hmem, ValuationSubring.mem_nonunits_iff, ← hρ0, map_sub, hρy, sub_self]

end GlobalTheory.KZ.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerRatioReducesToConstModValuation
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KronRatio

open GlobalTheory.KroneckerCongruence

variable {Ω : Type} [Field Ω]

theorem mem_of_isIntegral_int (V : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := Ω)).1 h
  rw [← hy]; exact y.2

theorem valuation_natCast_eq_one (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime)
    (hqV : ((q : ℕ) : Ω) ∈ V.nonunits) (hD : ¬ q ∣ D) : V.valuation (D : Ω) = 1 := by
  have hcop : IsCoprime (q : ℤ) (D : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 hD
  obtain ⟨a, b, hab⟩ := hcop
  have hle : ∀ n : ℤ, V.valuation (n : Ω) ≤ 1 := fun n => (V.valuation_le_one_iff _).2 (intCast_mem V n)
  have hq1 : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.1 hqV
  by_contra hne
  have hD1 : V.valuation (D : Ω) < 1 := lt_of_le_of_ne ((V.valuation_le_one_iff _).2 (natCast_mem V D)) hne
  have h1 : (1 : Ω) = (a : Ω) * (q : Ω) + (b : Ω) * (D : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hab
    push_cast at this
    exact this.symm
  have h2 : V.valuation (1 : Ω) < 1 := by
    rw [h1]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hq1
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hD1
  simp at h2

theorem mem_of_bdd (V : ValuationSubring Ω) {q D : ℕ} (hq : q.Prime) (hqV : ((q : ℕ) : Ω) ∈ V.nonunits)
    (hD : ¬ q ∣ D) {a : Ω} (h : ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * a)) : a ∈ V := by
  obtain ⟨k, hk⟩ := h
  have h1 := mem_of_isIntegral_int V hk
  have hv := valuation_natCast_eq_one V hq hqV hD
  rw [← V.valuation_le_one_iff] at h1 ⊢
  rwa [map_mul, map_pow, hv, one_pow, one_mul] at h1

theorem coeff_mul_mem (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V)
    (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V := by
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

theorem coeff_pow_mem (V : ValuationSubring Ω) (x : HahnSeries ℚ Ω) (hx : ∀ r, x.coeff r ∈ V) (n : ℕ)
    (r : ℚ) : (x ^ n).coeff r ∈ V := by
  have he : x ^ n = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx ^ n) := by
    rw [map_pow, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff]; exact (_ : V).2

theorem coeff_mul_mem_nonunits (V : ValuationSubring Ω) (x y : HahnSeries ℚ Ω)
    (hx : ∀ r, x.coeff r ∈ V.nonunits) (hy : ∀ r, y.coeff r ∈ V) (r : ℚ) : (x * y).coeff r ∈ V.nonunits := by
  have hx' : ∀ r, x.coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hx r)))
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ z : V, ρ z = 0 ↔ V.valuation (z : Ω) < 1 := fun z => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  have hX : hahnSeriesCoeffRingHomMap ρ (liftV V x hx') = 0 := by
    ext t
    rw [hahnSeriesCoeffRingHomMap_coeff]
    exact (hρ0 _).2 (V.mem_nonunits_iff.1 (hx t))
  have he : x * y = hahnSeriesCoeffRingHomMap V.subtype (liftV V x hx' * liftV V y hy) := by
    rw [map_mul, map_liftV, map_liftV]
  rw [he, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 ((liftV V x hx' * liftV V y hy).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, map_mul, hX, zero_mul]
  rfl

end GlobalTheory.KronRatio

namespace GlobalTheory.KZ


open GlobalTheory.KroneckerCongruence GlobalTheory.KronRatio in
theorem kronecker_ratio_reduces_to_const : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M : ℕ) (f : X.Kˣ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) → (∀ g : X.K, (∀ r, (X.exp g).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp g).coeff r ∈ V.nonunits) → W.valuation (g - algebraMap Ω X.K ((X.exp g).coeff 0)) < 1) → ∃ κ : Ω, κ ≠ 0 ∧ W.valuation (algebraMap Ω X.K κ * ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K)) / (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q) - 1) < 1 := by
  intro Ω _ _ _ ε X hε hj M f hM hf
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  let F : SL(2, ZMod M) → X.K := fun τ =>
    if h : ∃ σ, red σ = τ then X.sl (ofSL h.choose) (f : X.K) else (f : X.K)
  have hF : ∀ σ : SL(2, ℤ), X.sl (ofSL σ) (f : X.K) = F (red σ) := by
    intro σ
    have h : ∃ σ', red σ' = red σ := ⟨σ, rfl⟩
    have e : F (red σ) = X.sl (ofSL h.choose) (f : X.K) := dif_pos h
    have hσ' : red h.choose = red σ := h.choose_spec
    have hγ : σ * h.choose⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      have : σ * h.choose⁻¹ ∈ red.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ', mul_inv_cancel]
      exact this
    rw [e]
    calc X.sl (ofSL σ) (f : X.K) = X.sl (ofSL (σ * h.choose⁻¹ * h.choose)) (f : X.K) := by
          rw [inv_mul_cancel_right]
      _ = X.sl (ofSL h.choose) (X.sl (ofSL (σ * h.choose⁻¹)) (f : X.K)) := by rw [map_mul, X.sl_mul]
      _ = _ := by rw [hf _ hγ]
  choose D hD0 hD using X.bdd
  let P : X.K → Finset ℕ := fun g => (D g).primeFactors ∪ (D g⁻¹).primeFactors
  refine ⟨M.primeFactors ∪ P f ∪ Finset.univ.biUnion (fun τ => P (F τ)), ?_⟩
  intro q hq hqS V s hqV hs σ hσ W hW hdom
  have hn : ∀ h : X.K, q ∉ (D h).primeFactors → ∀ r, (X.exp h).coeff r ∈ V := fun h hh r =>
    mem_of_bdd V hq hqV (fun hd => hh (Nat.mem_primeFactors.2 ⟨hq, hd, (hD0 h).ne'⟩)) (hD h r)
  have hint : ∀ g : X.K, q ∉ P g → (∀ r, (X.exp g).coeff r ∈ V) ∧ (∀ r, (X.exp g⁻¹).coeff r ∈ V) := fun g hg =>
    ⟨hn g fun h => hg (Finset.mem_union_left _ h), hn _ fun h => hg (Finset.mem_union_right _ h)⟩
  have hqM : q ∉ M.primeFactors := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hqf : q ∉ P f := fun h => hqS (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hqF : q ∉ P (F (red σ)) := fun h =>
    hqS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  obtain ⟨hf1, hf2⟩ := hint _ hqf
  rw [← hF σ] at hqF
  obtain ⟨hs1, hs2⟩ := hint _ hqF
  have hcop : Nat.Coprime q M :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => hqM (Nat.mem_primeFactors.2 ⟨hq, hd, hM.ne'⟩)
  have hK := kronecker_congruence_tower ε X hε hj M q (f : X.K) hM hq hcop hf σ ⟨hσ.2.1, hσ.2.2⟩ V s hqV hs hf1 hs1
  refine ⟨1, one_ne_zero, ?_⟩
  generalize (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) *
    X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = A at hK ⊢
  have hB0 : X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).2 f.ne_zero)
      (pow_ne_zero _ ((map_ne_zero _).2 ((map_ne_zero _).2 f.ne_zero)))
  have hBinv : ∀ r, (X.exp (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q)⁻¹).coeff r ∈ V := by
    intro r
    rw [mul_inv, ← inv_pow, ← map_inv₀, ← map_inv₀ (X.gal s.symm), map_mul, map_pow]
    refine coeff_mul_mem V _ _ (fun t => ?_) (coeff_pow_mem V _ (fun t => ?_) q) r
    · rw [X.gal_exp]; exact (hs _ (hf2 t)).1
    · rw [X.gal_exp]; exact (hs _ (hs2 t)).2.1
  generalize X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q = B at hK hB0 hBinv ⊢
  have hge : algebraMap Ω X.K 1 * A / B - 1 = (A - B) * B⁻¹ := by
    rw [map_one, one_mul]; field_simp
  rw [hge]
  have hgc : ∀ r, (X.exp ((A - B) * B⁻¹)).coeff r ∈ V.nonunits := by
    intro r; rw [map_mul]; exact coeff_mul_mem_nonunits V _ _ hK hBinv r
  generalize (A - B) * B⁻¹ = g at hgc ⊢
  have hgV : ∀ r, (X.exp g).coeff r ∈ V := fun r =>
    (V.valuation_le_one_iff _).1 (le_of_lt (V.mem_nonunits_iff.1 (hgc r)))
  have h1 := hdom g hgV fun r _ => hgc r
  have hcV := V.mem_nonunits_iff.1 (hgc 0)
  have hcm := hgV 0
  generalize (X.exp g).coeff 0 = c at h1 hcV hcm
  have h2 : W.valuation (algebraMap Ω X.K c) < 1 := by
    by_cases hc0 : c = 0
    · rw [hc0, map_zero, map_zero]; exact zero_lt_one
    refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 ((hW c).2 hcm)) fun heq => ?_
    have hinv : algebraMap Ω X.K c⁻¹ ∈ W := by
      rw [← W.valuation_le_one_iff, map_inv₀, map_inv₀, heq, inv_one]
    have h3 : V.valuation c⁻¹ ≤ 1 := (V.valuation_le_one_iff _).2 ((hW _).1 hinv)
    have h4 : V.valuation (c⁻¹ * c) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' h3) hcV
    rw [inv_mul_cancel₀ hc0, map_one] at h4
    exact lt_irrefl _ h4
  have h5 := lt_of_le_of_lt (W.valuation.map_add _ _) (max_lt h1 h2)
  rwa [sub_add_cancel] at h5

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerAutomorphismMovesIntegersAlmostUnit
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kummer_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L] (σ : G), (∀ x ∈ F, σ • x = x) →
    ∀ ζ α : L, IsPrimitiveRoot ζ p → α ≠ 0 → α ^ p ∈ F → σ • α = ζ * α → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ σ hσ ζ α hζ hα hαp hσα r hr
  obtain ⟨t, hrt, ht1⟩ := exists_between hr
  have ht0 : 0 < t := lt_of_le_of_lt (zero_le') hrt
  set s : ℝ≥0 := t⁻¹ with hs_def
  have hs1 : 1 < s := by rw [hs_def]; exact one_lt_inv₀ ht0 |>.mpr ht1
  have hs0 : 0 < s := lt_trans zero_lt_one hs1
  have hrs : r * s < 1 := by
    rw [hs_def, ← div_eq_mul_inv]; exact (div_lt_one ht0).mpr hrt
  obtain ⟨y, hyF, hy⟩ := _root_.GlobalTheory.AlmostEt.kummer_approx_critical L v p hp F hF hp1 α hαp hp0 s hs1
  have hz := _root_.GlobalTheory.AlmostEt.valuation_sub_one_pow_eq_prime L v p hp ζ hζ
  have hp2 : 2 ≤ p := hp.two_le
  have hpn : p - 1 ≠ 0 := by omega
  set β := α - y with hβ_def
  have hσβ : σ • β - β = (ζ - 1) * α := by
    rw [hβ_def, smul_sub, hσα, hσ y hyF]; ring
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have hne : σ • β - β ≠ 0 := by
    rw [hσβ]; exact mul_ne_zero (sub_ne_zero.mpr hζ1) hα
  have hβ0 : β ≠ 0 := by
    intro h; apply hne; rw [h, smul_zero, sub_zero]

  have hvβ : v β ≤ s * v (σ • β - β) := by
    have h1 : v β ^ (p - 1) ≤ (s * v (σ • β - β)) ^ (p - 1) := by
      rw [hσβ, map_mul, mul_pow, mul_pow, hz]
      calc v β ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := hy
        _ ≤ s ^ (p - 1) * v (p : L) * v α ^ (p - 1) := by
          gcongr
          exact le_self_pow₀ hs1.le hpn
        _ = s ^ (p - 1) * (v (p : L) * v α ^ (p - 1)) := by ring
    exact le_of_pow_le_pow_left₀ hpn (zero_le') h1
  obtain ⟨d, hdF, hd0, hdlo, hdhi⟩ := _root_.GlobalTheory.AlmostEt.klc_scale L v p hp F hF hp0 hp1 (r * s) hrs β hβ0
  refine ⟨β * d ^ p, Subfield.mem_top _, hdhi, ?_⟩
  have hσx : σ • (β * d ^ p) - β * d ^ p = d ^ p * (σ • β - β) := by
    rw [smul_mul', smul_pow', hσ d hdF]; ring
  rw [hσx]
  have hvx : v (β * d ^ p) ≤ s * v (d ^ p * (σ • β - β)) := by
    rw [map_mul, map_mul]
    calc v β * v (d ^ p) ≤ s * v (σ • β - β) * v (d ^ p) := by gcongr
      _ = s * (v (d ^ p) * v (σ • β - β)) := by ring
  have : r * s < s * v (d ^ p * (σ • β - β)) := lt_of_lt_of_le hdlo hvx
  rw [mul_comm] at this
  exact lt_of_mul_lt_mul_left this (zero_le')

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCompletionNoPrimeTorsion
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem rootOfUnity_eq_pow {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K]
    (l : ℕ) (hl : 0 < l) (ζ : Kˣ) (hζ : ζ ^ l = 1) (m : ℕ) (hm : 0 < m) : ∃ η : Kˣ, ζ = η ^ m := by
  have : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hω' : IsPrimitiveRoot (algebraMap Ω K ω) l := hω.map_of_injective (algebraMap Ω K).injective
  have hζK : (ζ : K) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω'.eq_pow_of_pow_eq_one hζK
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ω ^ i) hm
  have hz0 : algebraMap Ω K z ≠ 0 := by
    intro h0
    have : (ζ : K) = 0 := by rw [← hi, ← map_pow, ← hz, map_pow, h0, zero_pow hm.ne']
    exact ζ.ne_zero this
  refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, map_pow, hi]

theorem khat_no_l_torsion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l), (l : ℤ_[l]) • x = 0 → x = 0 := by
  intro Ω _ _ _ ε X l _ x hx
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  suffices hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by
    apply AdicCompletion.ext
    intro n
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]
  intro n
  obtain ⟨hsurj, hker, hmul, hone, -, -, -⟩ := H3.cls_props Ω ε X l (n + 1)
  obtain ⟨-, hker0, -, hone0, -, -, hred⟩ := H3.cls_props Ω ε X l n
  obtain ⟨f, hf⟩ := hsurj (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x)
  have hpow : ∀ k : ℕ, X.cls l (n + 1) (f ^ k) = k • X.cls l (n + 1) f := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ f k, hmul, ih, succ_nsmul]
  have h1 : X.cls l (n + 1) (f ^ l) = X.cls l (n + 1) 1 := by
    rw [hpow, hone, hf, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← map_smul, hx, map_zero]
  obtain ⟨g, hg⟩ := (hker _ _).1 h1
  rw [one_mul] at hg
  set ζ : X.Kˣ := f * (g ^ (l ^ n))⁻¹ with hζdef
  have hζ : ζ ^ l = 1 := by
    rw [hζdef, mul_pow, hg, inv_pow, ← pow_mul, ← pow_succ, mul_inv_cancel]
  have : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨η, hη⟩ := rootOfUnity_eq_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)
  have hf' : f = 1 * (η * g) ^ (l ^ n) := by
    rw [one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]
  rw [hred x f hf.symm, ← hone0]
  exact (hker0 _ _).2 ⟨_, hf'⟩

end GlobalTheory.KZ.BettiB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariantStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_rootOfInvariant_T_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ), l.Prime → l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ∀ (u : X.K), u ≠ 0 → Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)) → (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) → ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) → X.sl (ofSL ModularGroup.T) u = u := by
  first | exact @GlobalTheory.TInv.sl_T_eq | exact GlobalTheory.TInv.sl_T_eq | (intros; apply GlobalTheory.TInv.sl_T_eq <;> assumption)
end

