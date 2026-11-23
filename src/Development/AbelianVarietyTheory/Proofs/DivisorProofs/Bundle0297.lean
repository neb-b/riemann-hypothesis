module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicProperties
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section
namespace GlobalTheory.KSp.ScBasic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E]

end GlobalTheory.KSp.ScBasic
end

namespace GlobalTheory.KSp

open MeasureTheory Matrix in
private theorem sc_units_eq_mul_nabs_norm_rpow {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : Eˣ) :
    _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) *
      ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := by
  simp [_root_.GlobalTheory.KSp.sc, z.ne_zero]

open MeasureTheory Matrix in
private theorem rpow_natCast_div_two_sq {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x ^ ((m : ℝ) / 2)) ^ 2 = x ^ m := by
  rw [← Real.rpow_natCast (x ^ ((m : ℝ) / 2)) 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x m]
  congr 1
  push_cast
  ring

open MeasureTheory Matrix in
private theorem sc_zero' {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) : _root_.GlobalTheory.KSp.sc F χ m 0 = 0 := by
  simp [_root_.GlobalTheory.KSp.sc]

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.KSp.sc_basic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : _root_.GlobalTheory.WeilM.ResEtaPow (R := F) ⊥ χ m), _root_.GlobalTheory.KSp.sc F χ m 1 = 1 ∧ (∀ z z' : E, _root_.GlobalTheory.KSp.sc F χ m (z * z') = _root_.GlobalTheory.KSp.sc F χ m z * _root_.GlobalTheory.KSp.sc F χ m z') ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖_root_.GlobalTheory.KSp.sc F χ m (z : E)‖ ^ 2 = _root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (c (z : E))⁻¹ * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = _root_.GlobalTheory.KSp.sc F χ m (z : E)) ∧ (∀ t : Fˣ, _root_.GlobalTheory.KSp.sc F χ m (algebraMap F E t) = (_root_.GlobalTheory.KSp.sgn E t * (_root_.GlobalTheory.SplitWeil.nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m ((z : E) * c (z : E)) = ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hinj := hE.algebraMap_injective
  have hinv := hE.invol
  have hpos : ∀ t : Fˣ, 0 < _root_.GlobalTheory.SplitWeil.nabs F t :=
    _root_.GlobalTheory.SplitWeil.nabs_pos F
  have hmul := _root_.GlobalTheory.SplitWeil.nabs_mul F
  have hunit : ∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) *
      ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := fun z => sc_units_eq_mul_nabs_norm_rpow F χ m z
  have hnorm : ∀ z : Eˣ, algebraMap F E ((Units.map (Algebra.norm F : E →* F) z : Fˣ) : F) =
      (z : E) * c z := fun z => by
    simpa using hE.algebraMap_norm (z : E)
  have hNc : ∀ z : Eˣ, Units.map (Algebra.norm F : E →* F) (Units.map (c : E →* E) z) =
      Units.map (Algebra.norm F : E →* F) z := by
    intro z
    apply Units.ext
    apply hinj
    rw [hnorm, hnorm]
    simp [hinv, mul_comm]
  have hNa : ∀ t : Fˣ, Units.map (Algebra.norm F : E →* F) (Units.map (algebraMap F E : F →* E) t)
      = t * t := by
    intro t
    apply Units.ext
    apply hinj
    rw [hnorm]
    simp
  have hbase : ∀ t : Fˣ, _root_.GlobalTheory.KSp.sc F χ m (algebraMap F E t) =
      (_root_.GlobalTheory.KSp.sgn E t * (_root_.GlobalTheory.SplitWeil.nabs F t : ℝ)) ^ m := by
    intro t
    have h1 := hunit (Units.map (algebraMap F E : F →* E) t)
    simp only [Units.coe_map, MonoidHom.coe_coe] at h1
    rw [h1, hχ t, hNa, hmul, Real.mul_rpow (hpos t).le (hpos t).le, ← sq,
      rpow_natCast_div_two_sq (hpos t) m, mul_pow]
    simp only [_root_.GlobalTheory.KSp.sgn, bot_sup_eq]
    split_ifs with h₁ h₂ h₂ <;>
      first
        | (push_cast; ring1)
        | exact absurd (Subgroup.mem_sup_right h₂) h₁
        | exact absurd (by rwa [bot_sup_eq] at h₁) h₂
  refine ⟨?_, ?_, hunit, ?_, ?_, hbase, ?_⟩
  · simpa [_root_.GlobalTheory.SplitWeil.nabs_one] using hunit 1
  · intro z z'
    rcases eq_or_ne z 0 with rfl | hz
    · simp [sc_zero']
    rcases eq_or_ne z' 0 with rfl | hz'
    · simp [sc_zero']
    obtain ⟨u, rfl⟩ : ∃ u : Eˣ, (u : E) = z := ⟨Units.mk0 z hz, rfl⟩
    obtain ⟨u', rfl⟩ : ∃ u : Eˣ, (u : E) = z' := ⟨Units.mk0 z' hz', rfl⟩
    rw [← Units.val_mul, hunit, hunit, hunit, map_mul, map_mul, hmul,
      Real.mul_rpow (hpos _).le (hpos _).le]
    push_cast [Circle.coe_mul]
    ring
  · intro z
    rw [hunit, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (hpos _).le _), rpow_natCast_div_two_sq (hpos _) m]
  · intro z
    have h1 := hunit (Units.map (c : E →* E) z)⁻¹
    simp only [Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, map_inv] at h1
    have hs := hpos (Units.map (Algebra.norm F : E →* F) z)
    have habs_inv : ∀ t : Fˣ, _root_.GlobalTheory.SplitWeil.nabs F t⁻¹ =
        (_root_.GlobalTheory.SplitWeil.nabs F t)⁻¹ := fun t =>
      eq_inv_of_mul_eq_one_left (by rw [← hmul, inv_mul_cancel, _root_.GlobalTheory.SplitWeil.nabs_one])
    rw [h1, hNc, hunit,
      _root_.GlobalTheory.WeilM.ResEtaPow.map_conj (c := c) hE hχ z, inv_inv,
      habs_inv, Real.inv_rpow hs.le, ← rpow_natCast_div_two_sq hs m]
    have ha0 : ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hs _).ne'
    push_cast at ha0 ⊢
    field_simp
  · intro z
    have hz : Units.map (Algebra.norm F : E →* F) z ∈ (Units.map (Algebra.norm F : E →* F)).range :=
      ⟨z, rfl⟩
    rw [← hnorm, hbase]
    simp [_root_.GlobalTheory.KSp.sgn, hz]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassDivisionValueQExpansion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpansionB

theorem val_div_ne_int (N : ℕ) [NeZero N] (j : ZMod N) (hj : j ≠ 0) (n : ℤ) :
    ((j.val : ℂ)) / N ≠ n := by
  intro h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [div_eq_iff hN] at h
  have h' : (j.val : ℤ) = n * (N : ℤ) := by exact_mod_cast h
  apply hj
  have h2 := congrArg (Int.cast : ℤ → ZMod N) h'
  simpa using h2

theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  classical
  intro N _ x hx
  rw [hasQ_iff]
  intro τ
  obtain ⟨T, hT, hS⟩ := _root_.GlobalTheory.WpFam.RowsSummed.main N 1 τ x _ le_rfl (GlobalTheory.T.G2_add_weierstrassP_row_sum τ (tors N τ x))
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hT' : HasSum (fun k : ℕ => cSum N 1 1 x k *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T := by
    simpa using hT
  set c : ℂ := (if x 0 = 0 then ch N (x 1) / (1 - ch N (x 1)) ^ 2 else 0) with hcdef
  have hval : wB N x τ = T + c := by
    rw [wB_eq, hS, div_eq_iff (pow_ne_zero 2 hc), hcdef]
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have him : (((x 1).val : ℂ) / N).im = 0 := by
        have : (((x 1).val : ℂ) / N) = ((((x 1).val : ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.ofReal_im]
      have hr := (_root_.GlobalTheory.WpFam.RowReal.row_real _ him (val_div_ne_int N (x 1) h1)).1
      have hch : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((x 1).val : ℂ) / N)) = ch N (x 1) := by
        rw [ch, mul_div_assoc]
      rw [hch] at hr
      rw [if_pos h0, if_pos h0]
      have e2 : (1 + 1 : ℕ) = 2 := rfl
      rw [e2, hr]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
    · rw [if_neg h0, if_neg h0]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
  rw [hval]
  have hs : HasSum (fun k : ℕ => if k = 0 then c else 0) c := hasSum_ite_eq 0 c
  convert hT'.add hs using 2 with k
  by_cases hk : k = 0
  · subst hk
    simp [cB, cSum, hcdef]
  · simp [cB, hk]

end GlobalTheory.WpFam.ExpansionB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorBaseChangeTransportPoint
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginCut

theorem torsor_baseChange_point :
    ∀ (A A₁ R R₁ : Type) [CommRing A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R]
    [CommRing R₁] [Algebra A₁ R₁] (j : A →+* A₁) (γ : R →+* R₁) (ρ : R →+* A) (ρ₁ : R₁ →+* A₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ →
    ρ₁.comp (algebraMap A₁ R₁) = RingHom.id A₁ →
    ρ₁.comp γ = j.comp ρ →
    ∀ (q : ℕ), 0 < q → ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q actA →
    ∃ (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ R₁] DA₁)) (h : DA →+* DA₁),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁ q actA₁ ∧
      h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁).comp β ∧
      ∀ σ : DA →+* FractionRing A₁,
        (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
          (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
        ∃ σ₁ : DA₁ →+* FractionRing A₁,
          (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
            (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  intro A A₁ R R₁ _ _ _ _ _ _ _ j γ ρ ρ₁ β hβ hret hργ q hq DA _ _ actA hT
  letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) := β.toAlgebra
  obtain ⟨act', -, hT'⟩ := GlobalTheory.LocAcyc.isZModTorsor_baseChange (GlobalTheory.LocAcyc.GenFib A R)
    (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA q hq actA hT

  let M₁ := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)
  let f : R₁ →+* FractionRing A₁ := (algebraMap A₁ (FractionRing A₁)).comp ρ₁
  have hf : ∀ m : M₁, IsUnit (f m) := by
    rintro ⟨m, hm⟩
    obtain ⟨a, ha, rfl⟩ := hm
    have : ρ₁ (algebraMap A₁ R₁ a) = a := by
      simpa using congrArg (fun φ : A₁ →+* A₁ => φ a) hret
    simp only [f, RingHom.comp_apply, this]
    exact IsLocalization.map_units (FractionRing A₁) (⟨a, ha⟩ : nonZeroDivisors A₁)
  let ρK : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* FractionRing A₁ :=
    IsLocalization.lift (M := M₁) (S := GlobalTheory.LocAcyc.GenFib A₁ R₁) hf
  have hρK : ρK.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = f :=
    IsLocalization.lift_comp hf
  refine ⟨TensorProduct (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA, inferInstance,
    inferInstance, act', Algebra.TensorProduct.includeRight.toRingHom, hT', ?_, ?_⟩
  · ext b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  · intro σ hσ
    have hagree : ρK.comp β = σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) := by
      apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
      rw [hσ, RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hρK, ← hργ]
      rfl
    letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (FractionRing A₁) := (ρK.comp β).toAlgebra
    let fA : GlobalTheory.LocAcyc.GenFib A₁ R₁ →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { ρK with commutes' := fun _ => rfl }
    let gA : DA →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { σ with commutes' := fun b => (congrArg (fun φ => φ b) hagree).symm }
    refine ⟨(Algebra.TensorProduct.productMap fA gA).toRingHom, ?_⟩
    ext r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one,
      mul_one]
    show ρK (algebraMap R₁ _ r) = _
    rw [← RingHom.comp_apply ρK, hρK]
    rfl

end GlobalTheory.KeyOriginCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
section
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorsorFieldPoint


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor (B D : Type) [CommRing B] [CommRing D]
    [Algebra B D] (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act) : Algebra.FormallyUnramified B D := by
  obtain ⟨-, -, hff, hbij⟩ := h
  haveI : NeZero q := ⟨hq.ne'⟩
  let g : D →ₐ[B] (Multiplicative (ZMod q) → D) :=
    Pi.algHom B (fun _ ↦ D) fun σ ↦ (act σ : D →ₐ[B] D)
  let F : D ⊗[B] D →ₐ[D] (Multiplicative (ZMod q) → D) :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId D _) g
  have hF : (F : D ⊗[B] D → _) = Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ ↦ D) fun _ ↦ AlgHom.id B D) g := by
    ext x : 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp_all
  have hFb : Function.Bijective F := by rw [hF]; exact hbij
  haveI : Algebra.FormallyUnramified D (Multiplicative (ZMod q) → D) :=
    (Algebra.FormallyUnramified.pi_iff _).2 fun _ ↦ inferInstance
  haveI : Algebra.FormallyUnramified D (D ⊗[B] D) :=
    Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofBijective F hFb).symm
  exact Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat D


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.TorsorFieldPoint.exists_point_finite_separable : ∀ (B K : Type) [CommRing B] [Field K]
    (f : B →+* K) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L)
      (σ : D →+* L), σ.comp (algebraMap B D) = (algebraMap K L).comp f := by
  intro B K _ _ f D _ _ q hq act h
  haveI := _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor B D q hq act h
  obtain ⟨hfin, -, hff, -⟩ := h
  letI : Algebra B K := f.toAlgebra
  haveI : Nontrivial (K ⊗[B] D) := Module.FaithfullyFlat.rTensor_nontrivial B D K
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[B] D)
  letI : Field (K ⊗[B] D ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (K ⊗[B] D ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.FormallyUnramified K (K ⊗[B] D ⧸ m) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective
  refine ⟨K ⊗[B] D ⧸ m, inferInstance, inferInstance, inferInstance,
    Algebra.FormallyUnramified.isSeparable K _,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext b
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.algebraMap_eq]
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rfl

end GlobalTheory.TorsorFieldPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorFieldEqProdGaloisStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_field_eq_prod_galois : ∀ (K M : Type) [Field K] [CommRing M] [Algebra K M] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)), 0 < q →
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)),
      (∀ i, FiniteDimensional K (L i)) ∧ (∀ i, IsGalois K (L i)) ∧
      (∀ i, Module.finrank K (L i) ∣ q) ∧ Nonempty (M ≃ₐ[K] ∀ i, L i) := by
  first | (exact @GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (exact GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois) | (intros; apply GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois  <;> assumption)
end

