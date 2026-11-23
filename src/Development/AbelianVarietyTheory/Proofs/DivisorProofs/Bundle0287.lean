module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingAlgebraicProperties
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section
namespace GlobalTheory.KSp

section PairAlg

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem pr_eq_trace (Q : Matrix α α E) (x y : Matrix α ν E) :
    pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  have h : fromCols x (0 : Matrix α ν E) * stdJ ν E * ((fromCols (0 : Matrix α ν E) y).map c)ᵀ = x * (y.map c)ᵀ := by
    ext i k
    simp [stdJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [pr, form, hTens_eq, h]
  congr 2
  simp only [Matrix.trace, diag, Matrix.mul_apply, transpose_apply]
  rw [Finset.sum_comm]

theorem trace_single_pair (Q : Matrix α α E) (y : Matrix α ν E) (i : α) (j : ν) (z : E) :
    Matrix.trace (Qᵀ * (Matrix.single i j z * (y.map c)ᵀ)) = z * (Q * y.map c) i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Finset.mul_sum, ite_and]
  refine Finset.sum_congr rfl fun _ _ => by ring

def prLin (Q : Matrix α α E) : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))))
    (fun x x' y => by simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])
    (fun x y y' => by
      rw [show (y + y').map c = y.map c + y'.map c from Matrix.map_add _ (map_add c) _ _]
      simp [Matrix.add_mul, Matrix.mul_add, mul_add])
    (fun t x y => by
      rw [show (t • y).map c = t • y.map c from by ext i j; simp [map_smul]]
      simp [Matrix.smul_mul, Matrix.mul_smul, mul_left_comm])

end PairAlg

end GlobalTheory.KSp

namespace GlobalTheory.KSp

theorem pr_alg : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν]
    (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F,
      (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧
      (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧
      ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q hQ
  have hc : ∀ z, c (c z) = z := hE.invol
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  have hap : ∀ x y : Matrix α ν E, prLin c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) :=
    fun _ _ => rfl
  refine ⟨prLin c Q, fun x y => by rw [hap, pr_eq_trace], fun x y => ?_, fun y hy => ?_, fun x y a => ?_, hap⟩
  ·
    have h : Matrix.trace (Qᵀ * (y * (x.map c)ᵀ)) = c (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.trace, diag, Matrix.mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc, hQ.1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [hap, hap, h, ht]
  ·
    obtain ⟨bE, -, -⟩ := hE.basis
    haveI : Module.Finite F E := Module.Finite.of_basis bE
    have htr : Algebra.trace F E 1 ≠ 0 := by
      rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hw : Q * y.map c = 0 := by
      ext i j
      by_contra hij
      apply htr
      have := hy (Matrix.single i j ((Q * y.map c) i j)⁻¹)
      rw [hap, trace_single_pair, inv_mul_cancel₀ hij] at this
      simpa using this
    have hy0 : y.map c = 0 := by
      have := congrArg (fun m => Q⁻¹ * m) hw
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ.2] using this
    ext i j
    exact c.toRingHom.injective (by simpa using congrFun (congrFun hy0 i) j)
  ·
    have h : ((y * (a.map c)ᵀ).map c)ᵀ = a * (y.map c)ᵀ := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mul_apply, map_sum, hc, mul_comm]
    rw [hap, hap, h, Matrix.mul_assoc]

end GlobalTheory.KSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixColumnPairingDiagonalNorm
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem pr_eq_half_trace_mat (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (x y : Matrix α ν E) :
  pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  simp only [pr, form, GlobalTheory.WeilM.hTens, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, stdJ, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Pi.zero_apply, Matrix.zero_apply, map_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, one_apply, Matrix.trace, Matrix.mul_apply, transpose_apply, map_apply, diag_apply]
  congr 2
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.one_apply, mul_ite, ite_mul, mul_comm, mul_left_comm, mul_assoc]

theorem pr_diag_norm : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E) (D' : α → F) (a : Matrix ν ν E) (D : ν → F), Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E, 2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j, (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q _ u D' a D hQu x
  have hc : ∀ z, c (c z) = z := hE.invol
  have hmm : ∀ {m n : Type} (M : Matrix m n E), (M.map c).map c = M := fun M => by ext i j; simp [hc]
  have hd : ∀ {m : Type} [Fintype m] [DecidableEq m] (d : m → F),
      (diagonal (fun i => algebraMap F E (d i))).map c = diagonal (fun i => algebraMap F E (d i)) := by
    intro m _ _ d; ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
  set dD' := diagonal (fun i => algebraMap F E (D' i))
  set dD := diagonal (fun j => algebraMap F E (D j))
  set Y := uᵀ * x * a with hY
  have hQT : Qᵀ = u.map c * dD' * uᵀ := by
    rw [hQu, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have hbs : ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ = a * dD * (a.map c)ᵀ * (x.map c)ᵀ := by
    rw [Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul,
      transpose_mul, hd, diagonal_transpose, transpose_map, hmm, ← transpose_map, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rfl
  have hYs : (Y.map c)ᵀ = (a.map c)ᵀ * (x.map c)ᵀ * u.map c := by
    rw [hY, Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul, transpose_map,
      transpose_transpose]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (Qᵀ * (x * ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ)) = Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) := by
    rw [hQT, hbs, hYs, hY]
    rw [show u.map c * dD' * uᵀ * (x * (a * dD * (a.map c)ᵀ * (x.map c)ᵀ)) =
      u.map c * (dD' * uᵀ * x * a * dD * (a.map c)ᵀ * (x.map c)ᵀ) by simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) =
      algebraMap F E (∑ i, ∑ j, D' i * D j * Algebra.norm F (Y i j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, diag_apply, Matrix.mul_apply, dD', dD, diagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, transpose_apply, map_apply,
      map_sum, map_mul, hE.algebraMap_norm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨b, -, -⟩ := hE.basis
  haveI : Module.Free F E := Module.Free.of_basis b
  haveI : Module.Finite F E := Module.Finite.of_basis b
  have hfin : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [pr_eq_half_trace_mat, htr, hsum, Algebra.trace_algebraMap, hfin, nsmul_eq_mul, Nat.cast_ofNat,
    inv_mul_cancel_left₀ (two_ne_zero : (2 : F) ≠ 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicFiniteVolumeIntegralBound
section
open IsLocalRing Polynomial

namespace GlobalTheory.GenFibBaseChange

theorem exists_genFib_maps : ∀ (T O A A₁ R R₁ : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R] [CommRing R₁] [Algebra A₁ R₁]
    (j : A →+* A₁) (i₁ : A₁ →+* T), Function.Injective j → Function.Injective i₁ →
    ∀ (jA : R →+* O) (jA₁ : R₁ →+* O) (γ : R →+* R₁)
      (ψA : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib T O),
    jA₁.comp (algebraMap A₁ R₁) = (algebraMap T O).comp i₁ →
    γ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp j →
    jA₁.comp γ = jA →
    ψA.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∃ (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O)
      (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
      ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ ∧
      ψA₁.comp β = ψA ∧
      β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := by
  intro T O A A₁ R R₁ _ _ _ _ _ _ _ _ _ _ _ _ j i₁ hj hi₁ jA jA₁ γ ψA h1 h2 h3 h4
  have hu1 : ∀ y : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁),
      IsUnit (((algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : i₁ a ∈ nonZeroDivisors T := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hi₁ (by simpa using h)))
    have e : jA₁ (algebraMap A₁ R₁ a) = algebraMap T O (i₁ a) := by
      simpa using congrArg (fun f => f a) h1
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T O)
      (⟨algebraMap T O (i₁ a), ⟨i₁ a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
  have hu2 : ∀ y : Algebra.algebraMapSubmonoid R (nonZeroDivisors A),
      IsUnit (((algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ) y) := by
    rintro ⟨y, a, ha, rfl⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hi : j a ∈ nonZeroDivisors A₁ := mem_nonZeroDivisors_of_ne_zero (fun h => ha0 (hj (by simpa using h)))
    have e : γ (algebraMap A R a) = algebraMap A₁ R₁ (j a) := by
      simpa using congrArg (fun f => f a) h2
    simp only [RingHom.coe_comp, Function.comp_apply, e]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ R₁)
      (⟨algebraMap A₁ R₁ (j a), ⟨j a, hi, rfl⟩⟩ : Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  let ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)) hu1
  let β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁ :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) hu2
  have k1 : ψA₁.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA₁ := IsLocalization.lift_comp hu1
  have k3 : β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ := IsLocalization.lift_comp hu2
  refine ⟨ψA₁, β, k1, ?_, k3⟩
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  rw [RingHom.comp_assoc, k3, ← RingHom.comp_assoc, k1, RingHom.comp_assoc, h3, h4]

end GlobalTheory.GenFibBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZero
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem inCell_iff_det_ne_zero : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)),
    InCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0 := by
  intro F _ _ E _ _ c δ hE ν _ _ g
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    have hdet : ∀ x : UG c (stdJ ν E), (mat c x).det ≠ 0 := fun x =>
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit (x : GL (ν ⊕ ν) E))).ne_zero
    have hp0 : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0 (mat c p).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hp, fromBlocks_toBlocks]
    have hq0 : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0 (mat c q).toBlocks₂₂ := by
      rw [← (mem_sieg c).1 hq, fromBlocks_toBlocks]
    have hpd := hdet p
    have hqd := hdet q
    rw [hp0, det_fromBlocks_zero₂₁] at hpd
    rw [hq0, det_fromBlocks_zero₂₁] at hqd
    change (mat c p * stdJ ν E * mat c q).toBlocks₂₁.det ≠ 0
    rw [hp0, hq0]
    simp only [stdJ, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [det_neg, det_mul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (mul_ne_zero (right_ne_zero_of_mul hpd) (left_ne_zero_of_mul hqd))
  · intro hC
    set A := (mat c g).toBlocks₁₁ with hA
    set B := (mat c g).toBlocks₁₂ with hB
    set C := (mat c g).toBlocks₂₁ with hCdef
    set D := (mat c g).toBlocks₂₂ with hD
    have hg0 : mat c g = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    have hrel : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
    have hkey : C * (D.map c)ᵀ = D * (C.map c)ᵀ := by
      have h := congrArg Matrix.toBlocks₂₂ hrel
      rw [hg0] at h
      simp only [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
      simp at h
      exact (neg_add_eq_zero.1 h).symm
    have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 (isUnit_iff_ne_zero.2 hC)
    have hCs : IsUnit (C.map c)ᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, det_transpose]
      exact (hCu.map (RingHom.mapMatrix (c : E →+* E))).map detMonoidHom
    have hCC : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.2 hC)
    set v := C⁻¹ * D with hv
    have hvh : (v.map c)ᵀ = v := by
      apply hCu.mul_left_cancel
      apply hCs.mul_right_cancel
      have e1 : ((v.map c)ᵀ) * (C.map c)ᵀ = (D.map c)ᵀ := by
        rw [hv, Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← transpose_mul, ← Matrix.map_mul, hCC,
          Matrix.map_one _ (map_zero c) (map_one c), transpose_one, Matrix.mul_one]
      rw [Matrix.mul_assoc, e1, hkey, hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul]
    let q := unip c v hvh
    have hq : q ∈ sieg c ν := by
      change (fromBlocks (1 : Matrix ν ν E) v 0 1).toBlocks₂₁ = 0
      rw [toBlocks_fromBlocks₂₁]
    refine ⟨g * q⁻¹ * (weyl c ν)⁻¹, ?_, q, hq, by group⟩
    rw [mem_sieg]
    change (mat c g * fromBlocks 1 (-v) 0 1 * -stdJ ν E).toBlocks₂₁ = 0
    rw [hg0]
    simp only [stdJ, fromBlocks_neg, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simp
    rw [hv, ← Matrix.mul_assoc, hCC, Matrix.one_mul, neg_add_cancel]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTrans
section
open IsLocalRing

namespace GlobalTheory

theorem indEtale_localPieces_trans : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra S T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A) (_ : Algebra.Etale S A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[S] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R S T _ _ _ _ _ _ _ hS hT
  obtain ⟨κ, _, _, _, Tj, hmono, hcov, hpc⟩ := hT
  have hK : ∀ j, ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ)
      (V : μ → Subalgebra R T), Monotone V ∧ (∀ m, V m ≤ (Tj j).restrictScalars R) ∧
      (∀ x ∈ Tj j, ∃ m, x ∈ V m) ∧
      (∀ m, ∀ x ∈ V m, ∀ y ∈ Tj j, x * y = 1 → ∃ z ∈ V m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] V m)) := by
    intro j
    obtain ⟨B, _, _, _, Q, _, ⟨e⟩⟩ := hpc j
    exact _root_.GlobalTheory.localDecomp_indEtale R S T hS (Tj j) B Q ⟨e⟩
  choose μ pre dir ne V hVmono hVle hVcov hVloc hVee using hK
  let P : Subalgebra R T → Prop := fun W => ∃ (j : κ) (m : μ j), V j m = W
  have key : ∀ (j₁ : κ) (m₁ : μ j₁) (j : κ), j₁ ≤ j → ∃ m : μ j, V j₁ m₁ ≤ V j m := by
    intro j₁ m₁ j hj
    letI := pre j; haveI := dir j; haveI := ne j
    refine _root_.GlobalTheory.essEtaleLocal_le_of_directed R T ((Tj j).restrictScalars R) (μ j) (V j) (hVmono j) ?_ ?_ (V j₁ m₁) ?_
      (hVee j₁ m₁)
    · intro x hx; exact hVcov j x hx
    · intro m x hx y hy hxy; exact hVloc j m x hx y hy hxy
    · intro x hx
      have := hVle j₁ m₁ hx
      exact hmono hj this
  refine ⟨{W : Subalgebra R T // P W}, inferInstance, ⟨?_⟩, ?_, Subtype.val, fun a b h => h, ?_, ?_⟩
  · rintro ⟨W₁, j₁, m₁, rfl⟩ ⟨W₂, j₂, m₂, rfl⟩
    obtain ⟨j, h₁, h₂⟩ := directed_of (· ≤ ·) j₁ j₂
    obtain ⟨a, ha⟩ := key j₁ m₁ j h₁
    obtain ⟨b, hb⟩ := key j₂ m₂ j h₂
    letI := pre j; haveI := dir j
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
    exact ⟨⟨V j c, j, c, rfl⟩, ha.trans (hVmono j hac), hb.trans (hVmono j hbc)⟩
  · obtain ⟨j⟩ := (inferInstance : Nonempty κ)
    obtain ⟨m⟩ := ne j
    exact ⟨⟨V j m, j, m, rfl⟩⟩
  · intro t
    obtain ⟨j, hj⟩ := hcov t
    obtain ⟨m, hm⟩ := hVcov j t hj
    exact ⟨⟨V j m, j, m, rfl⟩, hm⟩
  · rintro ⟨W, j, m, rfl⟩
    exact hVee j m

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indScal_lift_law (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    (fun x => f x ⊗ₜ[ℂ] (1:ℂ)) ∈ indSpace (parab k (blocks a b))
      ((twist ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) (deltaHalf k (Two (Fin a) (Fin b)))).comp
        (leviProj k (blocks a b))) := by
  intro p x
  have h := hf.2 p x
  apply (TensorProduct.lid ℂ ℂ).injective
  simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, MonoidHom.coe_coe] at h ⊢
  rw [h]
  simp [parChar, detRep, ofChar_apply]
  ring

def indScalLift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
  ⟨⟨fun x => f x ⊗ₜ[ℂ] (1:ℂ), indScal_lift_law ν β a b hf⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((show IsOpen {g : GL (Fin (a + b)) k | rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f} from hf.1).mem_nhds (by simp)) fun g hg => by
      have hg' : rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f := hg
      apply Subtype.ext
      funext x
      show f (x * g) ⊗ₜ[ℂ] (1:ℂ) = f x ⊗ₜ[ℂ] (1:ℂ)
      rw [show f (x * g) = f x from congrFun hg' x])⟩

theorem indScal_lift_apply (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b)
    (x : GL (Fin (a + b)) k) : TensorProduct.lid ℂ ℂ ((indScalLift ν β a b hf).1.1 x) = f x := by
  simp [indScalLift]

def indScalVal (ν β : kˣ →* ℂˣ) (a b : ℕ) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] (GL (Fin (a + b)) k → ℂ) where
  toFun F x := TensorProduct.lid ℂ ℂ (F.1.1 x)
  map_add' F G := by
    funext x
    show TensorProduct.lid ℂ ℂ (F.1.1 x + G.1.1 x) = _
    rw [map_add (f := _)]
    rfl
  map_smul' c F := by
    funext x
    show TensorProduct.lid ℂ ℂ (c • F.1.1 x) = _
    rw [map_smul]
    rfl

theorem indScal_scal_lift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    indScalVal ν β a b (indScalLift ν β a b hf) = f :=
  funext (indScal_lift_apply ν β a b hf)

theorem indScal_irreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M := by
  intro H k _ _ _ _ a b ν β hνs hνu hβs hβu M hM hinv
  have hs : IsSmoothChar (ν * β) := hνs.mul hβs
  have hu : IsUnitaryChar (ν * β) := fun g => by simp [hνu g, hβu g]
  have h₁ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp a hs hu
  have h₂ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp b hβs hβu
  have hirr := H k a b ℂ ℂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β) h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
  let S : Subrepresentation (prod₂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β)) :=
    ⟨M.comap (indScalVal ν β a b), fun g F hF => hinv _ hF g⟩
  have hS : S.toSubmodule = M.comap (indScalVal ν β a b) := rfl
  have hmem : ∀ f (hf : f ∈ indScal ν β a b), f ∈ M ↔ indScalLift ν β a b hf ∈ S.toSubmodule := fun f hf => by
    rw [hS, Submodule.mem_comap, indScal_scal_lift]
  rcases hirr.eq_bot_or_eq_top S with h | h
  · left
    refine (Submodule.eq_bot_iff M).2 fun f hf => ?_
    have h' := (hmem f (hM hf)).1 hf
    rw [h] at h'
    have h0 : indScalLift ν β a b (hM hf) = 0 := (Submodule.mem_bot ℂ).1 h'
    rw [← indScal_scal_lift ν β a b (hM hf), h0, map_zero]
  · right
    intro f hf
    refine (hmem f hf).2 ?_
    rw [h]
    exact Submodule.mem_top

end GlobalTheory.RankFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureOverGenericFibreHartogsStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosureOverGenericFibre_hartogs : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (τ : D →ₗ[GlobalTheory.LocAcyc.GenFib A R] GlobalTheory.LocAcyc.GenFib A R),
      (∀ c ∈ GlobalTheory.KeyOriginNoeth.closure A R D, ∃ r : R, algebraMap R _ r = τ c) →
    ∀ (a₀ : A), a₀ ≠ 0 → ∀ (n : ℕ) (x y : Fin n → D),
      (∀ i, y i ∈ GlobalTheory.KeyOriginNoeth.closure A R D) →
      (∀ d : D, ∑ i, x i * algebraMap _ D (τ (y i * d)) =
        GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D;
    GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.ClosureHartogs.closure_hart) | (exact GlobalTheory.ClosureHartogs.closure_hart) | (intros; apply GlobalTheory.ClosureHartogs.closure_hart  <;> assumption)
end

