module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdeleEquivOfLocal
section
open NumberField IsDedekindDomain TensorProduct

noncomputable section

namespace GlobalTheory.NormLevelCompare

section Adeles

open Rat.HeightOneSpectrum

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem padic_cast {p q : Nat.Primes} (h : p = q) :
    ∃ e : ℚ_[p] ≃ₐ[ℚ] ℚ_[q], ∀ x, e x ∈ PadicInt.subring q ↔ x ∈ PadicInt.subring p := by
  subst h
  exact ⟨AlgEquiv.refl, fun _ => Iff.rfl⟩

theorem padicEquiv_mem {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
    [IsDedekindDomain R] [IsFractionRing R ℚ] (v : HeightOneSpectrum R)
    (x : v.adicCompletion ℚ) :
    adicCompletion.padicEquiv v x ∈ PadicInt.subring (primesEquiv v) ↔
      x ∈ v.adicCompletionIntegers ℚ := by
  refine ⟨fun hx => ?_, fun hx => (adicCompletion.padicEquiv_bijOn v).mapsTo hx⟩
  obtain ⟨y, hy, hxy⟩ := (adicCompletion.padicEquiv_bijOn v).surjOn hx
  obtain rfl : y = x := (adicCompletion.padicEquiv v).injective hxy
  exact hy

def primeCorr : HeightOneSpectrum ℤ ≃ HeightOneSpectrum (𝓞 ℚ) :=
  (primesEquiv (R := ℤ)).trans (primesEquiv (R := 𝓞 ℚ)).symm

theorem exists_local (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃ₐ[ℚ] w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have h : primesEquiv (primeCorr w) = primesEquiv w := by simp [primeCorr]
  obtain ⟨c, hc⟩ := padic_cast h
  refine ⟨((adicCompletion.padicEquiv (primeCorr w)).toAlgEquiv.trans c).trans
    (adicCompletion.padicEquiv w).symm.toAlgEquiv, fun x => ?_⟩
  rw [← padicEquiv_mem w, ← padicEquiv_mem (primeCorr w), ← hc]
  change adicCompletion.padicEquiv w ((adicCompletion.padicEquiv w).symm _) ∈ _ ↔ _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  rfl

theorem exists_adele_equiv_of_local {R R' K : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing R'] [IsDedekindDomain R'] [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra R' K] [IsFractionRing R' K] (σ : HeightOneSpectrum R' ≃ HeightOneSpectrum R)
    (e : ∀ w, (σ w).adicCompletion K ≃ₐ[K] w.adicCompletion K)
    (he : ∀ w x, e w x ∈ w.adicCompletionIntegers K ↔ x ∈ (σ w).adicCompletionIntegers K) :
    ∃ e : FiniteAdeleRing R K ≃ₐ[K] FiniteAdeleRing R' K,
      ∀ a, (∀ w, e a w ∈ w.adicCompletionIntegers K) ↔
        ∀ v, a v ∈ v.adicCompletionIntegers K := by
  let φ : FiniteAdeleRing R K →ₐ[K] FiniteAdeleRing R' K :=
    { toFun := fun a => ⟨fun w => e w (a (σ w)), by
        have h1 := σ.injective.tendsto_cofinite.eventually a.2
        exact h1.mono fun w hw => (he w _).2 hw⟩
      map_one' := FiniteAdeleRing.ext _ fun w => map_one (e w)
      map_mul' := fun a b => FiniteAdeleRing.ext _ fun w => map_mul (e w) _ _
      map_zero' := FiniteAdeleRing.ext _ fun w => map_zero (e w)
      map_add' := fun a b => FiniteAdeleRing.ext _ fun w => map_add (e w) _ _
      commutes' := fun r => FiniteAdeleRing.ext _ fun w => (e w).commutes r }
  have hφ : ∀ a w, φ a w = e w (a (σ w)) := fun _ _ => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    refine FiniteAdeleRing.ext _ fun v => ?_
    obtain ⟨w, rfl⟩ := σ.surjective v
    apply (e w).injective
    rw [← hφ, ← hφ, hab]
  have hsurj : Function.Surjective φ := by
    intro b
    let f : ∀ v : HeightOneSpectrum R, v.adicCompletion K :=
      Equiv.piCongrLeft (fun v : HeightOneSpectrum R => v.adicCompletion K) σ
        (fun w => (e w).symm (b w))
    have hf : ∀ w, f (σ w) = (e w).symm (b w) := fun w =>
      Equiv.piCongrLeft_apply_apply _ _ _ _
    refine ⟨⟨f, ?_⟩, FiniteAdeleRing.ext _ fun w => ?_⟩
    · have h1 := σ.symm.injective.tendsto_cofinite.eventually b.2
      refine h1.mono fun v hv => ?_
      obtain ⟨w, rfl⟩ := σ.surjective v
      rw [Equiv.symm_apply_apply] at hv
      change f (σ w) ∈ (σ w).adicCompletionIntegers K
      rw [hf, ← he, AlgEquiv.apply_symm_apply]
      exact hv
    · change e w (f (σ w)) = _
      rw [hf, AlgEquiv.apply_symm_apply]
  refine ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun a => ?_⟩
  change (∀ w, φ a w ∈ w.adicCompletionIntegers K) ↔
    ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K
  rw [σ.surjective.forall]
  exact forall_congr' fun w => he w _

theorem exists_adele_equiv :
    ∃ e : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af ≃ₐ[ℚ] IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af,
      ∀ a, e a ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHat ↔ a ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat := by
  choose e he using exists_local
  exact exists_adele_equiv_of_local primeCorr e he

end Adeles

section Transport

variable {A A' : Type} [CommRing A] [Algebra ℚ A] [CommRing A'] [Algebra ℚ A'] (e : A ≃ₐ[ℚ] A')

variable {V V' : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']

end Transport

section Adelic

variable (e : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af ≃ₐ[ℚ] IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af)
  (he : ∀ a, e a ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHat ↔ a ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat)



section Ideles

variable {K : Type} [Field K] [NumberField K]




end Ideles

section Groups

variable {E : Type} [Field E] [NumberField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]


include he



variable [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

end Groups

end Adelic

section Hypotheses

variable {K : Type} [Field K] [NumberField K] {d : ℕ} {δ : K}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E]



variable {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]
  [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]





end Hypotheses

end GlobalTheory.NormLevelCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleIsUnitDetLocalInvolution
section
open Matrix

namespace GlobalTheory.LocalLift

def invEquiv {O : Type} [CommRing O] (c : O →+* O) (hc : ∀ x, c (c x) = x) : O ≃+* O :=
  { c with invFun := c, left_inv := hc, right_inv := hc }

noncomputable def resInv {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O) (hc : ∀ x, c (c x) = x) :
    IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O :=
  (IsLocalRing.ResidueField.mapEquiv (invEquiv c hc)).toRingHom

theorem resInv_residue {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O)
    (hc : ∀ x, c (c x) = x) (x : O) :
    resInv c hc (IsLocalRing.residue O x) = IsLocalRing.residue O (c x) := by
  simp only [resInv, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem lift_of_field
    (hF : ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
      ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
      ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
        Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
        ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  intro O _ _ c hc h2 n S hS hSc A B C D hdet hU
  set π := IsLocalRing.residue O with hπ
  set cb := resInv c hc with hcbdef
  have hcb : ∀ x, cb (π x) = π (c x) := resInv_residue c hc
  have hcbM : ∀ M : Matrix (Fin n) (Fin n) O, (M.map c).map π = (M.map π).map cb := by
    intro M; ext i j; simp [hcb]
  have hcbb : ∀ x, cb (cb x) = x := by
    intro x; obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    show cb (cb (π y)) = π y
    rw [hcb, hcb, hc]
  have h2k : (2 : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (h2.map π).ne_zero; rwa [map_ofNat] at this
  have hSk : IsUnit (S.map π).det := by
    have := hS.map π; rwa [RingHom.map_det] at this
  have hSck : (S.map π)ᵀ = -(S.map π).map cb := by
    rw [← hcbM, ← Matrix.transpose_map, hSc]; ext i j; simp
  have h11 : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply] at hU
    have := (Matrix.fromBlocks_inj.1 hU).1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero] at this
    rw [add_comm]; simpa [Matrix.mul_assoc] using this
  have hinj : ∀ u, (A.map π) *ᵥ u = 0 → (C.map π) *ᵥ u = 0 → u = 0 := by
    intro u hA hC
    have hd : ((fromBlocks A B C D).map π).det ≠ 0 := by
      have := (hdet.map π).ne_zero; rwa [RingHom.map_det] at this
    have := Matrix.eq_zero_of_mulVec_eq_zero hd (v := Sum.elim u 0) (by
      rw [fromBlocks_map, fromBlocks_mulVec]; ext (i | i) <;> simp [hA, hC])
    funext i; simpa using congrFun this (Sum.inl i)
  have hiso : (A.map π)ᵀ * S.map π * (C.map π).map cb + (C.map π)ᵀ * S.map π * (A.map π).map cb = 0 := by
    have : (Aᵀ * S * C.map c + Cᵀ * S * A.map c).map π = 0 := by rw [h11]; ext; simp
    rw [Matrix.map_add _ (map_add π), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, Matrix.transpose_map, hcbM, hcbM] at this
    exact this
  obtain ⟨Xb, hXadm, hXunit⟩ := hF cb hcbb h2k (S.map π) hSk hSck (A.map π) (C.map π) hinj hiso

  obtain ⟨X0, hX0⟩ : ∃ X0 : Matrix (Fin n) (Fin n) O, X0.map π = Xb :=
    ⟨Xb.map (fun x => (IsLocalRing.residue_surjective x).choose), by
      ext i j; exact (IsLocalRing.residue_surjective (Xb i j)).choose_spec⟩
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hch : c h = h := by
    have h' : c 2 * c h = 1 := by rw [← map_mul, hh, map_one]
    rw [map_ofNat] at h'
    calc c h = (h * 2) * c h := by rw [mul_comm h 2, hh, one_mul]
      _ = h * (2 * c h) := by ring
      _ = h := by rw [h', mul_one]
  set Z0 := X0ᵀ * S with hZ0
  set Z := h • (Z0 + (Z0.map c)ᵀ) with hZ
  have hZh : (Z.map c)ᵀ = Z := by
    ext i j; simp only [hZ, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, map_mul, map_add, hch, hc]; ring
  set X := (Z * S⁻¹)ᵀ with hX
  have hSt : (S.map c)ᵀ = -S := by
    have : S.map c = -Sᵀ := by rw [hSc, neg_neg]
    rw [this, Matrix.transpose_neg, Matrix.transpose_transpose]
  have hSinv : S * (S⁻¹.map c)ᵀ = -1 := by
    have h1 : (S⁻¹.map c) * (S.map c) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul S hS]; exact Matrix.map_one _ (map_zero c) (map_one c)
    have h2' := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one, hSt, Matrix.neg_mul] at h2'
    rw [← neg_neg (S * _), h2']
  have hXS : Xᵀ * S = Z := by
    rw [hX, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.nonsing_inv_mul S hS, Matrix.mul_one]
  have hXc : X.map c = (S⁻¹.map c)ᵀ * Z := by
    rw [hX, Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hZh]
  refine ⟨X, ?_, ?_⟩
  · rw [hXS, hXc, ← Matrix.mul_assoc, hSinv, Matrix.neg_mul, Matrix.one_mul, add_neg_cancel]
  · have hSbt : ((S.map π).map cb)ᵀ = -S.map π := by
      have : (S.map π).map cb = -(S.map π)ᵀ := by rw [hSck, neg_neg]
      rw [this, Matrix.transpose_neg, Matrix.transpose_transpose]
    have hZb : ((Xbᵀ * S.map π).map cb)ᵀ = Xbᵀ * S.map π := by
      rw [Matrix.map_mul, Matrix.transpose_mul, hSbt, ← Matrix.transpose_map, Matrix.transpose_transpose,
        Matrix.neg_mul]
      exact (eq_neg_of_add_eq_zero_left hXadm).symm
    have hZ0b : Z0.map π = Xbᵀ * S.map π := by
      rw [hZ0, Matrix.map_mul, Matrix.transpose_map, hX0]
    have hZm : Z.map π = π h • (Z0.map π + ((Z0.map c).map π)ᵀ) := by
      ext i j
      simp only [hZ, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
        smul_eq_mul, map_mul, map_add]
    have hZπ : Z.map π = Xbᵀ * S.map π := by
      have h2h : π h * 2 = 1 := by rw [← map_ofNat π 2, ← map_mul, mul_comm, hh, map_one]
      rw [hZm, hcbM, hZ0b, hZb, ← two_smul (IsLocalRing.ResidueField O) (Xbᵀ * S.map π), smul_smul, h2h,
        one_smul]
    have hXπ : X.map π = Xb := by
      have hmm : (X.map π)ᵀ * S.map π = (Xᵀ * S).map π := by
        ext i j
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul]
      have e : (X.map π)ᵀ * S.map π = Xbᵀ * S.map π := by
        calc (X.map π)ᵀ * S.map π = (Xᵀ * S).map π := hmm
          _ = Z.map π := by rw [hXS]
          _ = Xbᵀ * S.map π := hZπ
      have e' := congrArg (· * (S.map π)⁻¹) e
      simp only [Matrix.mul_nonsing_inv_cancel_right _ _ hSk] at e'
      exact Matrix.transpose_inj.1 e'
    apply isUnit_of_map_unit π
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add π), Matrix.map_mul, hXπ]
    exact hXunit

theorem exists_admissible_isUnit_det :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det :=
  lift_of_field _root_.GlobalTheory.lagrangian_transverse_field

end GlobalTheory.LocalLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticParamOfPrimitivesOnBox
section
open Set

namespace GlobalTheory

private lemma eq_of_fderiv_fibre_zero_convex {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {g : ℕ}
    (F : P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (hC : IsOpen C)
    (hCc : Convex ℝ C) (hF : AnalyticOnNhd ℂ F (Z ×ˢ C))
    (hd : ∀ a, ∀ p ∈ Z ×ˢ C, fderiv ℂ F p (0, Pi.single a 1) = 0)
    {z : P} (hz : z ∈ Z) {y y' : Fin g → ℂ} (hy : y ∈ C) (hy' : y' ∈ C) :
    F (z, y) = F (z, y') := by
  have hda : ∀ x ∈ C, HasFDerivAt (fun w => F (z, w))
      ((fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ))) x := by
    intro x hx
    exact (hF (z, x) ⟨hz, hx⟩).differentiableAt.hasFDerivAt.comp x (hasFDerivAt_prodMk_right z x)
  have hzero : ∀ x ∈ C,
      (fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ)) = 0 := by
    intro x hx
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.pi_ext
    intro a t
    have e : ((0 : P), (Pi.single a t : Fin g → ℂ)) = t • ((0 : P), (Pi.single a 1 : Fin g → ℂ)) := by
      refine Prod.ext (by simp) ?_
      funext j
      by_cases h : j = a
      · subst h; simp
      · simp [h]
    show fderiv ℂ F (z, x) ((0 : P), Pi.single a t) = 0
    rw [e, map_smul, hd a (z, x) ⟨hz, hx⟩, smul_zero]
  exact hCc.is_const_of_fderivWithin_eq_zero
    (fun x hx => (hda x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [fderivWithin_of_isOpen hC hx, (hda x hx).fderiv, hzero x hx]) hy hy'

theorem exists_analytic_param_of_primitives_on_box : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type} (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ) (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (G G' : K → P × (Fin g → ℂ) → ℂ), (∀ k, IsOpen (W k)) → IsOpen Z → IsOpen C → Convex ℝ C → C.Nonempty → (∀ p ∈ Z ×ˢ C, ∃ k, p ∈ W k) → ((∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) → ((∀ k, AnalyticOnNhd ℂ (G' k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G' k p - G' l p = c k l p) → ∃ h : P → ℂ, AnalyticOnNhd ℂ h Z ∧ ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → G k p = G' k p + h p.1 := by
  intro P _ _ _ g K W c ω Z C G G' hW hZ hC hCc hCn hcov hG hG'
  obtain ⟨hGa, hGd, hGc⟩ := hG
  obtain ⟨hG'a, hG'd, hG'c⟩ := hG'
  classical
  have hov : ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G' k p = G l p - G' l p := by
    intro k l p hk hl hp
    have h1 := hGc k l p hk hl hp
    have h2 := hG'c k l p hk hl hp
    linear_combination h1 - h2
  let F : P × (Fin g → ℂ) → ℂ := fun p =>
    if h : ∃ k, p ∈ W k then G h.choose p - G' h.choose p else 0
  have hFeq : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → F p = G k p - G' k p := by
    intro k p hk hp
    have h : ∃ k, p ∈ W k := ⟨k, hk⟩
    simp only [F, dif_pos h]
    exact hov _ _ p h.choose_spec hk hp
  have hFloc : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → (fun q => G k q - G' k q) =ᶠ[nhds p] F := by
    intro k p hk hp
    filter_upwards [((hW k).inter (hZ.prod hC)).mem_nhds ⟨hk, hp⟩] with q hq
    exact (hFeq k q hq.1 hq.2).symm
  have hFa : AnalyticOnNhd ℂ F (Z ×ˢ C) := by
    intro p hp
    obtain ⟨k, hk⟩ := hcov p hp
    exact ((hGa k p ⟨hk, hp⟩).sub (hG'a k p ⟨hk, hp⟩)).congr (hFloc k p hk hp)
  have hFd : ∀ a, ∀ p ∈ Z ×ˢ C, fderiv ℂ F p (0, Pi.single a 1) = 0 := by
    intro a p hp
    obtain ⟨k, hk⟩ := hcov p hp
    have hs : HasFDerivAt (fun q => G k q - G' k q)
        (fderiv ℂ (G k) p - fderiv ℂ (G' k) p) p :=
      (hGa k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt.sub
        (hG'a k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt
    rw [← (hFloc k p hk hp).fderiv_eq, hs.fderiv]
    simp [hGd k a p hk hp, hG'd k a p hk hp]
  obtain ⟨y₀, hy₀⟩ := hCn
  refine ⟨fun z => F (z, y₀), ?_, ?_⟩
  · intro z hz
    have hi : AnalyticAt ℂ (fun w : P => (w, y₀)) z := analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (g := F) (f := fun w : P => (w, y₀)) (hFa (z, y₀) ⟨hz, hy₀⟩) hi
  · intro k p hk hp
    have hc := eq_of_fderiv_fibre_zero_convex F Z C hC hCc hFa hFd hp.1 hp.2 hy₀
    have hp' : ((p.1, p.2) : P × (Fin g → ℂ)) = p := rfl
    rw [hp'] at hc
    show G k p = G' k p + F (p.1, y₀)
    rw [← hc, hFeq k p hk hp]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxUnitPadicTensorStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_unit_padic_tensor : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), ∃ (b : E) (s : ℚ_[ℓ] ⊗[ℚ] E), IsIntegral ℤ_[ℓ] s ∧ (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = (z : ℚ_[ℓ] ⊗[ℚ] E) * (1 + (ℓ : ℚ_[ℓ] ⊗[ℚ] E) * s) := by
  first | (exact @GlobalTheory.PadicTensorApprox.exists_approx_unit) | (exact GlobalTheory.PadicTensorApprox.exists_approx_unit) | (intros; apply GlobalTheory.PadicTensorApprox.exists_approx_unit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfBlockLowerTriangularInvStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_of_blockLowerTriangular_inv' : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M) (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O), P * P' = 1 → P' * P = 1 → (∀ i j, P (Sum.inl i) (Sum.inr j) = 0) → ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  first | exact @GlobalTheory.exists_basis_of_blockLowerTriangular_inv | exact GlobalTheory.exists_basis_of_blockLowerTriangular_inv | (intros; apply GlobalTheory.exists_basis_of_blockLowerTriangular_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorOfValuationLeCofiniteStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_of_valuation_le_cofinite : ∀ (E : Type) [Field E] [NumberField E] (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)),
    (∀ᶠ w in Filter.cofinite, β w ≤ 1) → ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) → IsIntegral ℤ ((D : E) * x) := by
  first | exact @GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | exact GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le | (intros; apply GlobalTheory.ValBoundDenom.exists_common_denominator_of_valuation_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIdealMulEqSpanNumberFieldStatement
section
open scoped NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_ideal_mul_eq_span_numberField : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (w : Ideal (𝓞 F)), w ≠ ⊥ → ∃ (g e : 𝓞 F) (𝔟 : Ideal (𝓞 F)), g ≠ 0 ∧ e ∈ w ∧ 1 - e ∈ 𝔟 ∧ w * 𝔟 = Ideal.span {g} ∧ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
  first | (exact @GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime) | (exact GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime) | (intros; apply GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetOneMulStdBlockStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_det_one_mul_stdBlock' : ∀ {K : Type} [Field K] {n r : ℕ}, r < n → ∀ y : Matrix (Fin n) (Fin r) K, y.rank = r → ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧ g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y := by
  first | exact @GlobalTheory.exists_det_one_mul_stdBlock | exact GlobalTheory.exists_det_one_mul_stdBlock | (intros; apply GlobalTheory.exists_det_one_mul_stdBlock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingBijectiveLocalizedModuleMapOfRankStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localizedModule_map_bijective_of_rankAtStalk_eq : ∀ (R Q : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q] (N r : ℕ) (b : Fin N → Q), Submodule.span R (Set.range b) = ⊤ → (∀ P : PrimeSpectrum R, Module.rankAtStalk Q P = r) → ∀ P₀ : PrimeSpectrum R, ∃ (σ : Fin r ↪ Fin N) (f : R), f ∉ P₀.asIdeal ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers f) (Fintype.linearCombination R (b ∘ σ))) := by
  first | (exact @GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk) | (exact GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk) | (intros; apply GlobalTheory.exists_embedding_bijective_localizedModule_map_of_rankAtStalk  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAlgebraMapOfIntegralAtHeightOnePrimes
section
open scoped BigOperators Matrix ComplexConjugate
open Polynomial

namespace GlobalTheory

theorem integral_of_forall_height_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
      (t : FractionRing R),
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧
        t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) →
      ∃ a : R, algebraMap R (FractionRing R) a = t := by
  intro R _ _ _ _ t h
  exact ReciprocityTheory.ChartRestriction.G.T0.mem_of_mem_heightOne_localizations (K := FractionRing R) t
    (fun p hp h1 => @h p hp h1)

end GlobalTheory
end

