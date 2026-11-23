module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MassNorm

open GlobalTheory.ClassParam (krylov)

section Core

variable {R : Type} [CommRing R] {m : ℕ}

theorem aeval_of_commute_cyclic {M N : Matrix (Fin m) (Fin m) R} (v : Fin m → R) (hv : IsUnit (krylov M v).det)
    (h : Commute N M) : ∃ p : R[X], N = aeval M p := by
  let a := (krylov M v)⁻¹ *ᵥ (N *ᵥ v)
  let p : R[X] := ∑ j : Fin m, monomial (j : ℕ) (a j)
  have hp : aeval M p *ᵥ v = N *ᵥ v := by
    have : krylov M v *ᵥ a = N *ᵥ v := by rw [mulVec_mulVec, mul_nonsing_inv _ hv, one_mulVec]
    rw [← this]
    ext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [p, krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mulVec, Matrix.mulVec.eq_def (Matrix.of _), dotProduct, mul_comm]
  have hc : Commute (aeval M p) M := by
    have := congrArg (aeval M) (mul_comm p X)
    rwa [map_mul, map_mul, aeval_X] at this
  refine ⟨p, ((isUnit_iff_isUnit_det _).2 hv).mul_right_cancel ?_⟩
  rw [GlobalTheory.Orb.mul_krylov_of_commute h, GlobalTheory.Orb.mul_krylov_of_commute hc, hp]

def psi (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  D.val * GlobalTheory.Tw.Phi m R * (c.mapMatrix x)ᵀ * (GlobalTheory.Tw.Phi m R)ᵀ * (D⁻¹).val

theorem PhiT_mul_Phi : (GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R = 1 := mul_eq_one_comm.1 (Phi_mul_transpose m R)

theorem psi_mul (c : R →+* R) (D : GL (Fin m) R) (x y : Matrix (Fin m) (Fin m) R) :
    psi c D (x * y) = psi c D y * psi c D x := by
  have h1 : (D⁻¹).val * D.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [psi, map_mul, Matrix.transpose_mul]
  calc _ = D.val * GlobalTheory.Tw.Phi m R * (c.mapMatrix y)ᵀ * ((GlobalTheory.Tw.Phi m R)ᵀ * ((D⁻¹).val * D.val) * GlobalTheory.Tw.Phi m R) *
        (c.mapMatrix x)ᵀ * (GlobalTheory.Tw.Phi m R)ᵀ * (D⁻¹).val := by
        rw [h1, Matrix.mul_one, PhiT_mul_Phi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem psi_add (c : R →+* R) (D : GL (Fin m) R) (x y : Matrix (Fin m) (Fin m) R) :
    psi c D (x + y) = psi c D x + psi c D y := by
  simp only [psi, map_add (f := _), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem psi_smul (c : R →+* R) (D : GL (Fin m) R) (r : R) (x : Matrix (Fin m) (Fin m) R) :
    psi c D (r • x) = c r • psi c D x := by
  have : c.mapMatrix (r • x) = c r • c.mapMatrix x := by ext i j; simp
  simp only [psi, this, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem psi_one (c : R →+* R) (D : GL (Fin m) R) : psi c D 1 = 1 := by
  simp only [psi, map_one, Matrix.transpose_one, Matrix.mul_one]
  rw [Matrix.mul_assoc D.val, Phi_mul_transpose, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem psi_pow (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    psi c D (x ^ k) = psi c D x ^ k := by
  induction k with
  | zero => simp [psi_one]
  | succ k ih => rw [pow_succ, psi_mul, ih, pow_succ']

theorem psi_aeval (c : R →+* R) (D : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) (p : R[X]) :
    psi c D (aeval x p) = aeval (psi c D x) (p.map c) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), psi_add, hp, hq, Polynomial.map_add (f := _), map_add (f := _)]
  | monomial k r =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, psi_smul, psi_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem psi_units (c : R →+* R) (D h : GL (Fin m) R) :
    psi c D h.val = (D * thetaGL m c h⁻¹ * D⁻¹).val := by
  rw [Units.val_mul, Units.val_mul, GlobalTheory.LocTwist.thetaGL_val, inv_inv]
  simp only [psi, Matrix.mul_assoc]

theorem twCent_le (c : R →+* R) (hc : ∀ x, c (c x) = x) (D₁ D₂ : GL (Fin m) R)
    (hN : D₁ * thetaGL m c D₁ = D₂ * thetaGL m c D₂) (v : Fin m → R)
    (hv : IsUnit (krylov (D₁ * thetaGL m c D₁).val v).det) :
    twCent (thetaGL m c) D₁ ≤ twCent (thetaGL m c) D₂ := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  have hpsiN : ∀ D : GL (Fin m) R, psi c D (D * thetaGL m c D).val = ((D * thetaGL m c D)⁻¹).val := by
    intro D
    rw [psi_units]
    congr 1
    simp only [_root_.mul_inv_rev, map_mul, map_inv, hθ]
    group
  have hmem : ∀ (D g : GL (Fin m) R), g ∈ twCent (thetaGL m c) D ↔ psi c D g.val = (g⁻¹).val := by
    intro D g
    rw [psi_units]
    constructor
    · intro h
      have h' : g⁻¹ * D = D * thetaGL m c g⁻¹ := (twCent (thetaGL m c) D).inv_mem h
      congr 1
      rw [← h']; group
    · intro h
      have h' : D * thetaGL m c g⁻¹ * D⁻¹ = g⁻¹ := Units.ext h
      have : g⁻¹ ∈ twCent (thetaGL m c) D := by
        change g⁻¹ * D = D * thetaGL m c g⁻¹
        calc g⁻¹ * D = (D * thetaGL m c g⁻¹ * D⁻¹) * D := by rw [h']
          _ = _ := by group
      simpa using (twCent (thetaGL m c) D).inv_mem this
  intro g hg
  have hcomm : g * (D₁ * thetaGL m c D₁) = (D₁ * thetaGL m c D₁) * g := by
    have h1 : g * D₁ = D₁ * thetaGL m c g := hg
    have h2 : thetaGL m c g = D₁⁻¹ * g * D₁ := by rw [mul_assoc, h1]; group
    have h3 := congrArg (thetaGL m c) h2
    rw [hθ, map_mul, map_mul, map_inv, h2] at h3
    calc g * (D₁ * thetaGL m c D₁)
        = (D₁ * thetaGL m c D₁) * ((thetaGL m c D₁)⁻¹ * (D₁⁻¹ * g * D₁) * thetaGL m c D₁) := by group
      _ = _ := by rw [← h3]
  obtain ⟨p, hp⟩ := aeval_of_commute_cyclic v hv (N := g.val) (by
    change g.val * (D₁ * thetaGL m c D₁).val = (D₁ * thetaGL m c D₁).val * g.val
    rw [← Units.val_mul, ← Units.val_mul, hcomm])
  have e1 := psi_aeval c D₁ (D₁ * thetaGL m c D₁).val p
  rw [hpsiN] at e1
  have e2 := psi_aeval c D₂ (D₂ * thetaGL m c D₂).val p
  rw [hpsiN, ← hN] at e2
  rw [hmem] at hg ⊢
  rw [← hg, hp, e1, e2]

end Core

section Global

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem thF_ratF (m : ℕ) (g : GL (Fin m) E) : thF E m (ratF E m g) = ratF E m (thE E m g) :=
  (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (Af E)) _ _
    (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g).symm

theorem isClosed_twCent_thF (m : ℕ) (δ : GL (Fin m) (Af E)) : IsClosed (twCent (thF E m) δ : Set (GL (Fin m) (Af E))) := by
  have e : (twCent (thF E m) δ : Set (GL (Fin m) (Af E))) = {g | (g * δ).val = (δ * thF E m g).val} := by
    ext g; exact Units.ext_iff
  rw [e]
  haveI : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  exact isClosed_eq (Units.continuous_val.comp (continuous_id.mul continuous_const))
    (Units.continuous_val.comp (continuous_const.mul (GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _))))

theorem mass_eq_of_charpoly (m : ℕ) (δ₁ δ₂ : GL (Fin m) E)
    (h : (δ₂ * thE E m δ₂).val.charpoly = (δ₁ * thE E m δ₁).val.charpoly)
    (hs : (δ₁ * thE E m δ₁).val.charpoly.Separable) :
    mass (thF E m) (ratF E m).range (ratF E m δ₂) = mass (thF E m) (ratF E m).range (ratF E m δ₁) := by
  have hθE : ∀ g, thE E m (thE E m g) = g :=
    GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun x => IsCMField.complexConj_apply_apply E x)
  obtain ⟨x, hx⟩ := GlobalTheory.Orb.IsRegSS.exists_conj (A := E) (M := (δ₁ * thE E m δ₁).val) hs h
  have hx' : (δ₂ * thE E m δ₂) * x = x * (δ₁ * thE E m δ₁) := Units.ext hx
  have hu : (x⁻¹ * δ₂ * thE E m x) * thE E m (x⁻¹ * δ₂ * thE E m x) = δ₁ * thE E m δ₁ := by
    simp only [map_mul, map_inv, hθE]
    calc _ = x⁻¹ * ((δ₂ * thE E m δ₂) * x) := by group
      _ = _ := by rw [hx']; group
  have hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y :=
    fun y => GlobalTheory.ThetaPull.cFin_cFin y
  have hN : ratF E m δ₁ * thF E m (ratF E m δ₁) =
      ratF E m (x⁻¹ * δ₂ * thE E m x) * thF E m (ratF E m (x⁻¹ * δ₂ * thE E m x)) := by
    rw [thF_ratF, thF_ratF, ← map_mul, ← map_mul, hu]
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E m δ₁ * thF E m (ratF E m δ₁)).val (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [thF_ratF, ← map_mul]
    exact h1
  have heq : twCent (thF E m) (ratF E m δ₁) = twCent (thF E m) (ratF E m (x⁻¹ * δ₂ * thE E m x)) :=
    le_antisymm (twCent_le _ hc _ _ hN _ hv') (twCent_le _ hc _ _ hN.symm _ (hN ▸ hv'))
  set y := ratF E m x with hy
  have hconj : ratF E m (x⁻¹ * δ₂ * thE E m x) = y⁻¹ * ratF E m δ₂ * thF E m y := by
    rw [hy, thF_ratF, map_mul, map_mul, map_inv]
  have hT : twCent (thF E m) (ratF E m δ₁) = (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom := by
    rw [heq, hconj, GlobalTheory.TwOrbConj.twCent_conj]
  have hf : ∀ t : twCent (thF E m) (ratF E m δ₂), y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ twCent (thF E m) (ratF E m δ₁) := by
    intro t
    rw [hT]
    exact ⟨t, t.2, by simp [MulAut.conj_apply]⟩
  have hg : ∀ s : twCent (thF E m) (ratF E m δ₁), y * (s : GL (Fin m) (Af E)) * y⁻¹ ∈ twCent (thF E m) (ratF E m δ₂) := by
    intro s
    have hs' : (s : GL (Fin m) (Af E)) ∈ (twCent (thF E m) (ratF E m δ₂)).map (MulAut.conj y⁻¹).toMonoidHom :=
      hT ▸ s.2
    obtain ⟨t, ht, he⟩ := hs'
    have : (s : GL (Fin m) (Af E)) = y⁻¹ * t * y := by rw [← he]; simp [MulAut.conj_apply]
    rw [this]; simpa [mul_assoc] using ht
  let e : twCent (thF E m) (ratF E m δ₂) ≃ₜ* twCent (thF E m) (ratF E m δ₁) :=
    { toFun := fun t => ⟨y⁻¹ * t * y, hf t⟩
      invFun := fun s => ⟨y * s * y⁻¹, hg s⟩
      left_inv := fun t => Subtype.ext (by simp [mul_assoc])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
      continuous_invFun := Continuous.subtype_mk
        ((continuous_const.mul continuous_subtype_val).mul continuous_const) _ }
  have hyΓ : y ∈ (ratF E m).range := ⟨x, rfl⟩
  refine GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv _ _ (thF E m) (thF E m) _ _ (ratF E m δ₂) (ratF E m δ₁) (isClosed_twCent_thF E m _)
    (isClosed_twCent_thF E m _) e fun t => ?_
  change (t : GL (Fin m) (Af E)) ∈ (ratF E m).range ↔ y⁻¹ * (t : GL (Fin m) (Af E)) * y ∈ (ratF E m).range
  rw [Subgroup.mul_mem_cancel_right _ hyΓ, Subgroup.mul_mem_cancel_left _ ((ratF E m).range.inv_mem hyΓ)]

end Global

end GlobalTheory.MassNorm

theorem GlobalTheory.BCT.mass_eq_kap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (δ * thE E n δ).val.charpoly ∈ Ell E n → mass (thF E n) (ratF E n).range (ratF E n δ) = kap (δ * thE E n δ).val.charpoly * 2 ^ nfac (δ * thE E n δ).val.charpoly := by
  intro E _ _ _ _ n δ hP
  have hd : (δ * thE E n δ).val.charpoly.natDegree = n := hP.2.1
  have hs : (δ * thE E n δ).val.charpoly.Separable := hP.2.2.1
  generalize hPdef : (δ * thE E n δ).val.charpoly = P at hd hs ⊢
  have hcast : ∀ (k : ℕ) (_ : k = n), (∃ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P) ∧
      ∀ δ' : GL (Fin k) E, (δ' * thE E k δ').val.charpoly = P →
        mass (thF E k) (ratF E k).range (ratF E k δ') = mass (thF E n) (ratF E n).range (ratF E n δ) := by
    intro k hk
    subst hk
    exact ⟨⟨δ, hPdef⟩, fun δ' h' => GlobalTheory.MassNorm.mass_eq_of_charpoly E k δ δ' (h'.trans hPdef.symm) (hPdef ▸ hs)⟩
  obtain ⟨hex, hm⟩ := hcast _ hd
  unfold GlobalTheory.BCT.kap GlobalTheory.BCT.nfac
  rw [dite_eq_left hex, hm _ hex.choose_spec, div_mul_cancel₀ _ (pow_ne_zero _ two_ne_zero)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLevelFunctionInertEqLattic
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwOrbLevel

open GlobalTheory.TwLat

theorem twOrb_level_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K), Q.Monic → Q.natDegree = m → Q.Separable → IsCsr w Q → Algebra.adjoin K.E {(1 + algebraMap K.O B.A t * B.g)} = ⊤ → aeval (1 + algebraMap K.O B.A t * B.g) (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (1 + algebraMap K.O B.A t * B.g) * B.σ (1 + algebraMap K.O B.A t * B.g) = 1 → stTw m w Q (fun y : GLw m w => if y ∈ GlobalTheory.LFun.KGL w (n := m) ∧ nrmL m w y ∈ {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) = ((B.stSum : ℚ) : ℂ) := by
  intro E _ _ _ hE w hw K e hc hint hval hq k t ht htk m Q B hQm hQd hQs hQc hadj hQu hfin huσ
  set u : B.A := 1 + algebraMap K.O B.A t * B.g with hu_def
  obtain ⟨-, -, hθK, hnrm, -, -, -, -, -, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hE m w
  set cong : Set (GLw m w) := {g : GLw m w | g ∈ GlobalTheory.LFun.KGL w (n := m) ∧ ∀ i j, Valued.v (g.val i j -
    (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} with hcong
  set f : GLw m w → ℂ := fun y => if y ∈ GlobalTheory.LFun.KGL w (n := m) ∧ nrmL m w y ∈ cong then 1 else 0 with hf
  set S : Set (GLw m w) := {y | (nrmL m w y).val.charpoly = Q} with hS
  show clSum (thL m w) (GlobalTheory.LFun.KGL w (n := m)) S (fun _ => 1) f = _
  have hfK : ∀ c ∈ GlobalTheory.LFun.KGL w (n := m), ∀ y, f (c⁻¹ * y * thL m w c) = f y := by
    intro c hcK y
    have h1 : c⁻¹ * y * thL m w c ∈ GlobalTheory.LFun.KGL w (n := m) ↔ y ∈ GlobalTheory.LFun.KGL w (n := m) := by
      constructor
      · intro h
        have := mul_mem (mul_mem hcK h) (inv_mem (hθK c hcK))
        simpa [mul_assoc] using this
      · intro h
        exact mul_mem (mul_mem (inv_mem hcK) h) (hθK c hcK)
    have h2 : nrmL m w (c⁻¹ * y * thL m w c) ∈ cong ↔ nrmL m w y ∈ cong := by
      rw [hnrm]; exact GlobalTheory.T.principalCongruenceGL_conj_maxCompact_iff E w m k c _ hcK
    simp only [hf, h1, h2]
  have hf01 : ∀ y, f y = 0 ∨ f y = 1 := by
    intro y; simp only [hf]; split_ifs <;> simp
  have hSinv : ∀ y g, g⁻¹ * y * thL m w g ∈ S ↔ y ∈ S := by
    intro y g
    simp only [hS, Set.mem_setOf_eq, hnrm, Units.val_mul]
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hrstab : ∀ (δ x : GLw m w), (rStab fun k : GlobalTheory.LFun.KGL w (n := m) => f ((x * k)⁻¹ * δ * thL m w (x * k))).index ≠ 0 := by
    intro δ x
    have : rStab (fun k : GlobalTheory.LFun.KGL w (n := m) => f ((x * k)⁻¹ * δ * thL m w (x * k))) = ⊤ := by
      refine eq_top_iff.2 fun k' _ z => ?_
      have := hfK (k' : GLw m w) k'.2 ((x * ↑z)⁻¹ * δ * thL m w (x * ↑z))
      show f ((x * ↑(z * k'))⁻¹ * δ * thL m w (x * ↑(z * k'))) = f ((x * ↑z)⁻¹ * δ * thL m w (x * ↑z))
      rw [← this]
      congr 1
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [this, Subgroup.index_top]; exact one_ne_zero
  have htwinv : ∀ y g, twOrb (thL m w) (GlobalTheory.LFun.KGL w (n := m)) (g⁻¹ * y * thL m w g) f = twOrb (thL m w) (GlobalTheory.LFun.KGL w (n := m)) y f :=
    fun y g => GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ y g f (hrstab y)
  have hrank : Module.finrank K.E B.A = m := hfin.trans hQd
  let b : Module.Basis (Fin m) K.E B.A := Module.finBasisOfFinrankEq K.E B.A hrank
  have hgu : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ y ∈ L, u * y ∈ L := by
    intro L hg y hy
    rw [hu_def, add_mul, one_mul, mul_assoc]
    refine L.add_mem hy ?_
    rw [← Algebra.smul_def]
    exact L.smul_mem t (hg y hy)
  by_cases hui : IsIntegral K.O u
  · let Bu : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
    have hP : (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom :=
      _root_.GlobalTheory.charpoly_mulLeft_eq_map_symm K B _ e u Q hQm hadj hQu hfin
    have hsep : (Q.map e.symm.toRingHom).Separable := hQs.map
    obtain ⟨β₀, hβ₀, hX⟩ := GlobalTheory.UnitLemma.TwistUnit.twisted_unit_eq_unit K Bu huσ
      (by show (LinearMap.mulLeft K.E u).charpoly.Separable; rw [hP]; exact hsep) hui ((-1) ^ (m - 1))
      (neg_one_pow_eq_or B.A (m - 1))
    have hβ₀' : B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) := hβ₀
    have hgram : ∀ x : B.Aˣ, IsUnit (gram e b ((β₀ : B.A) * x)) := fun x =>
      _root_.GlobalTheory.TwLat.isUnit_gram_of_separable E hE w hw K e hc hint hval B m b u _ hsep hQu hadj _ (β₀.isUnit.mul x.isUnit)
    have hσβ : ∀ x : B.Aˣ, B.σ (x : B.A) = x → B.σ ((β₀ : B.A) * x) = (β₀ * x) * ((-1) ^ (m - 1) * u) := by
      intro x hx
      rw [map_mul, hβ₀', hx]; ring
    have hN : ∀ x : B.Aˣ, B.σ (x : B.A) = x → (nrmL m w (dlt e b ((β₀ : B.A) * x))).val = mulMat e b u :=
      fun x hx => _root_.GlobalTheory.TwLat.nrmL_dlt E hE w hw K e hc hint hval B m b u _ (hgram x) (hσβ x hx)
    have hcp : (mulMat e b u).charpoly = Q := by
      have h1 := Matrix.charpoly_map (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)) (e : K.E →+* w.adicCompletion E)
      have h2 : mulMat e b u = (LinearMap.toMatrix b b (LinearMap.mulLeft K.E u)).map (e : K.E →+* w.adicCompletion E) := rfl
      rw [h2, h1, LinearMap.charpoly_toMatrix, hP, Polynomial.map_map]
      ext n
      simp [Polynomial.coeff_map]
    obtain ⟨hΛK, hlat⟩ := GlobalTheory.T.latticeSpannedByGLColumns_eq_iff_GLint_coset E hE w hw K e hc hint hval B m b
    have hOrb : ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        twOrb (thL m w) (GlobalTheory.LFun.KGL w (n := m)) (dlt e b ((β₀ : B.A) * x)) f = ((B.N x : ℚ) : ℂ) := by
      intro x hx
      obtain ⟨φ, hφv, hφc⟩ := _root_.GlobalTheory.TwLat.twCent_equiv_torus E hE w hw K e hc hint hval B m b u _ (β₀.isUnit.mul x.isUnit)
        (hσβ x hx) hadj (hgram x)
      refine _root_.GlobalTheory.LatTransfer.twOrb_eq_N K B x (GLw m w) (thL m w) (GlobalTheory.LFun.KGL w (n := m)) _ f φ (lat e b) hfK hf01 hφc hΛK ?_ ?_
        (fun L hL => _root_.GlobalTheory.TwLat.exists_GLw_lat_eq E hE w hw K e hc hint hval B m b L hL.1)
      · intro t' q
        refine _root_.GlobalTheory.TwLatMul.lat_mul E hE w hw K e hc hint hval B m b _ q _ ?_
        rw [Units.val_mul, hφv t']
      · intro q
        have hf1 : f (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q) = 1 ↔
            (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q ∈ GlobalTheory.LFun.KGL w (n := m) ∧
              nrmL m w (q⁻¹ * dlt e b ((β₀ : B.A) * x) * thL m w q) ∈ cong) := by
          simp only [hf]; split_ifs with h <;> simp [h]
        rw [hf1, hnrm, GlobalTheory.T.twistedNorm_integral_iff_lattice_unimodular E hE w hw K e hc hint hval B m b _ (hgram x) q]
        have hlev : q⁻¹ * nrmL m w (dlt e b ((β₀ : B.A) * x)) * q ∈ cong ↔
            ∀ y ∈ lat e b q, B.g * y ∈ lat e b q :=
          GlobalTheory.T.principalCongruenceLevel_iff_lattice_stable E hE w hw K e hc hint hval B m b t k ht htk q _ (hN x hx)
        rw [hlev]
        have hXiff : (GlobalTheory.UnitLemma.IsLat K.O K.E (lat e b q) ∧ ∀ z, z ∈ lat e b q ↔
            ∀ y ∈ lat e b q, B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range) ↔ lat e b q ∈ Bu.X x := by
          rw [← hX x hx]; rfl
        constructor
        · rintro ⟨hL, hg, hsd⟩
          exact ⟨(hXiff.2 ⟨hL, hgu _ hg, hsd⟩).2, hg⟩
        · rintro ⟨hun, hg⟩
          obtain ⟨hL, -, hsd⟩ := hXiff.1 ⟨hlat q, hun⟩
          exact ⟨hL, hg, hsd⟩
    have hsum := _root_.GlobalTheory.BCT.ClSumParam.clSum_eq_finsum_param (GLw m w) (thL m w) (GlobalTheory.LFun.KGL w (n := m)) S f B.Cl
      (fun c => dlt e b ((β₀ : B.A) * ((Quot.out c).1 : B.Aˣ))) (fun c => ((B.N c.rep : ℚ) : ℂ))
      (fun c => by show (nrmL m w _).val.charpoly = Q; rw [hN _ (Quot.out c).2]; exact hcp)
      (by
        intro y hy
        obtain ⟨x, hx, g, rfl⟩ := _root_.GlobalTheory.TwLat.ClSurj.exists_twConj_dlt E hE w hw K e hc hint hval B m b u Q hQs hQu hadj β₀ hβ₀' hgram y hy
        let c : B.Cl := Quot.mk _ ⟨x, hx⟩
        obtain ⟨a, ha⟩ := _root_.GlobalTheory.UnitLemma.InvAlg.ClRel.eq_of_mk_eq K B ⟨x, hx⟩ (Quot.out c) (Quot.out_eq c).symm
        obtain ⟨g', hg'⟩ := (_root_.GlobalTheory.TwLatInj.dlt_twConj_iff E hE w hw K e hc hint hval B m b u hadj β₀ hβ₀' hgram x (Quot.out c).1 hx
          (Quot.out c).2).2 ⟨a, ha⟩
        refine ⟨c, g'⁻¹ * g, ?_⟩
        show _ = _ * dlt e b ((β₀ : B.A) * ((Quot.out c).1 : B.Aˣ)) * _
        rw [hg']
        simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left])
      (by
        intro c c' hcc
        obtain ⟨a, ha⟩ := (_root_.GlobalTheory.TwLatInj.dlt_twConj_iff E hE w hw K e hc hint hval B m b u hadj β₀ hβ₀' hgram (Quot.out c).1
          (Quot.out c').1 (Quot.out c).2 (Quot.out c').2).1 hcc
        rw [← Quot.out_eq c, ← Quot.out_eq c']
        exact Quot.sound ⟨a, ha⟩)
      hSinv htwinv (fun c => hOrb _ (Quot.out c).2)
    rw [hsum]
    show _ = ((∑ᶠ c : B.Cl, B.N c.rep : ℚ) : ℂ)
    by_cases hfs : (Function.support fun c : B.Cl => B.N c.rep).Finite
    · exact (map_finsum (Rat.castHom ℂ) hfs).symm
    · have hfs' : ¬ (Function.support fun c : B.Cl => ((B.N c.rep : ℚ) : ℂ)).Finite := by
        simpa [Function.support] using hfs
      rw [finsum_of_infinite_support hfs, finsum_of_infinite_support hfs']
      simp
  · have hX0 : ∀ x : B.A, B.X x = ∅ := by
      intro x
      ext L
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hL, hg, -⟩
      exact hui (_root_.GlobalTheory.UnitLemma.isIntegral_of_lat_stable K B u L hL (hgu L hg))
    have hN0 : ∀ x : B.A, B.N x = 0 := by
      intro x
      unfold GlobalTheory.UnitLemma.InvAlg.N GlobalTheory.UnitLemma.orbSum
      haveI : IsEmpty (GlobalTheory.UnitLemma.Orb K.O B.T (B.X x)) := by
        constructor
        intro o
        induction o using Quot.ind with
        | mk L =>
          have h := (hX0 x).subset L.2
          simp at h
      exact finsum_of_isEmpty _
    have hf0 : ∀ y ∈ S, ∀ q : GLw m w, f (q⁻¹ * y * thL m w q) = 0 := by
      intro y hy q
      simp only [hf]
      rw [if_neg]
      rintro ⟨-, hn, -⟩
      exact hui (GlobalTheory.T.isIntegral_of_integral_matrix_charpoly_root E hE w hw K e hc hint hval B m b u Q hQm hQu _ hn ((hSinv y q).2 hy))
    have hst : B.stSum = 0 := by
      unfold GlobalTheory.UnitLemma.InvAlg.stSum
      simp [hN0]
    rw [hst, Rat.cast_zero]
    unfold clSum
    refine (finsum_congr fun c => ?_).trans finsum_zero
    split_ifs with hc'
    · have h0 := hf0 _ hc'
      simp only [twOrb, avg, h0, finsum_zero, mul_zero]
    · rfl

end GlobalTheory.TwOrbLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuePulledBackSectionEqImageFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_pulledBackSection_eq_image_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : SecA A (FractionRing R) k) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R) F ⟶ A.A) (fr' : FrAt x'), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → fr.IsGen → (∀ z J, Good A.L z J → val fr' (𝟙 _) z J = val fr (spMap (algebraMap (FractionRing R) F)) z J) → ∀ c : FractionRing R, ValAt t x fr c → ValAt (GlobalTheory.TorsionExt.abPull (FractionRing R) F A k t) x' fr' (algebraMap (FractionRing R) F c) := by
  first | exact @GlobalTheory.ValuePullback.valAt_abPull | exact GlobalTheory.ValuePullback.valAt_abPull | (intros; apply GlobalTheory.ValuePullback.valAt_abPull <;> assumption)
end

