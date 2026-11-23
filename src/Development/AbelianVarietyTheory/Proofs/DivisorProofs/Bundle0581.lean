module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0561
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionLatticeTensorOfSubstitutionSt
section
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section
namespace GlobalTheory.LeviCut

theorem mem_range_map_of_flat {M1 M2 : Type} [AddCommGroup M1] [AddCommGroup M2]
    (N1 : Submodule ℤ M1) (N2 : Submodule ℤ M2) [Module.Flat ℤ (M2 ⧸ N2)] (z : M1 ⊗[ℤ] M2)
    (h1 : z ∈ LinearMap.range (LinearMap.lTensor M1 N2.subtype))
    (h2 : z ∈ LinearMap.range (LinearMap.rTensor M2 N1.subtype)) :
    z ∈ LinearMap.range (TensorProduct.map N1.subtype N2.subtype) := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨w, rfl⟩ := h2
  have hw : LinearMap.lTensor N1 N2.mkQ w = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M2 ⧸ N2) N1.subtype N1.injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, ← hu, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : N2.mkQ ∘ₗ N2.subtype = 0 := by ext x; simp
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨w', hw'⟩ := (lTensor_exact N1 (LinearMap.exact_subtype_mkQ N2) N2.mkQ_surjective w).1 hw
  refine ⟨w', ?_⟩
  rw [← hw', ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]

theorem flat_quot_dualWeyl (q : ℕ) (ν : Fin q → ℕ) :
    Module.Flat ℤ (MvPolynomial (Fin q × Fin q) ℤ ⧸ dualWeyl ℤ q q ν) := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨⟨c, hc⟩, hcx⟩ := (Submodule.mem_torsion_iff x).1 hx
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have : c • f ∈ dualWeyl ℤ q q ν := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; simpa using hcx
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact dualWeylSat ℤ q q ν c f hc0 this

theorem bidet_map' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

def psiR (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ) :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ))
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ))
      (fun s => C (X (a, s))) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ))
      (fun _ => 0) (fun t => X (b, t)) v.2) v.1

def psiL (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ) :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ))
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ))
      (fun s => X (a, s)) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ))
      (fun _ => 0) (fun t => C (X (b, t))) v.2) v.1

def phiR (p q : ℕ) : MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ) →+*
    MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ :=
  eval₂Hom Algebra.TensorProduct.includeLeftRingHom (fun v => 1 ⊗ₜ X v)

def phiL (p q : ℕ) : MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ) →+*
    MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ :=
  eval₂Hom (Algebra.TensorProduct.includeRight : MvPolynomial (Fin q × Fin q) ℤ →ₐ[ℤ] _).toRingHom
    (fun v => X v ⊗ₜ 1)

theorem phiR_psiR (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) :
    phiR p q (aeval (psiR p q) (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ) f)) = resT ℤ p q f := by
  have : (phiR p q).comp ((aeval (psiR p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ))) = (resT ℤ p q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiR p q).comp ((aeval (psiR p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ)))).comp C) ((resT ℤ p q).toRingHom.comp C)) r
    rintro ⟨i, j⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
        (simp [phiR, psiR, resT, resVarT])
  exact DFunLike.congr_fun this f

theorem phiL_psiL (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) :
    phiL p q (aeval (psiL p q) (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ) f)) = resT ℤ p q f := by
  have : (phiL p q).comp ((aeval (psiL p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ))) = (resT ℤ p q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiL p q).comp ((aeval (psiL p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ)))).comp C) ((resT ℤ p q).toRingHom.comp C)) r
    rintro ⟨i, j⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
        (simp [phiL, psiL, resT, resVarT])
  exact DFunLike.congr_fun this f

theorem phiR_map (p q : ℕ) (h : MvPolynomial (Fin q × Fin q) ℤ) :
    phiR p q (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ) h) = 1 ⊗ₜ h := by
  have : (phiR p q).comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ)) =
      (Algebra.TensorProduct.includeRight : _ →ₐ[ℤ] MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiR p q).comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ))).comp C) (((Algebra.TensorProduct.includeRight : _ →ₐ[ℤ] MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] _).toRingHom).comp C)) r
    intro v; (simp [phiR])
  exact DFunLike.congr_fun this h

theorem phiL_map (p q : ℕ) (h : MvPolynomial (Fin p × Fin p) ℤ) :
    phiL p q (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ) h) = h ⊗ₜ 1 := by
  have : (phiL p q).comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ)) =
      (Algebra.TensorProduct.includeLeft : _ →ₐ[ℤ] _ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiL p q).comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ))).comp C) (((Algebra.TensorProduct.includeLeft : _ →ₐ[ℤ] _ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ).toRingHom).comp C)) r
    intro v; (simp [phiL])
  exact DFunLike.congr_fun this h

theorem mul_mem_range_lTensor {A B : Type} [CommRing A] [CommRing B] (N : Submodule ℤ B) (u : A)
    (x : A ⊗[ℤ] B) (hx : x ∈ LinearMap.range (LinearMap.lTensor A N.subtype)) :
    (u ⊗ₜ (1 : B)) * x ∈ LinearMap.range (LinearMap.lTensor A N.subtype) := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.inductionOn with
  | tmul a n => exact ⟨(u * a) ⊗ₜ n, by simp⟩
  | add x y hx hy => rw [map_add (f := _), mul_add]; exact add_mem hx hy

theorem mul_mem_range_rTensor {A B : Type} [CommRing A] [CommRing B] (N : Submodule ℤ A) (u : B)
    (x : A ⊗[ℤ] B) (hx : x ∈ LinearMap.range (LinearMap.rTensor B N.subtype)) :
    ((1 : A) ⊗ₜ u) * x ∈ LinearMap.range (LinearMap.rTensor B N.subtype) := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.inductionOn with
  | tmul n b => exact ⟨n ⊗ₜ (u * b), by simp⟩
  | add x y hx hy => rw [map_add (f := _), mul_add]; exact add_mem hx hy

theorem resT_mem_lTensor (hS : SubstMem) (p q : ℕ) (ν : Fin (p + q) → ℕ)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) (hf : f ∈ dualWeyl ℤ (p + q) (p + q) ν) :
    resT ℤ p q f ∈ LinearMap.range (LinearMap.lTensor (MvPolynomial (Fin p × Fin p) ℤ)
      (dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j))).subtype) := by
  have hg : aeval (psiR p q) (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ) f) ∈
      dualWeyl (MvPolynomial (Fin p × Fin p) ℤ) q q (fun j => ν (Fin.natAdd p j)) := by
    refine hS (MvPolynomial (Fin p × Fin p) ℤ) q (p + q) (Fin.natAdd p) (Fin.strictMono_natAdd p) (psiR p q)
      ?_ ?_ ?_ ν _ (dualWeylMap ℤ _ C _ _ ν f hf)
    · intro a s; simp [psiR]
    · intro x s hx
      induction x using Fin.addCases with
      | left a => simp [psiR]
      | right b => exact absurd ⟨b, rfl⟩ hx
    · intro x y hy
      induction y using Fin.addCases with
      | right t => exact absurd ⟨t, rfl⟩ hy
      | left s =>
        induction x using Fin.addCases with
        | left a => exact ⟨X (a, s), by simp [psiR]⟩
        | right b => exact ⟨0, by simp [psiR]⟩
  rw [standardMonomialSpanDomain] at hg
  rw [← phiR_psiR]
  refine Submodule.span_induction (p := fun g _ => phiR p q g ∈ LinearMap.range
    (LinearMap.lTensor (MvPolynomial (Fin p × Fin p) ℤ) (dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j))).subtype))
    ?_ ?_ ?_ ?_ hg
  · rintro g ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← bidet_map' (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ), phiR_map]
    exact ⟨1 ⊗ₜ ⟨bideterminant ℤ sz hsz I, hsh ▸ bidetMem ℤ q q K sz hsz I⟩, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro u x _ hx
    rw [smul_eq_C_mul, map_mul]
    have : phiR p q (C u) = u ⊗ₜ 1 := by simp [phiR]
    rw [this]; exact mul_mem_range_lTensor _ u _ hx

theorem resT_mem_rTensor (hS : SubstMem) (p q : ℕ) (ν : Fin (p + q) → ℕ)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) (hf : f ∈ dualWeyl ℤ (p + q) (p + q) ν) :
    resT ℤ p q f ∈ LinearMap.range (LinearMap.rTensor (MvPolynomial (Fin q × Fin q) ℤ)
      (dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i))).subtype) := by
  have hg : aeval (psiL p q) (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ) f) ∈
      dualWeyl (MvPolynomial (Fin q × Fin q) ℤ) p p (fun i => ν (Fin.castAdd q i)) := by
    refine hS (MvPolynomial (Fin q × Fin q) ℤ) p (p + q) (Fin.castAdd q) (Fin.strictMono_castAdd q) (psiL p q)
      ?_ ?_ ?_ ν _ (dualWeylMap ℤ _ C _ _ ν f hf)
    · intro a s; simp [psiL]
    · intro x s hx
      induction x using Fin.addCases with
      | left a => exact absurd ⟨a, rfl⟩ hx
      | right b => simp [psiL]
    · intro x y hy
      induction y using Fin.addCases with
      | left s => exact absurd ⟨s, rfl⟩ hy
      | right t =>
        induction x using Fin.addCases with
        | left a => exact ⟨0, by simp [psiL]⟩
        | right b => exact ⟨X (b, t), by simp [psiL]⟩
  rw [standardMonomialSpanDomain] at hg
  rw [← phiL_psiL]
  refine Submodule.span_induction (p := fun g _ => phiL p q g ∈ LinearMap.range
    (LinearMap.rTensor (MvPolynomial (Fin q × Fin q) ℤ) (dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i))).subtype))
    ?_ ?_ ?_ ?_ hg
  · rintro g ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← bidet_map' (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ), phiL_map]
    exact ⟨⟨bideterminant ℤ sz hsz I, hsh ▸ bidetMem ℤ p p K sz hsz I⟩ ⊗ₜ 1, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro u x _ hx
    rw [smul_eq_C_mul, map_mul]
    have : phiL p q (C u) = 1 ⊗ₜ u := by simp [phiL]
    rw [this]; exact mul_mem_range_rTensor _ u _ hx

def toQ (p q : ℕ) : MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ →+*
    MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] MvPolynomial (Fin q × Fin q) ℚ :=
  (Algebra.TensorProduct.lift
    (RingHom.toIntAlgHom ((Algebra.TensorProduct.includeLeftRingHom).comp (map (Int.castRingHom ℚ))))
    (RingHom.toIntAlgHom ((Algebra.TensorProduct.includeRight :
      MvPolynomial (Fin q × Fin q) ℚ →ₐ[ℚ] MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] _).toRingHom.comp
        (map (Int.castRingHom ℚ))))
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toQ_tmul (p q : ℕ) (a : MvPolynomial (Fin p × Fin p) ℤ) (b : MvPolynomial (Fin q × Fin q) ℤ) :
    toQ p q (a ⊗ₜ b) = intQ p p a ⊗ₜ intQ q q b := by
  simp [toQ, intQ, RingHom.toIntAlgHom_apply]

theorem toQ_resT (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) :
    toQ p q (resT ℤ p q f) = resT ℚ p q (intQ (p + q) (p + q) f) := by
  have : (toQ p q).comp (resT ℤ p q).toRingHom = (resT ℚ p q).toRingHom.comp (map (Int.castRingHom ℚ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((toQ p q).comp (resT ℤ p q).toRingHom).comp C)
        (((resT ℚ p q).toRingHom.comp (map (Int.castRingHom ℚ))).comp C)) r
    rintro ⟨i, j⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [toQ, resT, resVarT, RingHom.toIntAlgHom_apply]
  exact RingHom.congr_fun this f

theorem resLat_of_substMem : SubstMem → ResLat := by
  intro hS p q ν f hf
  have := flat_quot_dualWeyl q (fun j => ν (Fin.natAdd p j))
  obtain ⟨w, hw⟩ := mem_range_map_of_flat (dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)))
    (dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j))) (resT ℤ p q f)
    (resT_mem_lTensor hS p q ν f hf) (resT_mem_rTensor hS p q ν f hf)
  rw [← toQ_resT, ← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorProduct.map_tmul, toQ_tmul]
    exact Submodule.subset_span ⟨a.1, a.2, b.1, b.2, rfl⟩
  | add x y hx hy => simp only [map_add]; exact add_mem hx hy

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractModStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarge_strictHenselisation_retract_mod : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ True) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.enlarge_retract) | (exact GlobalTheory.KeyOriginEnlarge.enlarge_retract) | (intros; apply GlobalTheory.KeyOriginEnlarge.enlarge_retract  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulResidueFibreClassOfPullbackEqZero
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem tmul_of_pull_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, pullHO1 h.w y = 0 → ∃ u : HO1 s₀, TMul h₀.w t u y := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl y hy
  have : IsClosedImmersion φ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ) hse.1)
  have : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip
    (IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom σ₀) hse.2.2.1)
  have hsec := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl
  have hred := _root_.GlobalTheory.AbCoh.red_iff_pre R R' X X' s s' σ φ h.w
  have hred₀ := _root_.GlobalTheory.AbCoh.red_iff_pre R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w
  have hb₀ := _root_.GlobalTheory.AbCoh.preRes_bijective R₀ X X₀ φ₀ s₀
  have nat : ∀ {U V : AffOp X} (a : U ⟶ V) (b : (OAff s).obj U),
      preα φ s s' V (mp (OAff s) a b) = mp (OPre φ s') a (preα φ s s' U b) :=
    fun a b ↦ (preCoef h.w).naturality a b
  have nat₀ : ∀ {U V : AffOp X} (a : U ⟶ V) (b : (OAff s).obj U),
      preα φ₀ s s₀ V (mp (OAff s) a b) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ U b) :=
    fun a b ↦ (preCoef h₀.w).naturality a b
  obtain ⟨c, rfl⟩ := H1.mk_surjective _ y
  have h1 : (preCoef h.w).pull1 (H1.mk _ c) = 0 := by rw [← hred.2.2.1, hy, map_zero]
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at h1
  obtain ⟨g', hg'⟩ := h1
  choose g hg using fun U ↦ (hsec U).1 (g' U)
  have hk : ∀ (U V : AffOp X) (a : U ⟶ V), preα φ s s' V (c.1 U V a - d0 _ g U V a) = 0 := by
    intro U V a
    have e := congrFun (congrFun (congrFun hg' U) V) a
    rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
    rw [map_sub, amitsur_d0_apply, map_sub, nat, hg, hg]
    exact sub_eq_zero.2 e.symm
  choose f hf using fun U V a ↦ ((hsec V).2.1 _).1 (hk U V a)
  let c' : Z1 (OAff s) := c - ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩
  have hc' : c'.1 = t • (f : C1 (OAff s)) := by
    funext U V a; exact hf U V a
  have hz : ∀ ⦃U V W : AffOp X⦄ (a : U ⟶ V) (b : V ⟶ W),
      t • (mp (OAff s) b (f U V a) + f V W b - f U W (a ≫ b)) = 0 := by
    intro U V W a b
    have e := c'.2 a b
    rw [hc'] at e
    simp only [Pi.smul_apply, map_smul] at e
    rw [smul_sub, smul_add, e, sub_self]
  let c₀ : Z1 (OPre φ₀ s₀) := ⟨fun U V a ↦ preα φ₀ s s₀ V (f U V a), fun U V W a b ↦ by
    have e := ((hsec W).2.2.2 _).2 (hz a b)
    rw [map_sub, map_add (f := _), nat₀] at e
    exact (sub_eq_zero.1 e).symm⟩
  obtain ⟨u, hu⟩ := hb₀.1.2 (H1.mk _ c₀)
  refine ⟨u, f, c', hc', ?_, (hred₀.1 f u).2 ⟨c₀, fun _ _ _ ↦ rfl, hu.symm⟩⟩
  rw [map_sub, sub_eq_self]
  exact H1.mk_eq_zero.2 ⟨g, rfl⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitary
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.RingContH

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  intro R _ F hF J _ _ D c hc n
  obtain ⟨_, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ringCohomologyComplex_continuous_filtered_colimit R F hF J D c hc n
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := hsurj (sp c.pt) n x
    obtain ⟨j, w, y, hw, hwy⟩ := h1 z hz
    refine ⟨j, cl _ n w hw, ?_⟩
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, heq]
    exact ⟨y, hwy⟩
  · obtain ⟨w, hw, rfl⟩ := hsurj (sp (D.obj j)) n y
    obtain ⟨h, hh⟩ := hpull (sp c.pt) (sp (D.obj j)) (spMap (c.ι.app j).hom) n w hw
    rw [hh, hzero] at hy
    obtain ⟨k, f, y', hy'⟩ := h2 j w hw hy
    refine ⟨k, f, ?_⟩
    obtain ⟨h', hh'⟩ := hpull (sp (D.obj k)) (sp (D.obj j)) (spMap (D.map f).hom) n w hw
    rw [hh', hzero]
    exact ⟨y', hy'⟩

end GlobalTheory.EtC.RingContH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatDescentGeometricPoints
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleGeomDescent

open scoped TensorProduct

theorem eq_of_geometric_points' {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rwa [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this

theorem descent : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsReduced A] [IsJacobsonRing A],
    Module.FaithfullyFlat A B → Algebra.Etale A B → ∀ b : B,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (φ ψ : B →+* k), φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) →
      φ b = ψ b) → ∃ a : A, algebraMap A B a = b := by
  intro A B _ _ _ _ _ hff het b hb
  have hBr : _root_.IsReduced B := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced A B
  have : Algebra.Smooth B (B ⊗[A] B) := inferInstance
  have hCr : _root_.IsReduced (B ⊗[A] B) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced B (B ⊗[A] B)
  have hC : (b ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] b := by
    refine eq_of_geometric_points' _ _ fun k _ _ χ => ?_
    have key := hb k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom) ?_
    · simpa using key
    · ext a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeLeftRingHom_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hx := (Algebra.IsEffective.of_faithfullyFlat A B b).mp (by simp [hC])
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha⟩

end GlobalTheory.EtaleGeomDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualLiftLinearCoefficientsMod
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem GlobalTheory.QLog.Chart.exists_dual_lift_lin : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  intro p O _ G d c m hp
  obtain ⟨n, hn⟩ := c.ker 1 2
  refine ⟨n, fun u => ?_⟩
  let L : MvPowerSeries (Fin d) O →ₗ[O] O := ∑ i, u i • coeff (Finsupp.single i 1)
  have hL : ∀ F, L F = ∑ i, u i * lin F i := fun F => by simp [L, LinearMap.sum_apply, lin]
  let f : MvPowerSeries (Fin d) O →ₗ[O] O ⧸ m := m.mkQ ∘ₗ L
  have hk : LinearMap.ker (c.ev n).toLinearMap ≤ LinearMap.ker f := by
    intro F hF
    have h := hn F hF
    change Ideal.Quotient.mk m (L F) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hL]
    refine Submodule.sum_mem _ fun i _ => m.mul_mem_left _ ?_
    obtain ⟨a, ha⟩ := h (Finsupp.single i 1) (by simp)
    have : lin F i = p ^ 1 * a := ha
    rw [this, pow_one]
    exact m.mul_mem_right _ hp
  let g : G.A n →ₗ[O] O ⧸ m := (LinearMap.ker (c.ev n).toLinearMap).liftQ f hk ∘ₗ
    ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm.toLinearMap
  have hg : ∀ F, g (c.ev n F) = f F := fun F => by
    have : ((c.ev n).toLinearMap.quotKerEquivOfSurjective (c.surj n)).symm (c.ev n F) =
        Submodule.Quotient.mk F := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property m.mkQ g m.mkQ_surjective
  refine ⟨WithConv.toConv φ, fun F => ?_⟩
  rw [← hL, ← Submodule.Quotient.eq]
  exact (LinearMap.congr_fun hφ (c.ev n F)).trans (hg F)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterShintaniPsiLiftStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ k n : ℕ, ∃ X ∈ Virt ℂ ℂ (GHat F F' n), (∀ g, X (inl g) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n g) ∧ ∀ δ, X (inl δ * inr s) = shLift s (psiG (rootSum (pullθ ι θ) k) n) δ := by
  first | (exact @GlobalTheory.Shin.exists_virt_psi_lift) | (exact GlobalTheory.Shin.exists_virt_psi_lift) | (intros; apply GlobalTheory.Shin.exists_virt_psi_lift  <;> assumption)
end

