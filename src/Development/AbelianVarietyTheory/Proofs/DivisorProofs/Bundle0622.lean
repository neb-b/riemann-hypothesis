module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensor
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KerTensor

theorem exists_factor {O σ A M : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module O M]
    (ev : MvPowerSeries σ O →ₐ[O] A) (hs : Function.Surjective ev)
    (ℓ : MvPowerSeries σ O →ₗ[O] M) (h : ∀ f, ev f = 0 → ℓ f = 0) :
    ∃ l : A →ₗ[O] M, ∀ f, l (ev f) = ℓ f := by
  have hle : LinearMap.ker ev.toLinearMap ≤ LinearMap.ker ℓ := fun f hf => h f hf
  have hs' : Function.Surjective ev.toLinearMap := hs
  refine ⟨(LinearMap.ker ev.toLinearMap).liftQ ℓ hle ∘ₗ
    (ev.toLinearMap.quotKerEquivOfSurjective hs').symm.toLinearMap, fun f => ?_⟩
  have : (ev.toLinearMap.quotKerEquivOfSurjective hs').symm (ev f) = Submodule.Quotient.mk f := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]; rfl
  simp [this]

theorem eval_coe {O σ A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (ev : MvPowerSeries σ O →ₐ[O] A) (x : σ → A)
    (hx : ∀ i, ev (X i) = x i) (P : MvPolynomial σ O) :
    ev (P : MvPowerSeries σ O) = MvPolynomial.aeval x P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.coe_C, MvPolynomial.aeval_C, ← ev.commutes a]
    rfl
  | add p q hp hq => rw [MvPolynomial.coe_add, map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p i hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hp, hx,
      MvPolynomial.aeval_X]

theorem eval_monomial {O σ A : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype σ]
    (ev : MvPowerSeries σ O →ₐ[O] A) (x : σ → A)
    (hx : ∀ i, ev (X i) = x i) (γ : σ →₀ ℕ) (c : O) :
    ev ((MvPolynomial.monomial γ c : MvPolynomial σ O) : MvPowerSeries σ O) =
      c • ∏ i, x i ^ γ i := by
  rw [eval_coe ev x hx, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Algebra.smul_def]

theorem le_degree {σ : Type} [Fintype σ] (γ : σ →₀ ℕ) (k : σ) : γ k ≤ γ.degree := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.single_le_sum (f := fun i => γ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem degree_sum {σ τ : Type} [Fintype σ] [Fintype τ] (γ : σ ⊕ τ →₀ ℕ) :
    γ.degree = (Finsupp.equivFunOnFinite.symm fun i => γ (Sum.inl i) : σ →₀ ℕ).degree +
      (Finsupp.equivFunOnFinite.symm fun j => γ (Sum.inr j) : τ →₀ ℕ).degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.coe_equivFunOnFinite_symm]

end GlobalTheory.KerTensor

namespace GlobalTheory.KerTensor

theorem ker_tensor : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B) (m N : ℕ), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → (∀ f, evA f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, evB f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∀ f, E f = 0 → ∀ α : σ ⊕ τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  intro p O A B σ τ _ _ _ _ _ _ _ x y evA evB E m N hA hB hE sA sB kA kB f hf α hα
  classical
  set I : Ideal O := Ideal.span {(p : O) ^ m} with hI
  have fact : ∀ {ρ R : Type} [CommRing R] [Algebra O R] (ev : MvPowerSeries ρ O →ₐ[O] R),
      Function.Surjective ev → (∀ f, ev f = 0 → ∀ α : ρ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) →
      ∀ β : ρ →₀ ℕ, β.degree < N → ∃ l : R →ₗ[O] O ⧸ I, ∀ g, l (ev g) = Ideal.Quotient.mk I (coeff β g) := by
    intro ρ R _ _ ev hs hk β hβ
    obtain ⟨l, hl⟩ := exists_factor ev hs ((Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ coeff β) (fun g hg => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hI]
      exact Ideal.mem_span_singleton.2 (hk g hg β hβ))
    exact ⟨l, fun g => by rw [hl]; rfl⟩
  have hdeg := degree_sum α
  set α₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => α (Sum.inl i) with hα₁
  set α₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => α (Sum.inr j) with hα₂
  obtain ⟨l1, hl1⟩ := fact evA sA kA α₁ (by omega)
  obtain ⟨l2, hl2⟩ := fact evB sB kB α₂ (by omega)
  let Λ : A ⊗[O] B →ₗ[O] O ⧸ I := TensorProduct.lift ((LinearMap.mul O (O ⧸ I)).compl₁₂ l1 l2)
  have hΛ : ∀ a b, Λ (a ⊗ₜ b) = l1 a * l2 b := fun a b => by simp [Λ]

  have hmono : ∀ (γ : σ ⊕ τ →₀ ℕ) (c : O),
      Λ (E ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O)) =
        Ideal.Quotient.mk I (coeff α ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O)) := by
    intro γ c
    set γ₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => γ (Sum.inl i) with hγ₁
    set γ₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => γ (Sum.inr j) with hγ₂
    have e1 := eval_monomial evA x hA.1 γ₁ 1
    have e2 := eval_monomial evB y hB.1 γ₂ 1
    have eE := eval_monomial E _ hE.1 γ c
    have split : (∏ k, (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) k ^ γ k) =
        (∏ i, x i ^ γ₁ i) ⊗ₜ[O] (∏ j, y j ^ γ₂ j) := by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, hγ₁, hγ₂, Finsupp.coe_equivFunOnFinite_symm]
      have h1 : (∏ i, (x i ⊗ₜ[O] (1 : B)) ^ γ (Sum.inl i)) = (∏ i, x i ^ γ (Sum.inl i)) ⊗ₜ[O] (1 : B) := by
        rw [← Algebra.TensorProduct.includeLeft_apply (S := O), map_prod]
        simp only [map_pow, Algebra.TensorProduct.includeLeft_apply]
      have h2 : (∏ j, ((1 : A) ⊗ₜ[O] y j) ^ γ (Sum.inr j)) = (1 : A) ⊗ₜ[O] (∏ j, y j ^ γ (Sum.inr j)) := by
        rw [← Algebra.TensorProduct.includeRight_apply, map_prod]
        simp only [map_pow, Algebra.TensorProduct.includeRight_apply]
      rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [eE, split, map_smul, hΛ, ← one_smul O (∏ i, x i ^ γ₁ i), ← e1, ← one_smul O (∏ j, y j ^ γ₂ j),
      ← e2, hl1, hl2]
    simp only [MvPolynomial.coe_monomial, coeff_monomial]
    have hiff : α = γ ↔ α₁ = γ₁ ∧ α₂ = γ₂ := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        ext k
        cases k with
        | inl i => simpa [hα₁, hγ₁] using congrArg (fun g => g i) h1
        | inr j => simpa [hα₂, hγ₂] using congrArg (fun g => g j) h2
    by_cases h : α = γ
    · rw [if_pos h, if_pos (hiff.1 h).1, if_pos (hiff.1 h).2]
      simp [Algebra.smul_def]
    · rw [if_neg h]
      by_cases h1 : α₁ = γ₁
      · rw [if_neg (fun h2 => h (hiff.2 ⟨h1, h2⟩))]; simp
      · rw [if_neg h1]; simp
  have hpoly : ∀ P : MvPolynomial (σ ⊕ τ) O,
      Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = Ideal.Quotient.mk I (coeff α (P : MvPowerSeries (σ ⊕ τ) O)) := by
    intro P
    induction P using MvPolynomial.induction_on' with
    | monomial γ c => exact hmono γ c
    | add P Q hP hQ => rw [MvPolynomial.coe_add, map_add (f := _), map_add (f := _), hP, hQ, map_add (f := _), map_add (f := _)]

  obtain ⟨N', hN'⟩ := hE.2 m
  set K := max N' N with hK
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => K) f with hP
  have hrest : ∀ γ : σ ⊕ τ →₀ ℕ, γ.degree < K → coeff γ (f - (P : MvPowerSeries (σ ⊕ τ) O)) = 0 := by
    intro γ hγ
    have hle : γ ≤ Finsupp.equivFunOnFinite.symm fun _ => K := by
      intro k
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact le_of_lt (lt_of_le_of_lt (le_degree γ k) hγ)
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos hle, sub_self]
  obtain ⟨c, hc⟩ := hN' (f - (P : MvPowerSeries (σ ⊕ τ) O))
    (fun γ hγ => hrest γ (lt_of_lt_of_le hγ (le_max_left _ _)))
  have hzero : Λ (E (f - (P : MvPowerSeries (σ ⊕ τ) O))) = 0 := by
    rw [hc]
    have : (p : A ⊗[O] B) ^ m * c = ((p : O) ^ m) • c := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [this, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul]
  have hsplit : E f = E (P : MvPowerSeries (σ ⊕ τ) O) + E (f - (P : MvPowerSeries (σ ⊕ τ) O)) := by
    rw [← map_add (f := _), add_sub_cancel]
  have hPval : Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = 0 := by
    have := congrArg Λ hsplit
    rw [hf, map_zero, map_add (f := _), hzero, add_zero] at this
    exact this.symm
  have hcoeff : coeff α f = coeff α (P : MvPowerSeries (σ ⊕ τ) O) := by
    have := hrest α (lt_of_lt_of_le hα (le_max_right _ _))
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hmk : Ideal.Quotient.mk I (coeff α f) = 0 := by rw [hcoeff, ← hpoly, hPval]
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)

end GlobalTheory.KerTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectSectionResStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefectSection_res : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (V : Scheme.{0}) (g : V ⟶ U), Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defectSec Q q V (Units.map g.appTop.hom.toMonoidHom u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.defectSec_res
  | exact GlobalTheory.EtC.RedChern.defectSec_res
  | (intros; apply GlobalTheory.EtC.RedChern.defectSec_res <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectEqOfPowEqStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerSplittingDefect_eq_of_pow_eq : ∀ (q : ℕ) [NeZero q] (κ : twZ q ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u) → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), κ ≫ φ = resι ℤ (twZ q) → ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v' := by
  first
  | exact @GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | exact GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | (intros; apply GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectGlueQthRootsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerSplittingDefect_glue_qthRoots : ∀ (q : ℕ) [NeZero q] (φ : Gm ⟶ (res ℤ (twZ q)).X 0), (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v') → ∀ (U : Scheme.{0}) (b : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) → ∃ η : Sec ((res ℤ (twZ q)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom b → Sec.res g η = dv q φ V v := by
  first
  | exact @GlobalTheory.EtC.KumPic.DvGlue.glue
  | exact GlobalTheory.EtC.KumPic.DvGlue.glue
  | (intros; apply GlobalTheory.EtC.KumPic.DvGlue.glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDifferenceMulRootOfUnityStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerSplittingDifference_mul_rootOfUnity : ∀ (q : ℕ) [NeZero q] (κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 →
      Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) →
    ∀ φ : Gm ⟶ (res ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1))).X 0,
      κ ≫ φ = resι ℤ ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ (v ω : (Γ(U, ⊤))ˣ), ω ^ q = 1 →
      Sec.map φ (unitSec (ω * v)) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U (ω * v)) =
        Sec.map φ (unitSec v) - (restrMap (Int.castRingHom (ZMod q)) (tw q 1)).app U 0 (kumT q U v) := by
  first | (exact @GlobalTheory.EtC.kumDiff_mul_rootOfUnity) | (exact GlobalTheory.EtC.kumDiff_mul_rootOfUnity) | (intros; apply GlobalTheory.EtC.kumDiff_mul_rootOfUnity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairTransferStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pullback_pair_transfer : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') := by
  first | (exact @GlobalTheory.PullIsoCongr.isocongr) | (exact GlobalTheory.PullIsoCongr.isocongr) | (intros; apply GlobalTheory.PullIsoCongr.isocongr  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFormalGroupLawQuasiLogarithms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

variable (p : ℕ) [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p]

theorem map_inL_fr {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (f : MvPowerSeries (Fin d) R) : MvPowerSeries.map h (inL f) = inL (MvPowerSeries.map h f) := by
  unfold inL
  rw [map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_inR_fr {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (f : MvPowerSeries (Fin d) R) : MvPowerSeries.map h (inR f) = inR (MvPowerSeries.map h f) := by
  unfold inR
  rw [map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_coboundaryOne_teichmullerLift_law (σ : k →+* k') {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) (Fr p k)) :
    MvPowerSeries.map (frMap p σ) (cob1 (fun i => lift p (μ i)) f) =
      cob1 (fun i => lift p (MvPowerSeries.map σ (μ i))) (MvPowerSeries.map (frMap p σ) f) := by
  unfold cob1
  rw [map_sub, map_sub, map_inL_fr, map_inR_fr,
    map_subst (hasSubst_of_constantCoeff_zero fun i => constantCoeff_lift p (hμ i))]
  simp only [map_lift]

theorem map_mem_intBy_one (σ : k →+* k') {ι : Type} {g : MvPowerSeries ι (Fr p k)}
    (hg : g ∈ intBy p k ι 1) : MvPowerSeries.map (frMap p σ) g ∈ intBy p k' ι 1 := by
  intro α
  obtain ⟨w, hw⟩ := hg α
  refine ⟨WittVector.map σ w, ?_⟩
  rw [coeff_map, hw, one_mul, one_mul, frMap_algebraMap]

theorem map_mem_quasiInt (σ : k →+* k') {ι : Type} {g : MvPowerSeries ι (Fr p k)}
    (hg : g ∈ quasiInt p k ι) : MvPowerSeries.map (frMap p σ) g ∈ quasiInt p k' ι := by
  intro α i
  obtain ⟨w, hw⟩ := hg α i
  refine ⟨WittVector.map σ w, ?_⟩
  rw [coeff_map, ← map_natCast (frMap p σ), ← map_mul, hw, frMap_algebraMap]

theorem frMap_red (σ : k →+* k') {x : Fr p k} {a : WittVector p k} {b : k}
    (hx : x = algebraMap _ (Fr p k) a) (ha : WittVector.constantCoeff a = b) :
    frMap p σ x = algebraMap _ (Fr p k') (WittVector.map σ a) ∧
      WittVector.constantCoeff (WittVector.map σ a) = σ b := by
  refine ⟨by rw [hx, frMap_algebraMap], ?_⟩
  rw [← ha, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem quasiLog_map :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [Field k'] [CharP k' p]
      (σ : k →+* k') (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ)
      (hμ' : IsLaw (fun i => MvPowerSeries.map σ (μ i))), ∀ f ∈ quasiLog p hμ,
      MvPowerSeries.map (frMap p σ) f ∈ quasiLog p hμ' ∧
      (f ∈ intBy p k (Fin d) 1 → MvPowerSeries.map (frMap p σ) f ∈ intBy p k' (Fin d) 1) ∧
      (∀ t, Red p (cob1 (fun i => Katz.lift p (μ i)) f) t →
        Red p (cob1 (fun i => Katz.lift p (MvPowerSeries.map σ (μ i)))
          (MvPowerSeries.map (frMap p σ) f)) (MvPowerSeries.map σ t)) ∧
      ∀ w, RedV p (lin f) w → RedV p (lin (MvPowerSeries.map (frMap p σ) f)) (fun i => σ (w i)) := by
  intro p _ k k' _ _ _ _ σ d μ hμ hμ' f hf
  have key := map_coboundaryOne_teichmullerLift_law p σ μ hμ.const f
  refine ⟨⟨map_mem_quasiInt p σ hf.1, ?_⟩, map_mem_intBy_one p σ, ?_, ?_⟩
  · rw [← key]; exact map_mem_intBy_one p σ hf.2
  · intro t ht α
    obtain ⟨w, hw, hw0⟩ := ht α
    obtain ⟨e1, e2⟩ := frMap_red p σ hw hw0
    refine ⟨WittVector.map σ w, ?_, ?_⟩
    · rw [← key, coeff_map, e1]
    · rw [e2, coeff_map]
  · intro w hw i
    obtain ⟨a, ha, ha0⟩ := hw i
    obtain ⟨e1, e2⟩ := frMap_red p σ ha ha0
    refine ⟨WittVector.map σ a, ?_, e2⟩
    change coeff _ (MvPowerSeries.map (frMap p σ) f) = _
    rw [coeff_map]; exact e1

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdLiftOfFrameMatrixEquation
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem mu_dvd_of_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι κ : Type) [Fintype ι] (R S : Matrix ι ι F.B) (R0 S0 : Matrix ι ι (Ainf p O)) (Y : Matrix ι κ F.B) (F0 : Matrix ι κ (Ainf p O)), (∀ i j, F.τ ∣ R i j - F.a (R0 i j)) → (∀ i j, F.τ ∣ S i j - F.a (S0 i j)) → (∀ i m, F.τ ∣ Y i m - F.a (F0 i m)) → R * Y.map F.σ = S * Y → ∀ i m, Sandwich.mu ε ∣ (R0 * F0.map WittVector.frobenius - S0 * F0) i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F ι κ _ R S R0 S0 Y F0 hR hS hY hRS i m
  apply (F.a_dvd _).1
  set q := Ideal.Quotient.mk (Ideal.span {F.τ})
  have key : ∀ x y : F.B, F.τ ∣ x - y → q x = q y := fun x y h =>
    Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
  have hR' : ∀ i j, q (R i j) = q (F.a (R0 i j)) := fun i j => key _ _ (hR i j)
  have hS' : ∀ i j, q (S i j) = q (F.a (S0 i j)) := fun i j => key _ _ (hS i j)
  have hY' : ∀ i m, q (Y i m) = q (F.a (F0 i m)) := fun i m => key _ _ (hY i m)
  have hYσ : ∀ i m, q (F.σ (Y i m)) = q (F.a (WittVector.frobenius (F0 i m))) := fun i m => by
    apply key
    rw [← F.σ_a, ← map_sub]
    exact tau_dvd_sigma F _ (hY i m)
  have h := congrArg (fun M => q (M i m)) hRS
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul] at h
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change q _ = 0
  rw [Matrix.sub_apply, map_sub, map_sub, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Matrix.map_apply, ← hR', ← hS', ← hYσ, ← hY']
  exact h

end GlobalTheory.WinLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesEvalTruncSubstEqSum
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DivSub

theorem eval_trunc'_eq_sum {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] (w : σ → R)
    (n : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    MvPolynomial.eval w (trunc' R n f) = ∑ β ∈ Finset.Iic n, coeff β f * ∏ i ∈ β.support, w i ^ β i := by
  have hsub : (trunc' R n f).support ⊆ Finset.Iic n := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, coeff_trunc'] at hm
    split_ifs at hm with h
    · exact Finset.mem_Iic.mpr h
    · exact absurd rfl hm
  rw [MvPolynomial.eval_eq, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [coeff_trunc', if_pos (Finset.mem_Iic.mp hm)]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

theorem eval_trunc'_subst_eq_sum :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] [DecidableEq σ]
      [Fintype τ] [DecidableEq τ] (z : σ → B) (u : τ → MvPowerSeries σ B),
      (∀ j, constantCoeff (u j) = 0) → ∀ (g : MvPowerSeries τ Q) (n : σ →₀ ℕ)
      (S : Finset (τ →₀ ℕ)), (∀ α : τ →₀ ℕ, α.degree ≤ n.degree → α ∈ S) →
      MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) g)) =
        ∑ α ∈ S, coeff α g *
          algebraMap B Q (MvPolynomial.eval z (trunc' B n (α.prod fun j e => u j ^ e))) := by
  intro B Q _ _ _ σ τ _ _ _ _ z u hu g n S hS
  have ha : HasSubst (up Q u) :=
    hasSubst_of_constantCoeff_zero fun j => by simp [up, constantCoeff_map, hu j]
  have hP : ∀ α : τ →₀ ℕ, (α.prod fun j e => (up Q u j) ^ e) =
      map (algebraMap B Q) (α.prod fun j e => u j ^ e) := by
    intro α
    rw [map_finsuppProd]
    simp [up, map_pow]
  have hcoeff : ∀ β ≤ n, coeff β (subst (up Q u) g) =
      ∑ α ∈ S, coeff α g * algebraMap B Q (coeff β (α.prod fun j e => u j ^ e)) := by
    intro β hβ
    rw [coeff_subst ha]
    simp_rw [hP, coeff_map, smul_eq_mul]
    apply finsum_eq_sum_of_support_subset
    intro α hα
    by_contra hαS
    apply hα
    dsimp only
    have hlt : n.degree < α.degree := lt_of_not_ge fun h => hαS (hS α h)
    rw [_root_.GlobalTheory.DivMono.coeff_finsuppProd_eq_zero_of_degree_lt B σ τ u hu α β (lt_of_le_of_lt (Finsupp.degree_mono hβ) hlt), map_zero,
      mul_zero]
  rw [eval_trunc'_eq_sum, Finset.sum_congr rfl fun β hβ => by
    rw [hcoeff β (Finset.mem_Iic.mp hβ)]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eval_trunc'_eq_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_mul, map_prod]
  simp_rw [map_pow]
  ring

end GlobalTheory.DivSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderSurjectsMatrixAlgebraModPrimePowerStatement
section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    (p : 𝓞 D.F) ∈ w0 →
    ∃ φ : D.O →ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⧸ w0 ^ r), Function.Surjective φ ∧
      ∀ b, φ b = 0 → b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O) := by
  first | (exact @GlobalTheory.UPel.HT.MatRed.exists_matRed) | (exact GlobalTheory.UPel.HT.MatRed.exists_matRed) | (intros; apply GlobalTheory.UPel.HT.MatRed.exists_matRed <;> assumption)
end

