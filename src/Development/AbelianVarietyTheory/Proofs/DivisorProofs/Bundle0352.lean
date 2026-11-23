module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0319
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussLemmaSymPowMatrixUpperTriangularPlaceOrder
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

namespace GlobalTheory.Nef

theorem ordVec_symMat_mulVec_triangular : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (P : Place k E) (m : ℕ)
    (A : Matrix (Fin 2) (Fin 2) E), A 1 0 = 0 → A.det ≠ 0 → ∀ (q : Fin (m + 1) → E) (c : E) (s t : Fin m → E),
    c ≠ 0 → (∀ j, ![s j, t j] ≠ 0) →
    ∑ i : Fin (m + 1), C (q i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i) =
      C c * ∏ j, (C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X)) →
    ordVec P ((symMat m A).mulVec q) = ord P c + ∑ j, ordVec P (A.mulVec ![s j, t j]) := by
  intro k E _ _ _ P m A hA10 hdet q c s t hc hst hq
  classical
  let α : Fin m → E := fun j => s j * A 0 0 + t j * A 0 1
  let β : Fin m → E := fun j => t j * A 1 1
  have hfac : ∀ j, C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X) = C (α j) + C (β j) * X := by
    intro j
    simp only [α, β, C_add, C_mul]
    ring
  have hvec : (symMat m A).mulVec q = fun a : Fin (m + 1) => c * (∏ j, (C (α j) + C (β j) * X)).coeff a := by
    rw [symMat_mulVec, hq]
    funext a
    simp only [hfac, coeff_C_mul]
  have hsup : ∀ (n : ℕ) (x : Fin n → E), nrm P (fun a => c * x a) = P.1 c * nrm P x := by
    intro n x
    have h := Finset.comp_sup_eq_sup_comp (s := Finset.univ) (f := fun a => P.1 (x a)) (fun y => P.1 c * y)
      (fun a b => by
        rcases le_total a b with h | h
        · rw [sup_eq_right.2 h, sup_eq_right.2 (mul_le_mul' le_rfl h)]
        · rw [sup_eq_left.2 h, sup_eq_left.2 (mul_le_mul' le_rfl h)]) (by simp)
    simp only [nrm, map_mul]
    exact h.symm
  have hfin2 : ∀ f : Fin 2 → WithZero (Multiplicative ℤ), Finset.univ.sup f = max (f 0) (f 1) := by
    intro f
    refine le_antisymm (Finset.sup_le fun i _ => ?_) (max_le (Finset.le_sup (Finset.mem_univ 0))
      (Finset.le_sup (Finset.mem_univ 1)))
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hw : ∀ j, nrm P (A.mulVec ![s j, t j]) = max (P.1 (α j)) (P.1 (β j)) := by
    intro j
    rw [nrm, hfin2]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hA10, zero_mul, zero_add, α, β]
    rw [mul_comm (A 0 0), mul_comm (A 0 1), mul_comm (A 1 1)]
  have hnz : ∀ j, nrm P (A.mulVec ![s j, t j]) ≠ 0 := by
    intro j h0
    have hne : A.mulVec ![s j, t j] ≠ 0 := fun h => hst j (Matrix.eq_zero_of_mulVec_eq_zero hdet h)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    have h1 : P.1 (A.mulVec ![s j, t j] i) ≤ nrm P (A.mulVec ![s j, t j]) :=
      Finset.le_sup (f := fun i => P.1 (A.mulVec ![s j, t j] i)) (Finset.mem_univ i)
    rw [h0] at h1
    exact (Valuation.ne_zero_iff _).2 hi (le_antisymm h1 zero_le')
  have hPc : P.1 c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hlogprod : ∀ S : Finset (Fin m), WithZero.log (∏ j ∈ S, nrm P (A.mulVec ![s j, t j])) =
      ∑ j ∈ S, WithZero.log (nrm P (A.mulVec ![s j, t j])) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        WithZero.log_mul (hnz a) (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), ih]
  have hmain : nrm P ((symMat m A).mulVec q) = P.1 c * ∏ j, nrm P (A.mulVec ![s j, t j]) := by
    rw [hvec, hsup, _root_.GlobalTheory.Nef.nrm_coeff_prod_linear k E P m α β]
    simp only [hw]
  rw [ordVec, hmain, WithZero.log_mul hPc (Finset.prod_ne_zero_iff.2 fun j _ => hnz j), hlogprod, ord]
  simp only [ordVec, Finset.sum_neg_distrib]
  ring

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePointsBaseChange
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBC

theorem exists_point_ext (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D]
    (ρ : R →+* A) (hρA : ρ.comp (algebraMap A R) = RingHom.id A)
    (h : GlobalTheory.KeyOriginEnlarge.PointAtZero A R D ρ) :
    ∃ S : D →+* FractionRing A,
      S.comp (GlobalTheory.KeyOriginNoeth.baseHom A R D) = (algebraMap A (FractionRing A)).comp ρ := by
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  obtain ⟨s, hs⟩ := h
  letI : Algebra (GlobalTheory.KeyOriginNoeth.closure A R D) D :=
    (GlobalTheory.KeyOriginNoeth.closure A R D).subtype.toAlgebra
  let g : A →+* GlobalTheory.KeyOriginNoeth.closure A R D :=
    (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D)).comp (algebraMap A R)
  let M : Submonoid (GlobalTheory.KeyOriginNoeth.closure A R D) := (nonZeroDivisors A).map g
  have hg : ∀ a : A, algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a) =
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) := fun _ => rfl
  have hR : ∀ r : R, algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D
      (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) r) = GlobalTheory.KeyOriginNoeth.baseHom A R D r :=
    fun _ => rfl
  haveI : IsLocalization M D :=
    { map_units := by
        rintro ⟨_, a, ha, rfl⟩
        show IsUnit (algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a))
        rw [hg]
        exact (IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A R)
          (⟨algebraMap A R a, a, ha, rfl⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))).map
          (algebraMap (GlobalTheory.LocAcyc.GenFib A R) D)
      surj := fun d => by
        obtain ⟨a, ha, hd⟩ := GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure A R D {d}
        refine ⟨(⟨_, hd d (Finset.mem_singleton_self d)⟩,
          ⟨g a, a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩), ?_⟩
        show d * algebraMap (GlobalTheory.KeyOriginNoeth.closure A R D) D (g a) = _
        rw [hg, mul_comm]
        rfl
      exists_of_eq := fun {x y} hxy => ⟨1, by rw [Subtype.ext hxy]⟩ }
  have hρa : ∀ a : A, ρ (algebraMap A R a) = a := fun a => congrArg (fun w => w a) hρA
  have hsr : ∀ r : R, s (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) r) =
      algebraMap A (FractionRing A) (ρ r) := fun r => congrArg (fun w => w r) hs
  have hu : ∀ y : M, IsUnit (s y) := by
    rintro ⟨_, a, ha, rfl⟩
    show IsUnit (s (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D) (algebraMap A R a)))
    rw [hsr, hρa]
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, ← map_zero (algebraMap A (FractionRing A))]
    exact fun h0 => nonZeroDivisors.ne_zero ha (IsFractionRing.injective A (FractionRing A) h0)
  refine ⟨IsLocalization.lift (M := M) (S := D) hu, ?_⟩
  apply RingHom.ext; intro r
  rw [RingHom.comp_apply, ← hR, IsLocalization.lift_eq, hsr]
  rfl

end GlobalTheory.KeyOriginBC

namespace GlobalTheory.KeyOriginBC

theorem pointAtZero_bc : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [CommRing A₁] [IsDomain A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (ρ : Localization.AtPrime QA →+* A)
    (hρA : ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A)
    (hρX : ρ (algebraMap A[X] (Localization.AtPrime QA) Polynomial.X) = 0)
    (hunit : ∀ y : (GlobalTheory.KeyOriginBC.ideal₁ f i i₁ EA QA jA hcomp hj).primeCompl,
      IsUnit (GlobalTheory.KeyOriginBC.reduce f EA QA ρ hρA hρX y))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (GlobalTheory.KeyOriginBC.reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit) := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ f i i₁ hf EA _ _ _ _ QA _ jA hcomp hj ρ hρA hρX hunit DA _ _ q actA
    hq htor hpt
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA := htor.1
  obtain ⟨S, hS⟩ := exists_point_ext A (Localization.AtPrime QA) DA ρ hρA hpt

  have hfK : Function.Injective ((algebraMap A₁ (FractionRing A₁)).comp f) :=
    (IsFractionRing.injective A₁ (FractionRing A₁)).comp hf
  let φ : FractionRing A →+* FractionRing A₁ := IsFractionRing.lift hfK
  have hφ : ∀ a : A, φ (algebraMap A (FractionRing A) a) = algebraMap A₁ (FractionRing A₁) (f a) :=
    fun a => IsFractionRing.lift_algebraMap hfK a

  have hρ₁a : ∀ a : A₁, reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) a) = a :=
    fun a => congrArg (fun w => w a) (reduceLoc_algebraMap f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)
  have hu₀ : ∀ y : Algebra.algebraMapSubmonoid (Loc₁ f i i₁ EA QA jA hcomp hj) (nonZeroDivisors A₁),
      IsUnit (((algebraMap A₁ (FractionRing A₁)).comp
        (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)) y) := by
    rintro ⟨_, a, ha, rfl⟩
    simp only [RingHom.coe_comp, Function.comp_apply, hρ₁a]
    refine IsUnit.mk0 _ ?_
    rw [ne_eq, ← map_zero (algebraMap A₁ (FractionRing A₁))]
    exact fun h0 => nonZeroDivisors.ne_zero ha (IsFractionRing.injective A₁ (FractionRing A₁) h0)
  let u : GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) →+* FractionRing A₁ :=
    IsLocalization.lift hu₀
  have hu : ∀ r, u (algebraMap _ (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) r) =
      algebraMap A₁ (FractionRing A₁) (reduceLoc f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit r) :=
    fun r => IsLocalization.lift_eq hu₀ r

  let v : DA →+* FractionRing A₁ := φ.comp S
  have huv : u.comp (fibBC f i i₁ EA QA jA hcomp hj hf) =
      v.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) := by
    apply IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
    apply RingHom.ext; intro r
    simp only [RingHom.coe_comp, Function.comp_apply, fibBC_algebraMap, hu]
    have h1 := congrArg (fun w => w r) (reduceLoc_locBC f i i₁ EA QA jA hcomp hj ρ hρA hρX hunit)
    have h2 := congrArg (fun w => w r) hS
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
    rw [h1]
    show _ = φ (S (GlobalTheory.KeyOriginNoeth.baseHom A _ DA r))
    rw [h2, hφ]

  letI : Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) (FractionRing A₁) :=
    (v.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).toAlgebra
  let W₁ : BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA →+* FractionRing A₁ :=
    (Algebra.TensorProduct.productMap
      (⟨(u : Over (fibBC f i i₁ EA QA jA hcomp hj hf) →+* FractionRing A₁), fun r =>
        congrArg (fun w => w r) huv⟩ :
          Over (fibBC f i i₁ EA QA jA hcomp hj hf) →ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)]
            FractionRing A₁)
      (⟨v, fun _ => rfl⟩ : DA →ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] FractionRing A₁)).toRingHom
  have hW : ∀ y, W₁ (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
      (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA) y) = u y := by
    intro y
    show W₁ ((show Over (fibBC f i i₁ EA QA jA hcomp hj hf) from y) ⊗ₜ (1 : DA)) = u y
    refine (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans ?_
    rw [map_one, mul_one]
    rfl
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)
    (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)
  refine ⟨W₁.comp (GlobalTheory.KeyOriginNoeth.closure A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)
    (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)).subtype, ?_⟩
  apply RingHom.ext; intro r
  show W₁ (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))
      (BC (fibBC f i i₁ EA QA jA hcomp hj hf) DA)
      (algebraMap _ (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) r)) = _
  rw [hW, hu]
  rfl

end GlobalTheory.KeyOriginBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationEqLatticeSeries
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoEq

theorem ofReal_prod_cpow {ι : Type} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (c : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ c = ∏ i ∈ s, ((r i : ℂ) ^ c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, ofReal_mul,
      mul_cpow_ofReal_nonneg (hr j (Finset.mem_insert_self _ _)) (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]

variable {F : Type} [Field F] [NumberField F]

theorem eisTerm_eq_kFac (σ : ℂ) (z : Emb F → ℂ) (a b : F) :
    eisTerm 2 σ z (a, b) = kFac F σ * ∏ τ : Emb F, phi σ ((τ a : ℂ) + (τ b : ℂ) * z τ) := by
  unfold eisTerm kFac phi
  rw [← Finset.prod_mul_distrib, norm_prod, ofReal_prod_cpow _ _ (fun _ _ => norm_nonneg _), ← Finset.prod_inv_distrib,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hn : ‖latPt z (a, b) τ‖ = (2 * Real.pi) * ‖(τ a : ℂ) + (τ b : ℂ) * z τ‖ := by
    simp only [latPt, norm_mul, norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hn, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
  simp only [latPt, mul_inv, mul_pow]
  ring

theorem split_zero (I : FractionalIdeal (𝓞 F)⁰ F) (g : F → ℂ) (h : Summable (fun ν : {ν : F // ν ∈ I} => g ν.1)) :
    ∑' ν : {ν : F // ν ∈ I}, g ν.1 = g 0 + ∑' ν : NZ I, g ν.1 := by
  classical
  have h0 : (0 : F) ∈ I := (I : Submodule (𝓞 F) F).zero_mem
  rw [h.tsum_eq_add_tsum_ite ⟨0, h0⟩]
  congr 1
  let e : NZ I → {ν : F // ν ∈ I} := fun ν => ⟨ν.1, ν.2.1⟩
  have he : Function.Injective e := fun x y hxy => Subtype.ext (congrArg Subtype.val hxy : _)
  rw [← he.tsum_eq]
  · refine tsum_congr fun ν => ?_
    have : e ν ≠ ⟨0, h0⟩ := fun h' => ν.2.2 (congrArg Subtype.val h' : _)
    simp only [this, if_false, e]
  · intro x hx
    have hx0 : x ≠ ⟨0, h0⟩ := by
      intro h'; apply hx; simp [h']
    exact ⟨⟨x.1, x.2, fun h' => hx0 (Subtype.ext h')⟩, rfl⟩

theorem prod_abs_emb [IsTotallyReal F] (b : F) : ∏ τ : Emb F, |τ b| = |((Algebra.norm ℚ b : ℚ) : ℝ)| := by
  rw [← Finset.abs_prod]
  congr 1
  apply Complex.ofReal_injective
  push_cast
  exact prod_emb b

theorem fTerm_zero [IsTotallyReal F] (hzero : ∀ (σ : ℂ) (y : ℝ), y ≠ 0 → GlobalTheory.HeckeTwo.hTrans σ 0 y = GlobalTheory.HeckeTwo.cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ)) (σ : ℂ) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b : F} (hb : b ≠ 0) :
    fTerm σ z b 0 = (∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))) *
      ((|((Algebra.norm ℚ b : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  unfold fTerm
  rw [← prod_abs_emb, ofReal_prod_cpow _ _ (fun _ _ => abs_nonneg _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hy : 0 < (z τ).im := hz τ
  have hτb : τ b ≠ 0 := (map_ne_zero τ).2 hb
  rw [map_zero, zero_mul, zero_mul, ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    hzero σ _ (mul_ne_zero hτb hy.ne'), abs_mul, abs_of_pos hy, ofReal_mul,
    mul_cpow_ofReal_nonneg (abs_nonneg _) hy.le]
  ring

theorem gFun_eq_eisSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ σ : ℂ, 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) ∧ GlobalTheory.HeckeTwo.gFun Zb 𝔞 𝔟 σ z = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 2 σ z := by
  intro F _ _ _ 𝔞 𝔟 Zb hZ σ hσ z hz
  have hS := _root_.GlobalTheory.HeckeTwo.summable_eisClass_two F 𝔞 𝔟 σ hσ z hz
  refine ⟨hS, ?_⟩
  have hinv : ∀ (ε : (𝓞 F)ˣ) (a b : F),
      eisTerm 2 σ z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = eisTerm 2 σ z (a, b) :=
    fun ε a b => eisTerm_unit even_two σ z ε a b
  obtain ⟨-, -, hBs, hsum⟩ := _root_.GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup F 𝔞 𝔟 (eisTerm 2 σ z) hinv hS
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ
  set P : ℂ := ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) with hPdef
  set K : ℂ := kFac F σ * (omegaFactor 𝔞 : ℂ) with hKdef
  have hper : ∀ c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
      ∑' a : {a : F // a ∈ latM 𝔞}, eisTerm 2 σ z (a.1, c.out.1) =
        K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1 := by
    intro c
    have hb : c.out.1 ≠ 0 := c.out.2.2
    obtain ⟨hfs, hP⟩ := _root_.GlobalTheory.HeckeTwoPoisson.poisson F 𝔞 σ hσ z hz c.out.1 hb
    simp_rw [eisTerm_eq_kFac]
    rw [tsum_mul_left, hP.tsum_eq, split_zero _ _ hfs, fTerm_zero GlobalTheory.T.heckePhiFourierTransform_zero_eq σ hz hb]
    ring
  have hz2 := _root_.GlobalTheory.PartialZetaSum.hasSum_norm_cpow F 𝔟 Zb hZ (1 + 2 * σ) (by simp; linarith)
  rw [show -(1 + 2 * σ) = -1 - 2 * σ by ring] at hz2
  have hX := hz2.mul_left (K * P)
  have hT : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * P * ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-1 - 2 * σ) +
          K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) := by
    simpa only [hper] using hBs
  have hY : Summable (fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) =>
      K * ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1) :=
    (hT.sub hX.summable).congr fun c => by ring
  unfold eisSum eisClass
  rw [hsum, tsum_congr hper, hX.summable.tsum_add hY, hX.tsum_eq, tsum_mul_left]
  have hA : ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ z (c.out.1, 0) = aPart 𝔞 σ :=
    tsum_congr fun c => by simp [eisTerm, latPt]
  rw [hA]
  unfold gFun bZero bOne
  rw [if_neg hσ0]
  ring

end GlobalTheory.HeckeTwoEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCosetRepTranslatesOrthogonalStatement
section
open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCosetRepTranslates_orthogonal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    ∀ (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd (k := k) n d →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res (k := k) 1), T ≠ T' →
    ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0 := by
  exact @GlobalTheory.HeisUnit.tr_cosetRep_orth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCochainsHomologyAddEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCochains_homology_addEquiv_alt : ∀ (k : Type) [CommRing k] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Rep.{0} k G) [GroundTheory.ProfCoh.IsDiscreteRep M] (C : CosimplicialObject AddCommGrpCat.{1}) (e : ∀ m : ℕ, C.obj (SimplexCategory.mk m) →+ ((Fin (m + 1) → G) → M)), (∀ m, Function.Injective (e m)) → (∀ m (φ : (Fin (m + 1) → G) → M), (∃ c, e m c = φ) ↔ IsLocallyConstant φ ∧ ∀ (τ : G) (σ : Fin (m + 1) → G), φ (fun i ↦ τ * σ i) = M.ρ τ (φ σ)) → (∀ m (i : Fin (m + 2)) (c : C.obj (SimplexCategory.mk m)) (σ : Fin (m + 2) → G), e (m + 1) (C.δ i c) σ = e m c (σ ∘ i.succAbove)) → ∀ n : ℕ, Nonempty (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj C).homology n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  first | exact @GlobalTheory.homogeneousCochains_homology_addEquiv | exact GlobalTheory.homogeneousCochains_homology_addEquiv | (intros; apply GlobalTheory.homogeneousCochains_homology_addEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact : ∀ (R : Type) [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ), Function.Exact (cpush K f n) (cpush K (mappingCone.inr f) n) ∧ Function.Exact (cpush K (mappingCone.inr f) n) (cpost K (mappingCone.fst f) n (n + 1) rfl) ∧ Function.Exact (cpost K (mappingCone.fst f) n (n + 1) rfl) (cpush K f (n + 1)) := by
  first | (exact @GlobalTheory.EtC.coneSeqTgt_exact) | (exact GlobalTheory.EtC.coneSeqTgt_exact) | (intros; apply GlobalTheory.EtC.coneSeqTgt_exact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIso
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KInjPull

variable {C : Type*} [Category C] [Abelian C]

theorem cls_eq_zero_of_acyclic {A I : CochainComplex C ℤ} (hA : A.Acyclic) [I.IsKInjective] {n : ℤ}
    (z : Cocycle A I n) : CohomologyClass.mk z = 0 := by
  let g : A ⟶ I⟦n⟧ := Cocycle.homOf (z.rightShift n 0 (zero_add n))
  let H := IsKInjective.homotopyZero g hA
  have h1 : δ (-1) 0 (Cochain.ofHomotopy H) = (z.1.rightShift n 0 (zero_add n)) := by
    rw [δ_ofHomotopy, Cochain.ofHom_zero, sub_zero]
    have := Cocycle.ofHom_homOf_eq_self (z.rightShift n 0 (zero_add n))
    exact congrArg Subtype.val this
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (Cochain.ofHomotopy H).rightUnshift (n - 1) (by omega), ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift _ (n - 1) (by omega) n 0 (by omega), h1]
  simp [smul_smul]

end GlobalTheory.EtC.KInjPull

theorem GlobalTheory.EtC.cpull_bijective_of_quasiIso : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (I : Cx R) [I.IsKInjective] (n : ℤ), Function.Bijective (cpull f I n) := by
  intro R _ K L f _ I _ n
  have hA := GlobalTheory.EtC.mappingCone_acyclic R f
  have hz : ∀ m (x : CohomologyClass (mappingCone f) I m), x = 0 := by
    intro m x
    obtain ⟨z, rfl⟩ := x.mk_surjective
    exact KInjPull.cls_eq_zero_of_acyclic hA z
  obtain ⟨e1, e2, -⟩ := GlobalTheory.EtC.coneSeq_exact R f I n
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨w, rfl⟩ := (e1 x).1 hx
    rw [hz n w, map_zero]
  · exact (e2 y).1 (hz (n + 1) _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfTermwiseBijectStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective : ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) → ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L), (∀ p n, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) → ∀ n, Function.Bijective (cpull g I n) := by
  first | (exact @GlobalTheory.LevelCx.main) | (exact GlobalTheory.LevelCx.main) | (intros; apply GlobalTheory.LevelCx.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneFixerSumVanishesCuspidalCharacterGLFinStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperplaneFixerSumVanishes_cuspidalCharacterGLFiniteField : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k : ℕ, (2 ≤ m ∨ ¬ k ≡ 0 [MOD Nat.card F - 1]) → HFree (cusp θ m k) := by
  first | (exact @GlobalTheory.Shin.hFree_cusp) | (exact GlobalTheory.Shin.hFree_cusp) | (intros; apply GlobalTheory.Shin.hFree_cusp  <;> assumption)
end

