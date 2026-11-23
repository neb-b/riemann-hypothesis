module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalSymplecticFixesSiegelPointI
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem holPart_eq_and_gaussian_of_orthogonal_symplectic (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (ho : sᵀ * s = 1) (hd : P.det ≠ 0) :
    GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ,
      cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) =
        cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  have hJ : s * J l ℝ = J l ℝ * s := by
    have h2 : s * J l ℝ * sᵀ = J l ℝ := SymplecticGroup.mem_iff.mp hs
    calc s * J l ℝ = s * J l ℝ * (sᵀ * s) := by rw [ho, Matrix.mul_one]
      _ = (s * J l ℝ * sᵀ) * s := by simp only [Matrix.mul_assoc]
      _ = J l ℝ * s := by rw [h2]
  have e1 : ∀ a b, s (.inl a) (.inr b) = - s (.inr a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inl b)
    simpa [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have e2 : ∀ a b, s (.inr a) (.inr b) = s (.inl a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inr b)
    simp [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at this
    linarith
  have hh : GlobalTheory.Published.Metaplectic.holPart s = P := by
    ext a b
    simp only [GlobalTheory.Published.Metaplectic.holPart, hP, e2, e1]
    push_cast; ring
  have hQP : Q = (-I) • P := by
    ext a b
    simp only [hP, hQ, e2, e1, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring_nf; rw [I_sq]; ring
  have hinv : -(Q * P⁻¹) = I • (1 : Matrix l l ℂ) := by
    rw [hQP, Matrix.smul_mul, mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hd), neg_smul, neg_neg]
  refine ⟨hh, fun x => ?_⟩
  rw [hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct]
  push_cast
  ring_nf; rw [I_sq]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterFunctionEqZeroOfComposable
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_composable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (l m : Λ) (q : Tot I g) (hq : q.1 ∈ F.V) :
    ∃ k k' k'' : K.K, K.le l k' k ∧ K.le m k'' k' ∧ q ∈ K.W k'' := by
  obtain ⟨hcov, hjoin⟩ := hK
  obtain ⟨k, hk⟩ := hcov (F.shift l (F.shift m q)) hq
  obtain ⟨k₁, hk₁⟩ := hcov (F.shift m q) hq
  obtain ⟨k', hk', -, hlk⟩ := hjoin l k₁ k (F.shift m q) hk₁ hk
  obtain ⟨k₂, hk₂⟩ := hcov q hq
  obtain ⟨k'', hk'', -, hmk⟩ := hjoin m k₂ k' q hk₂ hk'
  exact ⟨k, k', k'', hlk, hmk, hk''⟩

theorem eq_zero_of_cst_composable : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (l m : Λ) (p : Hol F.V),
    (∀ (k k' k'' : K.K), K.le l k' k → K.le m k'' k' → K.cst k'' p = 0) → p = 0 := by
  intro I _ g Λ _ F K hK l m p hp
  apply Hol.ext_fn
  intro z hz
  obtain ⟨k, k', k'', h1, h2, hq⟩ := exists_composable K hK l m ((z, 0) : Tot I g) hz
  have h : (K.cst k'' p).fn ((z, 0) : Tot I g) = (0 : Hol (K.W k'')).fn ((z, 0) : Tot I g) := by
    rw [hp k k' k'' h1 h2]
  rw [fn_cst K k'' p hq, show (0 : Hol (K.W k'')) = algebraMap ℂ _ 0 from (map_zero _).symm,
    Hol.fn_algebraMap _ hq] at h
  rw [show (0 : Hol F.V) = algebraMap ℂ _ 0 from (map_zero _).symm, Hol.fn_algebraMap _ hz]
  exact h

end GlobalTheory.AnPer.Charts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialOperatorSchwartzSeminormBound
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceOpDecay

theorem norm_le_max_comp {V : Type} [NormedAddCommGroup V] {κ κ₁' : Type} [Fintype κ] [Fintype κ₁']
    (z : κ ⊕ κ₁' → V) : ‖z‖ ≤ max ‖z ∘ Sum.inl‖ ‖z ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i => ?_
  cases i with
  | inl i => exact (norm_le_pi_norm (z ∘ Sum.inl) i).trans (le_max_left _ _)
  | inr j => exact (norm_le_pi_norm (z ∘ Sum.inr) j).trans (le_max_right _ _)

theorem pow_norm_le_add {V : Type} [NormedAddCommGroup V] {κ κ₁' : Type} [Fintype κ] [Fintype κ₁']
    (z : κ ⊕ κ₁' → V) (k : ℕ) : ‖z‖ ^ k ≤ ‖z ∘ Sum.inl‖ ^ k + ‖z ∘ Sum.inr‖ ^ k := by
  have h := pow_le_pow_left₀ (norm_nonneg z) (norm_le_max_comp z) k
  rcases le_total ‖z ∘ Sum.inl‖ ‖z ∘ Sum.inr‖ with hle | hle
  · rw [max_eq_right hle] at h; linarith [pow_nonneg (norm_nonneg (z ∘ Sum.inl)) k]
  · rw [max_eq_left hle] at h; linarith [pow_nonneg (norm_nonneg (z ∘ Sum.inr)) k]

theorem decay (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (z : κ ⊕ κ₁' → V),
      ‖z‖ ^ k * ‖qOp P f z‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ) f := by
  obtain ⟨s1, C1, hC1, h1⟩ := clm_sup_bound P {(k, 0)}
  obtain ⟨s2, C2, hC2, h2⟩ := clm_sup_bound P {(0, 0)}
  let sh : ℕ × ℕ → ℕ × ℕ := fun i => (k + i.1, i.2)
  refine ⟨s1 ∪ s2.image sh, C1 + C2, add_nonneg hC1 hC2, fun f z => ?_⟩
  set F := schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ
  set x := z ∘ Sum.inl
  set y := z ∘ Sum.inr
  set g := sliceR f x
  have hq : qOp P f z = P g y := rfl
  set S := (s1 ∪ s2.image sh).sup F f
  have hS0 : 0 ≤ S := apply_nonneg _ _

  have hy : ‖y‖ ^ k * ‖P g y‖ ≤ C1 * S := by
    have a1 : ‖y‖ ^ k * ‖P g y‖ ≤ SchwartzMap.seminorm ℂ k 0 (P g) := by
      have := SchwartzMap.le_seminorm ℂ k 0 (P g) y
      simpa [norm_iteratedFDeriv_zero] using this
    have a2 := h1 g
    simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] at a2
    have a3 : s1.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g ≤ S := by
      refine Seminorm.finset_sup_apply_le hS0 fun i hi => ?_
      have w := GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' f 0 i.1 i.2 x
      simp only [pow_zero, one_mul, zero_add] at w
      refine le_trans (b := SchwartzMap.seminorm ℂ _ _ f) w ?_
      have : F i f ≤ S := Seminorm.le_finset_sup_apply (Finset.mem_union_left _ hi)
      exact this
    calc _ ≤ _ := a1
      _ ≤ _ := a2
      _ ≤ C1 * S := by gcongr

  have hx : ‖x‖ ^ k * ‖P g y‖ ≤ C2 * S := by
    have a1 : ‖P g y‖ ≤ SchwartzMap.seminorm ℂ 0 0 (P g) := SchwartzMap.norm_le_seminorm ℂ (P g) y
    have a2 := h2 g
    simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] at a2
    have a3 : ‖x‖ ^ k * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g ≤ S := by
      have e : ‖x‖ ^ k * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g
          = s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) (((‖x‖ ^ k : ℝ) : ℂ) • g) := by
        rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      rw [e]
      refine Seminorm.finset_sup_apply_le hS0 fun i hi => ?_
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      have w := GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' f k i.1 i.2 x
      refine le_trans (b := SchwartzMap.seminorm ℂ _ _ f) w ?_
      have : F (sh i) f ≤ S :=
        Seminorm.le_finset_sup_apply (Finset.mem_union_right _ (Finset.mem_image_of_mem sh hi))
      simpa [F, sh, SchwartzMap.schwartzSeminormFamily_apply] using this
    calc ‖x‖ ^ k * ‖P g y‖ ≤ ‖x‖ ^ k * (C2 * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g) := by
          gcongr; exact a1.trans a2
      _ = C2 * (‖x‖ ^ k * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g) := by ring
      _ ≤ C2 * S := by gcongr
  rw [hq]
  calc ‖z‖ ^ k * ‖P g y‖ ≤ (‖x‖ ^ k + ‖y‖ ^ k) * ‖P g y‖ := by
        gcongr; exact pow_norm_le_add z k
    _ = ‖x‖ ^ k * ‖P g y‖ + ‖y‖ ^ k * ‖P g y‖ := by ring
    _ ≤ C2 * S + C1 * S := add_le_add hx hy
    _ = (C1 + C2) * S := by ring

end GlobalTheory.SliceOpDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardTorsionTrivialOfTorsorsHaveSections
section
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerStep

open GlobalTheory.KummerAlg

theorem p1 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), 0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := _root_.GlobalTheory.KummerAlg.finite_projective_faithfullyFlat
theorem p2 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective
theorem p4 : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 → ∃ φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => CommRing.Pic.AsModule c) B, ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := GlobalTheory.T.exists_multilinear_form_of_pic_torsion

theorem free_of_section (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B) (hq : 0 < q)
    (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p)
    (s : Alg φ →ₐ[B] B) : Module.Free B L := by
  let f : L →ₗ[B] B := s.toLinearMap ∘ₗ gen φ
  have hf : ∀ e : L, f e ^ q = φ (fun _ => e) := fun e => by
    have := congrArg s (prod_gen φ (fun _ => e))
    simpa [f, map_prod, Finset.prod_const, AlgHom.commutes] using this
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (LinearMap.range f) h
    obtain ⟨e, he⟩ := hφ m hm.isPrime
    apply he
    rw [← hf e]
    exact Ideal.pow_mem_of_mem _ (hle ⟨e, rfl⟩) q hq
  exact Module.Free.of_equiv
    (LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hsurj)).symm

theorem kummer_step : ∀ (B : Type) [CommRing B] (q : ℕ), 0 < q → IsUnit (q : B) →
    (∃ ζ : B, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) →
    (∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
      Module.FaithfullyFlat B D → ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
      Function.Bijective (Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) → Nonempty (D →ₐ[B] B)) →
    ∀ c : CommRing.Pic B, c ^ q = 1 → c = 1 := by
  intro B _ q hq hqu ⟨ζ, hζ, hζk⟩ hT c hc
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨φ, hφ⟩ := p4 B q c hc
  obtain ⟨hfin, hproj, hff⟩ := p1 B (CommRing.Pic.AsModule c) q φ hq hφ
  obtain ⟨s⟩ := hT (Alg φ) hfin hproj hff (act φ ζ hζ) (p2 B (CommRing.Pic.AsModule c) q φ hqu hφ ζ hζ hζk)
  have := free_of_section B (CommRing.Pic.AsModule c) q φ hq hφ s
  rw [← CommRing.Pic.mk_eq_self (M := c), CommRing.Pic.mk_eq_one_iff_free]
  exact this

end GlobalTheory.KummerStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulMemSubalgebraOfResBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub.PowerMultiple

variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

theorem res_pow_mul_mem_gen
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {D W V : X.Opens} (hD : IsAffineOpen D) (hDW : D ≤ W) (hDV : D ≤ V)
    (T : Set (F.obj (op V))) (f : Γ(X, W)) (a : F.obj (op W))
    (ha : ∀ (W' : X.Opens), IsAffineOpen W' → ∀ (h1 : W' ≤ X.basicOpen f) (h2 : W' ≤ V),
      (F.map (homOfLE h1).op).hom ((F.map (homOfLE (X.basicOpen_le f)).op).hom a) ∈
        gen F α h2 T) :
    ∃ m : ℕ, (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f ^ m * a) ∈ gen F α hDV T := by
  set fD : Γ(X, D) := (X.presheaf.map (homOfLE hDW).op).hom f with hfD
  have hbo : X.basicOpen fD = D ⊓ X.basicOpen f := Scheme.basicOpen_res X f (homOfLE hDW).op
  have hD'D : X.basicOpen fD ≤ D := X.basicOpen_le fD
  have hD'f : X.basicOpen fD ≤ X.basicOpen f := hbo.le.trans inf_le_right
  have hD'V : X.basicOpen fD ≤ V := hD'D.trans hDV
  have hD' : IsAffineOpen (X.basicOpen fD) := hD.basicOpen fD
  letI iRA : Algebra Γ(X, D) (F.obj (op D)) := (α.app (op D)).hom.toAlgebra
  letI iRR' : Algebra Γ(X, D) Γ(X, X.basicOpen fD) :=
    (X.presheaf.map (homOfLE hD'D).op).hom.toAlgebra
  letI iR'A' : Algebra Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) :=
    (α.app (op (X.basicOpen fD))).hom.toAlgebra
  letI iAA' : Algebra (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    (F.map (homOfLE hD'D).op).hom.toAlgebra
  letI iRA' : Algebra Γ(X, D) (F.obj (op (X.basicOpen fD))) :=
    ((F.map (homOfLE hD'D).op).hom.comp (α.app (op D)).hom).toAlgebra
  haveI : IsScalarTower Γ(X, D) (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(X, D) Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have := congr($(α.naturality (homOfLE hD'D).op).hom r)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  haveI : IsLocalization.Away fD Γ(X, X.basicOpen fD) := hD.isLocalization_basicOpen fD
  haveI : IsLocalization.Away (algebraMap Γ(X, D) (F.obj (op D)) fD)
      (F.obj (op (X.basicOpen fD))) := isLocalizationAway F α hα hD fD
  have hres : ∀ {U₁ U₂ U₃ : X.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂).op).hom ((F.map (homOfLE h₁).op).hom y) =
        (F.map (homOfLE (h₂.trans h₁)).op).hom y := by
    intro U₁ U₂ U₃ h₁ h₂ y
    rw [← CommRingCat.comp_apply, ← F.map_comp]
    rfl
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway (R := Γ(X, D)) (A := F.obj (op D))
    (R' := Γ(X, X.basicOpen fD)) (A' := F.obj (op (X.basicOpen fD))) fD
    ((F.map (homOfLE hDV).op).hom '' T) ((F.map (homOfLE hDW).op).hom a) (by
      have h0 := ha _ hD' hD'f hD'V
      rw [hres, gen_eq_adjoin] at h0
      change (F.map (homOfLE hD'D).op).hom ((F.map (homOfLE hDW).op).hom a) ∈ _
      rw [hres, Set.image_image]
      have hfun : (fun x => (algebraMap (F.obj (op D)) (F.obj (op (X.basicOpen fD))))
          ((F.map (homOfLE hDV).op).hom x)) = ⇑(F.map (homOfLE hD'V).op).hom :=
        funext fun x => hres _ _ x
      rw [hfun]
      exact h0)
  refine ⟨m, ?_⟩
  have hnat : (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f) = (α.app (op D)).hom fD := by
    have := congr($(α.naturality (homOfLE hDW).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  rw [map_mul, map_pow, hnat, gen_eq_adjoin]
  exact hm

end GlobalTheory.QcSub.PowerMultiple

theorem GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  intro X hX F α hα ι _ V hV T W hW f a ha
  classical
  haveI := Fintype.ofFinite ι
  rw [mem_sub] at ha
  choose s hs1 hs2 using fun j => _root_.GlobalTheory.affine_inter_finite_basicOpen_cover X hX W (V j) hW (hV j)
  have hle : ∀ j, ∀ h ∈ s j, X.basicOpen h ≤ V j := by
    intro j h hh
    obtain ⟨r, hr⟩ := hs1 j h hh
    rw [hr]
    exact X.basicOpen_le r
  choose m hm using fun j (h : s j) =>
    GlobalTheory.QcSub.PowerMultiple.res_pow_mul_mem_gen F α hα (hW.basicOpen h.1) (X.basicOpen_le h.1)
      (hle j h.1 h.2) (T j) f a (fun W' hW' h1 h2 => ha j W' hW' h1 h2)
  refine ⟨∑ j, ∑ h : s j, m j h, ?_⟩
  rw [mem_sub]
  intro j W' hW' hWW' hWV
  refine GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) W (T j) _ ?_ W' hW' hWW' hWV
  intro x hx
  have hx' := hs2 j hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx'
  obtain ⟨h, hh, hxh⟩ := hx'
  refine ⟨X.basicOpen h, hW.basicOpen h, hxh, X.basicOpen_le h, hle j h hh, ?_⟩
  have hmle : m j ⟨h, hh⟩ ≤ ∑ j, ∑ h : s j, m j h :=
    le_trans (Finset.single_le_sum (f := fun h' => m j h') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨h, hh⟩ : s j)))
      (Finset.single_le_sum (f := fun j' => ∑ h' : s j', m j' h') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j))
  rw [show ∑ j, ∑ h : s j, m j h = (∑ j, ∑ h : s j, m j h - m j ⟨h, hh⟩) + m j ⟨h, hh⟩ by omega,
    pow_add, mul_assoc, map_mul]
  refine mul_mem ?_ (hm j ⟨h, hh⟩)
  rw [map_pow]
  refine pow_mem ?_ _
  have := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom f)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickening
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SecGlue

theorem preimage_eq_of_comp_eq_of_sqZero : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T),
    Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens,
      u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  intro S T _ _ q hq hsq Y u w huw V
  have hsurj : Function.Surjective (spMap q).base := by
    intro p
    have hker : RingHom.ker q ≤ p.asIdeal := by
      intro x hx
      have hx2 : x * x ∈ RingHom.ker q ^ 2 := by
        rw [sq]; exact Ideal.mul_mem_mul hx hx
      rw [hsq, Ideal.mem_bot] at hx2
      exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
    haveI := p.isPrime
    haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
    refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
    intro x hx
    exact hker (by simpa [RingHom.mem_ker] using hx)
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage,
    ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, huw]

end GlobalTheory.SecGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleFibreStandardEtaleSpreads
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preirreducibleSpace_of_continuous_surjective_fibreChart {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [hX : PreirreducibleSpace X] (f : X → Y) (hf : Continuous f)
    (hs : Function.Surjective f) : PreirreducibleSpace Y :=
  ⟨by simpa [Set.image_univ_of_surjective hs] using
    hX.isPreirreducible_univ.image f hf.continuousOn⟩

theorem preirreducibleSpace_tensor_congr_fibreChart (A B C k : Type) [CommRing A] [CommRing B]
    [CommRing C] [CommRing k] [Algebra A B] [Algebra A C] [Algebra A k] (e : B ≃ₐ[A] C) :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) ↔ PreirreducibleSpace (PrimeSpectrum (k ⊗[A] C)) := by
  let E : k ⊗[A] B ≃ₐ[A] k ⊗[A] C := Algebra.TensorProduct.congr AlgEquiv.refl e
  let H := PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv
  constructor
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H H.continuous H.surjective
  · intro h
    exact preirreducibleSpace_of_continuous_surjective_fibreChart H.symm H.symm.continuous
      H.symm.surjective

theorem preirreducibleSpace_fibre_standardEtale_spreads :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B] [IsScalarTower A (MvPolynomial (Fin n) A) B], Algebra.IsStandardEtale (MvPolynomial (Fin n) A) B → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (a : A) (I : Finset A), algebraMap A Ω a ≠ 0 ∧ (∀ c ∈ I, algebraMap A Ω c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra A k], algebraMap A k a ≠ 0 → (∀ c ∈ I, algebraMap A k c = 0) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) := by
  intro A B _ _ _ n _ _ hB Ω _ _ _ hΩ
  obtain ⟨f, g, hf, hd, ⟨e⟩⟩ := _root_.GlobalTheory.standardEtale_mvPolynomial_hypersurface A B n hB
  have hΩ' := (_root_.GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff A _ f g Ω).1 ((preirreducibleSpace_tensor_congr_fibreChart A _ _ Ω e).1 hΩ)
  obtain ⟨a, I, ha, hI, hk⟩ := _root_.GlobalTheory.hypersurface_part_preirreducible_spreads A (Option (Fin n)) f g none hf hd Ω (algebraMap A Ω) hΩ'
  refine ⟨a, I, ha, hI, ?_⟩
  intro k _ _ _ hak hIk
  exact (preirreducibleSpace_tensor_congr_fibreChart A _ _ k e).2
    ((_root_.GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff A _ f g k).2 (hk k (algebraMap A k) hak hIk))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMapFrobeniusPowStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F →+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (k : ℕ) (P : F[X]), rootSum θ k (P.map t) = rootSum θ (k * ringChar F ^ j) P := by
  first | (exact @GlobalTheory.Shin.rootSum_map_frobeniusPow) | (exact GlobalTheory.Shin.rootSum_map_frobeniusPow) | (intros; apply GlobalTheory.Shin.rootSum_map_frobeniusPow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMinpolyPowEqSumStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m l : ℕ) (α : AlgebraicClosure F), 0 < m → α ^ (Nat.card F ^ m - 1) = 1 → rootSum θ l (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a ∈ Finset.range m, θ α ^ (l * Nat.card F ^ a) := by
  first | (exact @GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum) | (exact GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum) | (intros; apply GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzProductDecompositionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_product_decomposition : ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → X) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ ⊕ κ' → X) →
    ∃ (ι : Type) (_ : Fintype ι) (g₁ : ι → (κ → X) → ℂ) (g₂ : ι → (κ' → X) → ℂ),
      (∀ i, g₁ i ∈ GlobalTheory.WeilM.SB (κ → X)) ∧ (∀ i, g₂ i ∈ GlobalTheory.WeilM.SB (κ' → X)) ∧
      g = ∑ i, fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr) := by
  first | exact @GlobalTheory.SBProd.exists_sum_box | exact GlobalTheory.SBProd.exists_sum_box | (intros; apply GlobalTheory.SBProd.exists_sum_box <;> assumption)
end

