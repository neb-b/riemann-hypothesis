module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0353
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjEqOneOfPowEqOneOfSqZeroTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulUnramified

lemma eq_one_of_pow_eq_one_thick_affine (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (G : Over (Sp C)) [GrpObj G] (n : ℕ)
    (hn : IsUnit (n : C)) (R : CommRingCat.{0}) (g : Spec R ⟶ Sp C) (z : Over.mk g ⟶ G)
    (hz : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g), j ≫ z = 1)
    (hzn : z ^ n = 1) : z = 1 := by
  let φ : CommRingCat.of C ⟶ R := Spec.preimage g
  let K : Ideal C := RingHom.ker π
  let J : Ideal R := Ideal.map φ.hom K
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* R ⧸ J :=
    (Ideal.quotientMap J φ.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ∀ c, ψ (π c) = q (φ c) := by
    intro c
    have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk K c := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
    rfl
  have hJ : RingHom.ker q = J := Ideal.mk_ker
  have hJsq : J ^ 2 = ⊥ := by
    simp only [J, ← Ideal.map_pow]
    change Ideal.map φ.hom (RingHom.ker π ^ 2) = ⊥
    rw [hsq, Ideal.zero_eq_bot, Ideal.map_bot]
  let T₀ : Over (Sp C₀) := Over.mk (spMap ψ)
  have hw : Spec.map (CommRingCat.ofHom q) ≫ g = T₀.hom ≫ spMap π := by
    rw [← Spec.map_preimage g]
    simp only [T₀, spMap, Over.mk_hom, ← Spec.map_comp]
    congr 1
    ext c
    exact (hψ c).symm
  let j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g := Over.homMk (Spec.map (CommRingCat.ofHom q)) hw
  have hsurj : Function.Surjective j.left := by
    intro (p : PrimeSpectrum R)
    change p ∈ Set.range (PrimeSpectrum.comap q)
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 ∈ RingHom.ker q ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hJ, hJsq, Ideal.mem_bot] at this
    rw [this]
    exact zero_mem _
  have hker : RingHom.ker (CommRingCat.ofHom q).hom ^ 2 = ⊥ := by
    change RingHom.ker q ^ 2 = ⊥
    rw [hJ, hJsq]
  have hn' : IsUnit (n : Γ(Sp C, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  exact eq_one_of_pow_eq_one G j hsurj (mul_eq_zero_of_ker_sq (CommRingCat.ofHom q) hker) n hn' z
    (hz T₀ j) hzn

end GlobalTheory.MulUnramified

namespace GlobalTheory.MulUnramified

theorem eq_one_of_pow_eq_one_thick : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  intro C C₀ _ _ π hπ hsq G _ n hn T z hz hzn
  apply Over.OverMorphism.ext
  refine T.left.affineOpenCover.openCover.hom_ext _ _ fun i ↦ ?_
  let k : T.left.affineOpenCover.I₀ := i
  let f : Over.mk (T.left.affineOpenCover.f k ≫ T.hom) ⟶ T := Over.homMk (T.left.affineOpenCover.f k) rfl
  have hfz : (f ≫ z) ^ n = 1 := by
    rw [← MonObj.comp_pow, hzn, comp_one]
  have h := eq_one_of_pow_eq_one_thick_affine C C₀ π hπ hsq G n hn _ _ (f ≫ z)
    (fun T₀ j ↦ by rw [← Category.assoc]; exact hz T₀ _) hfz
  have h' := congrArg (·.left) (h.trans (comp_one f).symm)
  simp only [Over.comp_left] at h'
  exact h'

end GlobalTheory.MulUnramified
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GrpTangentPt

variable {S : Scheme.{0}} {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)

def sqZeroMapPt {M N : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N] (l : M →ₗ[R'] N) :
    Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' N)) ≫ x) ⟶
      Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' M)) ≫ x) :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (TrivSqZeroExt.map l).comp_algebraMap)

lemma sqZeroMapPt_comp {M N P : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
    [AddCommGroup P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]
    (l : M →ₗ[R'] N) (l' : N →ₗ[R'] P) :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = sqZeroMapPt x (l' ∘ₗ l) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

abbrev epsScalePt (c : R') : epsPtR x ⟶ epsPtR x := sqZeroMapPt x (c • (LinearMap.id : R' →ₗ[R'] R'))

lemma epsScalePt_left (c : R') : (epsScalePt x c).left = spMap (epsScaleR c) := rfl

lemma sqZeroMapPt_comp_eq {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M]
    [IsCentralScalar R' M] (l : R' →ₗ[R'] M) (l' : M →ₗ[R'] R') :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = epsScalePt x (l' (l 1)) := by
  rw [sqZeroMapPt_comp]
  congr 1
  refine LinearMap.ext_ring ?_
  simp

lemma epsScalePt_one : epsScalePt x (1 : R') = 𝟙 _ := by
  ext1
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

variable {G : Over S} [GrpObj G]

lemma epsScalePt_zero_comp {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x 0 ≫ w = 1 := by
  let π : epsPtR x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R' (DualNumber R'))) rfl
  have e : (1 : epsPtR x ⟶ G) = π ≫ (1 : Over.mk x ⟶ G) := (comp_one π).symm
  rw [e]
  ext1
  rw [Over.comp_left, Over.comp_left, ← hw, ← Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem epsScalePt_add_comp (a b : R') {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x (a + b) ≫ w = (epsScalePt x a ≫ w) * (epsScalePt x b ≫ w) := by
  let i₁ := LinearMap.inl R' R' R'
  let i₂ := LinearMap.inr R' R' R'
  have key : sqZeroMapPt x (i₁ + i₂) ≫ w = (sqZeroMapPt x i₁ ≫ w) * (sqZeroMapPt x i₂ ≫ w) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R' R' R')).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom
        (fun z => ⟨1, one_pos, TrivSqZeroExt.map i₁ z, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
  have := congrArg (sqZeroMapPt x (a • LinearMap.fst R' R' R' + b • LinearMap.snd R' R' R') ≫ ·) key
  simp only [comp_mul, ← Category.assoc, sqZeroMapPt_comp_eq] at this
  simpa [i₁, i₂] using this

theorem tanadd : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)
    (w : epsPtR x ⟶ G), spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left →
    ∀ (a b : R') (wa wb : epsPtR x ⟶ G), wa.left = spMap (epsScaleR a) ≫ w.left →
      wb.left = spMap (epsScaleR b) ≫ w.left → (wa * wb).left = spMap (epsScaleR (a + b)) ≫ w.left := by
  intro S G _ R' _ x w hw a b wa wb ha hb
  have ea : wa = epsScalePt x a ≫ w := Over.OverMorphism.ext ha
  have eb : wb = epsScalePt x b ≫ w := Over.OverMorphism.ext hb
  rw [ea, eb, ← epsScalePt_add_comp x a b hw]
  rfl

end GlobalTheory.GrpTangentPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorOrderTraceFormNondegenerate
section
open NumberField
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HTOrderTrace

theorem trace_tmul_padic {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (z : ℤ_[p]) (a : R) :
    Algebra.trace ℤ_[p] (ℤ_[p] ⊗[ℤ] R) (z ⊗ₜ a) = (Algebra.trace ℤ R a : ℤ_[p]) * z := by
  have h1 : (z ⊗ₜ a : ℤ_[p] ⊗[ℤ] R) = z • (1 ⊗ₜ a) := by simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul ℤ_[p] (ℤ_[p] ⊗[ℤ] R) (1 ⊗ₜ a) =
      (Algebra.lmul ℤ R a).baseChange ℤ_[p] := by
    ext c
    simp
  rw [h1, map_smul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, smul_eq_mul, mul_comm]
  rfl

theorem trace_form_padic_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (u : ℤ_[p] ⊗[ℤ] 𝓞 E),
    (∀ w, Algebra.trace ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) (u * w) = 0) → u = 0 := by
  intro E _ _ p _ u hu
  classical
  let b0 := RingOfIntegers.basis E
  let b1 := b0.baseChange ℤ_[p]
  have h1 : Algebra.discr ℤ_[p] b1 = (NumberField.discr E : ℤ_[p]) := by
    rw [NumberField.discr, Algebra.discr_def, Algebra.discr_def]
    rw [show ((Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).det : ℤ_[p]) =
      Int.castRingHom ℤ_[p] (Algebra.traceMatrix ℤ (RingOfIntegers.basis E)).det from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp [b1, b0, Algebra.traceForm_apply, trace_tmul_padic]
  have h0 : (NumberField.discr E : ℤ_[p]) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
  have hnd : (Algebra.traceForm ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)).Nondegenerate := by
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b1]
    have : LinearMap.BilinForm.toMatrix b1 (Algebra.traceForm ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)) =
        Algebra.traceMatrix ℤ_[p] b1 := by
      ext i j; simp [Algebra.traceMatrix_apply]
    rw [this, ← Algebra.discr_def, h1]; exact h0
  exact hnd.1 u (fun w => by simpa [Algebra.traceForm_apply] using hu w)

theorem ringHom_padic_eq_algebraMap : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [Ring B] [Algebra ℤ_[p] B] [Module.Free ℤ_[p] B]
    (f : ℤ_[p] →+* B), f = algebraMap ℤ_[p] B := by
  intro p _ B _ _ _ f
  ext c
  rw [← sub_eq_zero]
  set b := Module.Free.chooseBasis ℤ_[p] B
  have hdiv : ∀ n : ℕ, ∃ v : B, f c - algebraMap ℤ_[p] B c = (p : ℤ_[p]) ^ n • v := by
    intro n
    obtain ⟨μ, hμ⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n c)
    have hc : c = (c.appr n : ℤ_[p]) + (p : ℤ_[p]) ^ n * μ := by rw [← hμ]; ring
    refine ⟨f μ - algebraMap ℤ_[p] B μ, ?_⟩
    conv_lhs => rw [hc]
    rw [smul_sub, Algebra.smul_def, Algebra.smul_def, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow,
      map_natCast, map_natCast, map_natCast, map_natCast]
    noncomm_ring
  apply b.repr.injective
  ext i
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  obtain ⟨v, hv⟩ := hdiv ((b.repr (f c - algebraMap ℤ_[p] B c) i).valuation + 1)
  have hmem : b.repr (f c - algebraMap ℤ_[p] B c) i ∈
      Ideal.span {(p : ℤ_[p]) ^ ((b.repr (f c - algebraMap ℤ_[p] B c) i).valuation + 1)} := by
    rw [Ideal.mem_span_singleton]
    conv_rhs => rw [hv]
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have hne' : b.repr (f c - algebraMap ℤ_[p] B c) i ≠ 0 := by
    intro h
    apply hne
    rw [h]
  have := (PadicInt.mem_span_pow_iff_le_valuation _ hne' _).1 hmem
  omega

theorem matrix_basis_repr {ι R A : Type} [CommRing R] [AddCommGroup A] [Module R A] (m : ℕ) (b : Module.Basis ι R A)
    (M : Matrix (Fin m) (Fin m) A) (i j : Fin m) (k : ι) :
    (b.matrix (Fin m) (Fin m)).repr M (i, j, k) = b.repr (M i j) k := by
  simp only [Module.Basis.matrix, Module.Basis.map_repr, Module.Basis.repr_reindex_apply, LinearEquiv.trans_apply]
  rfl

theorem trace_mulLeft_matrix_eq : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (m : ℕ) (Z : Matrix (Fin m) (Fin m) A),
    LinearMap.trace R (Matrix (Fin m) (Fin m) A) (LinearMap.mulLeft R Z) = (m : R) * Algebra.trace R A Z.trace := by
  intro R A _ _ _ _ _ m Z
  classical
  let b := Module.Free.chooseBasis R A
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.trace_eq_matrix_trace R (b.matrix (Fin m) (Fin m)), Matrix.trace, Matrix.trace, map_sum,
    Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have key : ∀ j : Fin m, ∑ k, ((LinearMap.toMatrix (b.matrix (Fin m) (Fin m)) (b.matrix (Fin m) (Fin m)))
      (LinearMap.mulLeft R Z)).diag (i, j, k) = ∑ k, ((Algebra.leftMulMatrix b) (Z.diag i)).diag k := by
    intro j
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [LinearMap.toMatrix_apply, matrix_basis_repr, Algebra.leftMulMatrix_eq_repr_mul, Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem trace_mulLeft_baseChange_eq_zero : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (R : Type) [CommRing R] (x : O),
    (∀ y, LinearMap.trace ℤ O (LinearMap.mulLeft ℤ (x * y)) = 0) →
    ∀ Y : R ⊗[ℤ] O, LinearMap.trace R (R ⊗[ℤ] O) (LinearMap.mulLeft R ((1 ⊗ₜ x) * Y)) = 0 := by
  intro O _ _ _ R _ x hx Y
  have hb : ∀ z : O, LinearMap.mulLeft R ((1 : R) ⊗ₜ[ℤ] z) = (LinearMap.mulLeft ℤ z).baseChange R := by
    intro z; ext c w; simp
  induction Y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb' =>
    rw [mul_add, show LinearMap.mulLeft R ((1 ⊗ₜ x) * a + (1 ⊗ₜ x) * b) =
      LinearMap.mulLeft R ((1 ⊗ₜ x) * a) + LinearMap.mulLeft R ((1 ⊗ₜ x) * b) from
      map_add (LinearMap.mul R (R ⊗[ℤ] O)) _ _, map_add, ha, hb', add_zero]
  | tmul r y =>
    have h1 : ((1 : R) ⊗ₜ[ℤ] x) * (r ⊗ₜ y) = r • ((1 : R) ⊗ₜ[ℤ] (x * y)) := by
      simp [TensorProduct.smul_tmul']
    rw [h1, show LinearMap.mulLeft R (r • ((1 : R) ⊗ₜ[ℤ] (x * y))) =
      r • LinearMap.mulLeft R ((1 : R) ⊗ₜ[ℤ] (x * y)) from
      map_smul (LinearMap.mul R (R ⊗[ℤ] O)) _ _, map_smul, hb, LinearMap.trace_baseChange, hx, map_zero, smul_zero]

theorem inj_tmul (p : ℕ) [Fact p.Prime] (O : Type) [Ring O] [Module.Free ℤ O] (x : O)
    (h : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = 0) : x = 0 := by
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ ℤ_[p]) (RingHom.injective_int (algebraMap ℤ ℤ_[p]))
  have h1 : (Algebra.linearMap ℤ ℤ_[p]).rTensor O ((1 : ℤ) ⊗ₜ x) = 0 := by simpa using h
  have h2 := hinj (h1.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid ℤ O) h2

theorem trace_order_nondeg : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O),
    (∀ y : D.O, LinearMap.trace ℤ D.O (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  intro p _ D x hx
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨φ⟩ := D.splitP
  set A' := ℤ_[p] ⊗[ℤ] 𝓞 D.F
  let Φ : (ℤ_[p] ⊗[ℤ] D.O) ≃+* Matrix (Fin D.m) (Fin D.m) A' :=
    (Algebra.TensorProduct.comm ℤ ℤ_[p] D.O).toRingEquiv.trans
      (φ.toRingEquiv.trans (Algebra.TensorProduct.comm ℤ (𝓞 D.F) ℤ_[p]).toRingEquiv.mapMatrix)
  have hψ : Φ.toRingHom.comp (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] D.O)) =
      algebraMap ℤ_[p] (Matrix (Fin D.m) (Fin D.m) A') := ringHom_padic_eq_algebraMap p _ _
  have hΦs : ∀ (c : ℤ_[p]) (X : ℤ_[p] ⊗[ℤ] D.O), Φ (c • X) = c • Φ X := by
    intro c X
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
    exact congrArg (fun f => f c) hψ
  let e : (ℤ_[p] ⊗[ℤ] D.O) ≃ₗ[ℤ_[p]] Matrix (Fin D.m) (Fin D.m) A' :=
    { Φ.toAddEquiv with map_smul' := hΦs }
  have hconj : ∀ W : ℤ_[p] ⊗[ℤ] D.O, LinearMap.mulLeft ℤ_[p] (Φ W) = e.conj (LinearMap.mulLeft ℤ_[p] W) := by
    intro W
    ext V
    simp [LinearEquiv.conj_apply, e]
  set Z := Φ (1 ⊗ₜ x)
  have hZ : ∀ Y, Algebra.trace ℤ_[p] A' (Z * Y).trace = 0 := by
    intro Y
    have h1 := trace_mulLeft_baseChange_eq_zero D.O ℤ_[p] x hx (Φ.symm Y)
    rw [← LinearMap.trace_conj' _ e, ← hconj, map_mul, RingEquiv.apply_symm_apply, trace_mulLeft_matrix_eq] at h1
    have hm : (D.m : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 D.m_pos.ne'
    exact (mul_eq_zero.1 h1).resolve_left hm
  have hZ0 : Z = 0 := by
    ext i j
    apply trace_form_padic_eq_zero D.F p
    intro a
    have := hZ (Matrix.single j i a)
    rwa [Matrix.trace_mul_single, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at this
  have h1 : (1 : ℤ_[p]) ⊗ₜ[ℤ] x = 0 := by
    rw [← map_eq_zero_iff Φ Φ.injective]; exact hZ0
  exact inj_tmul p D.O x h1

end GlobalTheory.HTOrderTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditive
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.PostFun

variable {R : Type} [CommRing R]

theorem post_eq_cpush (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) :
    HK.post R K φ n = cpush K (resMap R φ) n := rfl

def resMapIdHomotopy (F : Shv R) : Homotopy (resMap R (𝟙 F)) (𝟙 (res R F)) := by
  have H2 := (InjectiveResolution.descIdHomotopy F (injectiveResolution F)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_id] at H2
  exact H2

def resMapCompHomotopy {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) :
    Homotopy (resMap R (φ ≫ ψ)) (resMap R φ ≫ resMap R ψ) := by
  have H2 := (InjectiveResolution.descCompHomotopy φ ψ (injectiveResolution F) (injectiveResolution G)
    (injectiveResolution M)).extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp] at H2
  exact H2

def resMapAddHomotopy {F G : Shv R} (φ ψ : F ⟶ G) :
    Homotopy (resMap R (φ + ψ)) (resMap R φ + resMap R ψ) := by
  have H : Homotopy (InjectiveResolution.desc (φ + ψ) (injectiveResolution G) (injectiveResolution F))
      (InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F) +
        InjectiveResolution.desc ψ (injectiveResolution G) (injectiveResolution F)) := by
    apply InjectiveResolution.descHomotopy (φ + ψ)
    · simp
    · simp [Preadditive.comp_add, Preadditive.add_comp, Functor.map_add (f := _)]
  have H2 := H.extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_add] at H2
  exact H2

theorem cpush_add (K : Cx R) {I J : Cx R} (f g : I ⟶ J) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f + g) n x = cpush K f n x + cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
  rw [← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add, Cochain.comp_add]

theorem post_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.post R K (𝟙 F) n x = x := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapIdHomotopy F), InjResCmp.cpush_id]

theorem post_comp (K : Cx R) {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) (n : ℤ) (x : HK R K F n) :
    HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x) := by
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapCompHomotopy φ ψ), InjResCmp.cpush_comp]
  rfl

theorem post_add (K : Cx R) {F G : Shv R} (φ ψ : F ⟶ G) (n : ℤ) :
    HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n := by
  ext x
  rw [post_eq_cpush, InjResCmp.cpush_homotopy K (resMapAddHomotopy φ ψ), cpush_add]
  rfl

def postHom (K : Cx R) (F G : Shv R) (n : ℤ) : (F ⟶ G) →+ (HK R K F n →+ HK R K G n) :=
  AddMonoidHom.mk' (fun φ => HK.post R K φ n) (fun φ ψ => post_add K φ ψ n)

theorem post_zsmul (K : Cx R) {F G : Shv R} (φ : F ⟶ G) (c : ℤ) (n : ℤ) (x : HK R K F n) :
    HK.post R K (c • φ) n x = c • HK.post R K φ n x := by
  have h := map_zsmul (postHom K F G n) c φ
  exact DFunLike.congr_fun h x

theorem pull_post {K L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) (n : ℤ) (x : HK R K F n) :
    HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) :=
  ZcFun.cpull_cpush f (resMap R φ) n x

theorem main : ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ), (∀ (F : Shv R) x, HK.post R K (𝟙 F) n x = x) ∧ (∀ {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) x, HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x)) ∧ (∀ {F G : Shv R} (φ ψ : F ⟶ G), HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n) ∧ (∀ {F G : Shv R} (φ : F ⟶ G) (c : ℤ) x, HK.post R K (c • φ) n x = c • HK.post R K φ n x) ∧ ∀ {L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) x, HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) := by
  intro R _ K n
  exact ⟨fun F x => post_id K F n x, fun φ ψ x => post_comp K φ ψ n x, fun φ ψ => post_add K φ ψ n,
    fun φ c x => post_zsmul K φ c n x, fun f _ _ φ x => pull_post f φ n x⟩

end GlobalTheory.EtC.PostFun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureFiniteTypeOfCharZeroStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_finiteType_over_adjoin : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.FiniteType k B := by
  first | (exact @GlobalTheory.integralClosure_finiteType_of_charZero) | (exact GlobalTheory.integralClosure_finiteType_of_charZero) | (intros; apply GlobalTheory.integralClosure_finiteType_of_charZero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOverStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_eq_one_of_liesOver_height_one : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  first | (exact @GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (exact GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (intros; apply GlobalTheory.integralClosure_height_eq_one_of_liesOver  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightOneUniformizerRamificationAStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_ramification_of_height_one : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → ∀ t : A, Irreducible t → p = Ideal.span {t} → ∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → ∃ (s : B) (e : ℕ), 1 ≤ e ∧ s ∈ Q ∧ (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) ∧ (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) := by
  first | (exact @GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (exact GlobalTheory.integralClosure_height_one_uniformizer_ramification) | (intros; apply GlobalTheory.integralClosure_height_one_uniformizer_ramification  <;> assumption)
end

