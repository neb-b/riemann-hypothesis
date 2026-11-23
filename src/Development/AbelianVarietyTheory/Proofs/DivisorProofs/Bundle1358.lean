module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SesquilinearDetOrdSignOnKernelConjGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

theorem ordL_mul_of_ne [Valued K (WithZero (Multiplicative ℤ))] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]
  rw [this, toAdd_mul]
  ring

theorem sign_mul_norm [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {d : K} (hd : d ≠ 0) (x : K) :
    (-1 : ℂ) ^ ordL (σ d * d * x) = (-1 : ℂ) ^ ordL x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσd : σ d ≠ 0 := (map_ne_zero σ).2 hd
  have hσo : ordL (σ d) = ordL d := by
    unfold ordL
    simp only [hσ]
  rw [ordL_mul_of_ne (mul_ne_zero hσd hd) hx, ordL_mul_of_ne hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul,
    (even_two_mul (ordL d)).neg_one_zpow, one_mul]

theorem gram_eq_mul (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι]
    (v : ι → Fin n → K) :
    (Matrix.of fun i j => hform σ H (v i) (v j)) =
      cT σ (Matrix.of fun p i => v i p) * H * Matrix.of fun p i => v i p := by
  ext i j
  simp only [hform, cT, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem cols_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {ι : Type} (v : ι → Fin n → K) :
    (Matrix.of fun p i => (M *ᵥ v i) p) = M * Matrix.of fun p i => v i p := by
  ext p i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem det_cT (σ : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι K) :
    (cT σ T).det = σ T.det := by
  unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl

theorem gram_det_change (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (b b' : Module.Basis ι K W) :
    ∃ d : K, d ≠ 0 ∧
      (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
        σ d * d * (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set T := b.toMatrix b' with hT
  have hcol : (Matrix.of fun p i => (b' i : Fin n → K) p) = (Matrix.of fun p i => (b i : Fin n → K) p) * T := by
    ext p j
    have hs := congrArg (fun x : W => (x : Fin n → K) p) (b.sum_repr (b' j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    rw [Matrix.of_apply, ← hs, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.of_apply, hT, Module.Basis.toMatrix_apply, mul_comm]
  have hTT : T * b'.toMatrix b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b b'
  have hd : T.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hTT
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨T.det, hd, ?_⟩
  rw [gram_eq_mul σ H (fun i => (b' i : Fin n → K)), gram_eq_mul σ H (fun i => (b i : Fin n → K)), hcol,
    cT_mul]
  set B := Matrix.of fun p i => (b i : Fin n → K) p
  rw [show cT σ T * cT σ B * H * (B * T) = cT σ T * (cT σ B * H * B) * T by simp only [Matrix.mul_assoc]]
  simp only [Matrix.det_mul, det_cT]
  ring

theorem sign_basis [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b : Module.Basis ι K W) (b' : Module.Basis ι' K W) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b' i : Fin n → K) (b' j)).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).det := by
  set e : ι' ≃ ι := b'.indexEquiv b
  have hsub : (Matrix.of fun i j => hform σ H ((b.reindex e.symm) i : Fin n → K) ((b.reindex e.symm) j)) =
      (Matrix.of fun i j => hform σ H (b i : Fin n → K) (b j)).submatrix e e := by
    ext i j
    simp [Module.Basis.reindex_apply]
  obtain ⟨d, hd, hdet⟩ := gram_det_change σ H W (b.reindex e.symm) b'
  rw [hdet, sign_mul_norm σ hσ hd, hsub, Matrix.det_submatrix_equiv_self]

theorem aeval_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    aeval (k⁻¹ * a * k).val Q = (k⁻¹).val * aeval a.val Q * k.val := by
  have hp : ∀ i : ℕ, ((k⁻¹ * a * k : GL (Fin n) K).val) ^ i = (k⁻¹).val * a.val ^ i * k.val := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  simp only [hp, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.UnitaryClasses.SgnConj

namespace GlobalTheory.UnitaryClasses.SgnConj

variable {K : Type} [Field K]

theorem ker_conj {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) =
      (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).comap (Matrix.toLin' k.val) := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Matrix.toLin'_apply, aeval_conj]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (fun y => k.val *ᵥ y) h
    simpa [Matrix.mulVec_mulVec] using this
  · intro h
    rw [h, Matrix.mulVec_zero]

def invEquiv {n : ℕ} (k : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.toLin' (k⁻¹).val) (Matrix.toLin' k.val)
    (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])

theorem map_invEquiv {n : ℕ} (Q : K[X]) (a k : GL (Fin n) K) :
    (LinearMap.ker (Matrix.toLin' (aeval a.val Q))).map (invEquiv k : (Fin n → K) →ₗ[K] (Fin n → K)) =
      LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q)) := by
  rw [ker_conj, Submodule.map_equiv_eq_comap_symm]
  rfl

theorem sgnOn_conj : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K),
    sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := by
  intro K _ _ σ hσ n Q a k
  set V := LinearMap.ker (Matrix.toLin' (aeval a.val Q))
  set V' := LinearMap.ker (Matrix.toLin' (aeval (k⁻¹ * a * k).val Q))
  let b0 := Module.finBasis K V
  let b'' : Module.Basis (Fin (Module.finrank K V)) K V' :=
    b0.map ((invEquiv k).ofSubmodules V V' (map_invEquiv Q a k))
  have hb'' : ∀ i, (b'' i : Fin n → K) = (k⁻¹).val *ᵥ (b0 i : Fin n → K) := by
    intro i
    simp [b'', Module.Basis.map_apply, LinearEquiv.ofSubmodules_apply, invEquiv]
  unfold sgnOn gramOn
  rw [sign_basis σ hσ 1 V' b'' (Module.finBasis K V')]
  congr 3
  rw [gram_eq_mul σ 1 (fun i => (b'' i : Fin n → K)), gram_eq_mul σ _ (fun i => (b0 i : Fin n → K))]
  simp only [hb'']
  rw [cols_mulVec, cT_mul]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

end GlobalTheory.UnitaryClasses.SgnConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIsEtaleCompletion
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.RegSmooth

theorem spanFinrank_top_eq_finrank_residueField (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (⊤ : Submodule R M).spanFinrank = Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) := by
  rw [← TensorProduct.spanFinrank_top_eq_of_residueField (⊤ : Submodule R M) Module.Finite.fg_top,
    ← Module.finrank_eq_spanFinrank_of_free]
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ResidueField R) (ResidueField R))
    (Submodule.topEquiv (R := R) (M := M))).finrank_eq

theorem spanFinrank_top_tensor_eq {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] {N : Type*} [AddCommGroup N]
    [Module A N] [Module.Finite A N] :
    (⊤ : Submodule B (B ⊗[A] N)).spanFinrank = (⊤ : Submodule A N).spanFinrank := by
  rw [spanFinrank_top_eq_finrank_residueField, spanFinrank_top_eq_finrank_residueField]
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B)
    (ResidueField B) N
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B)
    (ResidueField B) N
  rw [e₁.finrank_eq, ← e₂.finrank_eq, Module.finrank_baseChange]

theorem spanFinrank_map_eq_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).spanFinrank = (⊤ : Submodule B (B ⊗[A] I)).spanFinrank := by
  let g : B ⊗[A] I →ₗ[B] B :=
    (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.lTensor B B I.subtype
  have hg : Function.Injective g := by
    have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor B B I.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective
    exact (TensorProduct.AlgebraTensorModule.rid A B B).injective.comp h1
  have hr : Submodule.map g ⊤ = I.map (algebraMap A B) := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      induction x with
      | tmul b i =>
        have : g (b ⊗ₜ i) = b * algebraMap A B i := by
          simp [g, Algebra.smul_def, mul_comm]
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rw [Ideal.map, Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨(1 : B) ⊗ₜ ⟨i, hi⟩, trivial, ?_⟩
      simp [g, Algebra.smul_def]
  rw [← hr, Submodule.spanFinrank_map_eq_of_injective g hg]

theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim A = ringKrullDim B := by
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have e := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [h, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at e
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, e]

theorem isRegularLocalRing_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  have hd := ringKrullDim_eq_of_flat_of_map_maximalIdeal h
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A ?_, hd⟩
  have e : (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank := by
    rw [← h, spanFinrank_map_eq_of_flat, spanFinrank_top_tensor_eq, Submodule.spanFinrank_top]
  rw [e, hd]
  exact ((isRegularLocalRing_iff B).mp inferInstance).le

theorem isRegularLocalRing_of_flat_of_map_maximalIdeal' {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B) (hf : φ.Flat)
    (h : (maximalIdeal A).map φ = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  algebraize [φ]
  have : IsLocalHom (algebraMap A B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have : algebraMap A B a ∈ maximalIdeal B := h ▸ Ideal.mem_map_of_mem _ hm
    exact (mem_maximalIdeal _).1 this ha
  exact isRegularLocalRing_of_flat_of_map_maximalIdeal h

theorem isRegularLocalRing_of_isEtaleCompletion {A B : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B)
    (h : GlobalTheory.Toroidal.IsEtaleCompletion φ) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B :=
  isRegularLocalRing_of_flat_of_map_maximalIdeal' φ h.1 h.2.1

theorem smoothOfRelativeDimension_of_isRegularLocalRing {F : Type} [Field F] [PerfectField F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] (n : ℕ)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) = n) :
    SmoothOfRelativeDimension n f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension n)
    X.affineOpenCover.openCover fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of F ⟶ R := Spec.preimage (x ≫ f)
  letI : Algebra F R := φ.hom.toAlgebra
  have hφ : x ≫ f = spMap (algebraMap F R) := (Spec.map_preimage (x ≫ f)).symm
  change SmoothOfRelativeDimension n (x ≫ f)
  rw [hφ]
  have hft : LocallyOfFiniteType (spMap (algebraMap F R)) := by rw [← hφ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType F R := RingHom.finiteType_algebraMap.mp hft
  refine GlobalTheory.RegGenSmooth.smooth_of_regular F R n fun m hm => ?_
  let y : Spec R := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  have hcl : IsClosed ({x y} : Set X) := by
    have h1 : IsClosed ({y} : Set (Spec R)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
    have he := x.isOpenEmbedding
    have hlc := IsLocallyClosed.image h1.isLocallyClosed he.isInducing
      he.isOpen_range.isLocallyClosed
    rw [Set.image_singleton] at hlc
    exact isClosed_singleton_of_isLocallyClosed_singleton hlc
  obtain ⟨h1, h2⟩ := h (x y) hcl
  let e := (asIso (x.stalkMap y) ≪≫ Spec.stalkIso R y).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

end GlobalTheory.RegSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefCurveTest

theorem smoothOfRelativeDimension_one {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (s : C ⟶ Sp k) [Smooth s]
    (hd : topologicalKrullDim C = 1) : SmoothOfRelativeDimension 1 s := by
  obtain ⟨n, hn⟩ : ∃ n, SmoothOfRelativeDimension n s := exists_dim_of_preconnected s (genericPoint C)
  obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have e := (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).symm.trans
    (SmoothDim.ringKrullDim_affineOpen k _ _ _ hn U hU ⟨x, hxU⟩)
  obtain rfl : 1 = n := by exact_mod_cast e
  exact hn

theorem exists_smooth_finite {k : Type} [Field k] [IsAlgClosed k] {D : Scheme.{0}} [IsIntegral D] (s : D ⟶ Sp k)
    [IsProper s] (hd : topologicalKrullDim D = 1) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (f : C ⟶ D), IsFinite f ∧ f (genericPoint C) = genericPoint D ∧
      topologicalKrullDim C = 1 ∧ Smooth (f ≫ s) := by
  let f := D.fromSpecResidueField (genericPoint D)
  let c := f.fromNormalization
  haveI : IsFinite c := NormCurve.isFinite_fromNormalization f s
  have htr : letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
      Algebra.trdeg k Γ(Spec (D.residueField (genericPoint D)), ⊤) ≤ 1 := by
    obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    have e : ⊤ ≤ f ⁻¹ᵁ U := fun z _ => by
      change f z ∈ U
      rw [Scheme.fromSpecResidueField_apply]
      exact VB.genericPoint_mem hxU
    letI := (NormCurve.constHom s U).toAlgebra
    haveI : Algebra.FiniteType k Γ(D, U) := NormCurve.finiteType_constHom s hU
    haveI : Nonempty (⊤ : (Spec (D.residueField (genericPoint D))).Opens) :=
      ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
    letI := (NormCurve.isField_sections (⊤ : (Spec (D.residueField (genericPoint D))).Opens)).toField
    letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
    letI := (f.appLE U ⊤ e).hom.toAlgebra
    haveI : IsScalarTower k Γ(D, U) Γ(Spec (D.residueField (genericPoint D)), ⊤) :=
      .of_algebraMap_eq' (NormCurve.appLE_comp_constHom s f U ⊤ e).symm
    exact (NormCurve.finite_integralClosure k (NormCurve.surjectiveOnStalks_appLE f hU ⊤ e)).2
      ((ringKrullDim_quotient_le _).trans (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).le)
  have hξ : genericPoint D ∈ Set.range c := by
    refine ⟨f.toNormalization (Nonempty.some inferInstance), ?_⟩
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization, Scheme.fromSpecResidueField_apply]
  have hs : Function.Surjective c := fun y =>
    (genericPoint_specializes y).mem_closed c.isClosedMap.isClosed_range hξ
  have hη : c (genericPoint _) = genericPoint D := by
    obtain ⟨y, hy⟩ := hξ
    refine ((genericPoint_specializes _).antisymm ?_).eq.symm
    exact ((genericPoint_specializes y).map c.continuous).trans (specializes_of_eq hy)
  exact ⟨f.normalization, inferInstance, c, inferInstance, hη,
    ((Published.dim_le_of_isIntegralHom c).antisymm (PosBaseChange.dim_le_of_isClosedMap c.isClosedMap hs)).trans hd,
    CurveThrough.smooth_of_dedekind_charts k _ _ (NormCurve.isDedekindDomain_sections f s htr)⟩

def CurveTest (K : Type) [Field K] {X : Scheme.{0}} (L : LB X) : Prop :=
  ∀ (C : Scheme.{0}) [Algebra K Γ(C, ⊤)], SmoothOfRelativeDimension 1 (strHom K (X := C)) → IsProjOver (strHom K (X := C)) →
    GeometricallyConnected (strHom K (X := C)) → ∀ g : C ⟶ X, 0 ≤ interNum K (structureModule C) ![L.pull g]

theorem CurveTest.pull {K : Type} [Field K] {X Y : Scheme.{0}} {L : LB X} (h : CurveTest K L) (hL : L.IsLB)
    (π : Y ⟶ X) : CurveTest K (L.pull π) := fun C _ hs hp hc g => by
  refine (h C hs hp hc (g ≫ π)).trans_eq (interNum_congr_cls K _ (isLB_vecOne (LB.isLB_pull hL _))
    (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hL _) _)) fun j => ?_)
  fin_cases j
  exact pull_comp g π (cls L hL)

theorem CurveTest.isNef_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)]
    {L : LB X} (h : CurveTest K L) (hL : L.IsLB) : IsNef K L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong K i
  have hi := appTop_algebraMap_along K i
  rw [comp_strHom hi] at hp
  obtain ⟨C, _, f, _, hη, hdC, hs⟩ := exists_smooth_finite (strHom K D) hd
  letI := algebraΓAlong K f
  have hf := appTop_algebraMap_along K f
  have hpC : IsProper (f ≫ strHom K D) := inferInstance
  rw [comp_strHom hf] at hs hpC
  have hM := LB.isLB_pull hL i
  have h₀ := h.pull hL i C (smoothOfRelativeDimension_one _ hdC) (ProperCurve.isProjOver_of_isProper _ hdC)
    (geometricallyConnected_of_isAlgClosed _) f
  have e₁ := ProjFin.interNumOn_eq_residueDegree_mul K D C f (ProperCurve.isProjOver_of_isProper _ hd) hd hη _ hM
  rw [interNumOn_eq_interNum_pull hf (isLB_vecOne hM)] at e₁
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL)]
  have hdeg : 0 < f.residueDegree (genericPoint C) := Nat.pos_of_ne_zero
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite f _).2 (residueFieldMap_finite_of_locallyQuasiFinite f _))
  have e₂ : (fun j => ((![L.pull i] : Fin 1 → LB D) j).pull f) = ![(L.pull i).pull f] :=
    funext fun j => by fin_cases j; rfl
  have e₃ : (fun j => ((![L] : Fin 1 → LB X) j).pull i) = ![L.pull i] := funext fun j => by fin_cases j; rfl
  rw [e₂] at e₁
  rw [e₃]
  rw [e₁] at h₀
  exact nonneg_of_mul_nonneg_right h₀ (by exact_mod_cast hdeg)

theorem CurveTest.isNef (hN : Published.NefProductNonneg) {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    {L : LB X} (h : CurveTest (AlgebraicClosure k) L) (hL : L.IsLB) : IsNef k L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong k i
  have hi := appTop_algebraMap_along k i
  rw [comp_strHom hi] at hp
  have hM := LB.isLB_pull hL i
  obtain ⟨D', _, π, hp', hd', -, -, he⟩ :=
    Published.exists_algClosed_baseChange (ProperCurve.isProjOver_of_isProper (strHom k D) hd)
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL), ← he 1 _ fun j => LB.isLB_pull (isLB_vecOne hL j) i]
  refine hN _ D' 1 hp' (hd'.trans hd) _ fun j => ?_
  fin_cases j
  exact ((h.pull hL i).pull hM π).isNef_of_isAlgClosed (LB.isLB_pull hM π)

end GlobalTheory.NefCurveTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlane
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagrGram

theorem hTens_eq_trace {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_rhs => enter [2, j, 2, l]; rw [Finset.sum_comm]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hTens_restrict {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (JA : Matrix α α E) (JB : Matrix β β E) (JB₁ : Matrix γ γ E) (ι : Matrix β γ E)
    (h : ιᵀ * JB * ι.map c = JB₁) (z z' : Matrix α γ E) :
    hTens c JA JB (z * ιᵀ) (z' * ιᵀ) = hTens c JA JB₁ z z' := by
  rw [hTens_eq_trace, hTens_eq_trace, ← h, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.map_mul, Matrix.transpose_map]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem incM_map_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {m k : Type} (J : Matrix m k E) :
    (incM F J).map (cA σ) = incM F (J.map σ) := by
  ext i j
  simp [incM, cA, inclR]

theorem symp_restrict_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E)
    (ι : Matrix (Fin d) (Fin d₁) E), ιᵀ * JW * ι.map σ = JW₁ → ∀ z z' : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (cA σ) (-1) (incM F JX) (incM F JW) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F ι)ᵀ)
        (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F ι)ᵀ) = symp (cA σ) (-1) (incM F JX) (incM F JW₁) z z' := by
  intro F E _ _ _ _ _ σ n d d₁ JX JW JW₁ ι h z z'
  have hA : (incM F ι)ᵀ * incM F JW * (incM F ι).map (cA σ) = incM F JW₁ := by
    rw [incM_map_cA, ← h]
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp only [incM, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [h1, Matrix.one_mul, Matrix.one_mul]
  simp only [symp]
  rw [hTens_restrict _ _ _ _ _ hA]

end GlobalTheory.MixedLagrGram
end
end

