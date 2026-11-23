module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import GroundTheory.GlobalFields.LocalAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCommutingTwistedConjCompactMemTwistedCentral
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.NormOneProper

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := by
  intro E _ _ _ hU n w y hy C hC
  by_cases hs : IsSplitAt w
  · refine ⟨{1}, isCompact_singleton, fun z hz _ => ⟨z, ?_, 1, rfl, (mul_one z).symm⟩⟩
    have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    have h2 : nrmL n w y = y := by rw [nrmL, if_pos hs]
    rw [h2] at hz
    change z * y = y * thL n w z
    rw [h1, MonoidHom.id_apply, hz]
  · set K := w.adicCompletion E
    obtain ⟨-, hinv, hv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    letI : StarRing K :=
      { star := cj w
        star_involutive := hinv
        star_mul := fun a b => by rw [map_mul, mul_comm]
        star_add := map_add (cj w) }
    have hse : starRingEnd K = cj w := RingHom.ext fun _ => rfl
    have hθ : thL n w = thetaGL n (starRingEnd K) := by rw [thL, if_neg hs, hse]
    have hθv : ∀ g : GLw n w, (thL n w g).val = GlobalTheory.Tw.theta g.val := fun g => by
      rw [hθ]; exact thetaGL_val g
    have hN : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val := by
      rw [nrmL, if_neg hs, ← hse, Units.val_mul, thetaGL_val]; rfl
    have hReg : GlobalTheory.Tw.Reg (y.val) := ⟨y.isUnit, by rw [← hN]; exact hy⟩
    have TC := GlobalTheory.Tw.twisted_centraliser n K y.val hReg
    letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField _ _
    haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    have hnorm : ∀ x : K, ‖star x‖ = ‖x‖ := fun x => by
      simp only [Valued.toNormedField.norm_def]
      have h1 := Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (star x)
      have h2 := Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) x
      have h3 : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict (star x) =
          (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict x :=
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h1.trans ((hv x).trans h2.symm))
      rw [h3]
    set C' : Set (GLw n w) := (fun c : GLw n w => y * c⁻¹) '' C
    have hC' : IsCompact C' := hC.image (by fun_prop)
    obtain ⟨D, hD, hDp⟩ := _root_.GlobalTheory.Tw.NormOneCore.exists_normOne_mul_compact K hnorm n y.val hReg C' hC'
    refine ⟨D, hD, fun z hz hzC => ?_⟩
    have hzv : z.val * GlobalTheory.Tw.nrm y.val = GlobalTheory.Tw.nrm y.val * z.val := by
      rw [← hN, ← Units.val_mul, hz, Units.val_mul]
    have hzA : z.val ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val} := (TC.2.2.2.2.1 z.val).1 hzv
    have hcomm : ∀ x ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val}, z.val * x = x * z.val := by
      intro x hx
      have hle : Algebra.adjoin K {GlobalTheory.Tw.nrm y.val} ≤ Subalgebra.centralizer K {z.val} := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact hzv
      exact hle hx z.val (Set.mem_singleton _)
    have hadj : GlobalTheory.Tw.adj y.val z.val = (y * (thL n w z)⁻¹ * y⁻¹).val := by
      rw [Units.val_mul, Units.val_mul, ← map_inv, hθv, GlobalTheory.Tw.theta, GlobalTheory.Tw.adj]
      have hzi : ((z⁻¹ : GLw n w).val)⁻¹ = z.val := by
        rw [Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 z.isUnit)]
      rw [hzi, Matrix.coe_units_inv y]
      simp only [Matrix.mul_assoc]
    have hu : (y * (z⁻¹ * y * thL n w z)⁻¹).val = z.val * GlobalTheory.Tw.adj y.val z.val := by
      rw [hcomm _ (TC.2.2.2.1 _ hzA).1, hadj]
      simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    obtain ⟨t, htA, ht1, d, hd, rfl⟩ := hDp z hzA _ ⟨_, hzC, rfl⟩ hu
    refine ⟨t, ?_, d, hd, rfl⟩
    have htc : t.val ∈ GlobalTheory.Tw.cent y.val := by rw [TC.2.2.2.2.2]; exact ⟨htA, ht1⟩
    change t * y = y * thL n w t
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hθv]; exact htc.2)

end GlobalTheory.NormOneProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullstellensatzPointOfSystem
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry CategoryTheory

open GlobalTheory.CompHt

namespace GlobalTheory.ConeOnto

theorem exists_rat_pt {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Sp K) [LocallyOfFiniteType f]
    {Z : Set X} (hZ : IsLocallyClosed Z) {x : X} (hx : x ∈ Z) :
    ∃ a : Sp K ⟶ X, a ≫ f = 𝟙 _ ∧ ∀ w, a w ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hZ
  replace hc : IsClosed {c} := hc
  exact ⟨pointOfClosedPoint f c hc, pointOfClosedPoint_comp _ _ _, fun w => by rw [pointOfClosedPoint_apply]; exact hcZ⟩

end GlobalTheory.ConeOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThK.SmoothLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure IsSmModOn (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Γ : Set (GAd σ J)) (φ : GAd σ J → ℂ) :
    Prop where
  left : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g
  level : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, GlobalTheory.SiegelSet.IsRealLine σ J (γ i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => γ i (t i)).prod)
  growth : ∃ N : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr GlobalTheory.SiegelSet.lineDer φ g‖ ≤ C * (GlobalTheory.AdelicU.height σ J g : ℝ) ^ N

theorem IsSmModOn.of_isSmoothModerate {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Γ : Set (GAd σ J)}
    {φ : GAd σ J → ℂ} (h : GlobalTheory.SiegelSet.IsSmoothModerate σ J φ) (hΓ : Γ ⊆ ratPts σ J) : IsSmModOn σ J Γ φ :=
  ⟨fun γ hγ g => h.left γ (hΓ hγ) g, h.level, h.cont, h.smooth, h.growth⟩

theorem isSmModOn_const (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Γ : Set (GAd σ J)) (c : ℂ) :
    IsSmModOn σ J Γ fun _ => c :=
  have h := GlobalTheory.SiegelSet.isSmoothModerate_const σ J c
  ⟨fun _ _ _ => rfl, h.level, h.cont, h.smooth, h.growth⟩

end GlobalTheory.ThK.SmoothLev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
section
noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def IsTwEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f = x →
      p f₁ = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • x

def IsOffEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∃ k ∈ KInf σ W B.emb, ∃ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k ∧ ∃ c : ℂ,
    c ≠ (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) ∧ ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f = x → p f₁ = c • x

def twPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsTwEig B M om p W₁ H' χ z x}

def offPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsOffEig B M om p W₁ H' χ z x}

def KStabL (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (N : Submodule ℂ P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ k₁ ∈ KInf σ W₁ B.emb, IsLevi H' 1 k₁ k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N

theorem twPart_le (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : twPart B M om p W₁ H' χ z V ≤ V :=
  Submodule.span_le.2 fun _ hx => hx.1

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddNormPowLeSumLinearFormPow
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem onePlusNormPow_le_sum_linearForm_pow : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ), ∃ (K : ℕ) (l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (C : ℝ), (∀ j, ‖l j‖ ≤ 1) ∧ ∀ y, (1 + ‖y‖) ^ N ≤ C * (1 + ∑ j, |l j y| ^ N) := by
  intro F _ _ κ _ N
  let b := Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)
  let K := Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)
  let c : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
    fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let w : Fin K → ℝ := fun j => (1 + ‖c j‖) * ‖b j‖
  have hw : ∀ j, 0 ≤ w j := fun j => by positivity
  let W : ℝ := 1 + ∑ j, w j
  have hW1 : 1 ≤ W := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hw j); simp only [W]; linarith
  have hwW : ∀ j, w j ≤ W := fun j => by
    have := Finset.single_le_sum (f := w) (fun j _ => hw j) (Finset.mem_univ j)
    simp only [W]; linarith
  let l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := fun j => (1 + ‖c j‖)⁻¹ • c j
  have hl : ∀ j, ‖l j‖ ≤ 1 := fun j => by
    have h0 : 0 < 1 + ‖c j‖ := by positivity
    simp only [l, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h0]
    rw [inv_mul_le_iff₀ h0]; linarith
  have hlw : ∀ j y, |l j y| * w j = |b.repr y j| * ‖b j‖ := fun j y => by
    have h0 : 0 < 1 + ‖c j‖ := by positivity
    simp only [l, w, c, ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos h0]
    field_simp
  have hnorm : ∀ y, ‖y‖ ≤ ∑ j, |l j y| * w j := fun y => by
    calc ‖y‖ = ‖∑ j, b.repr y j • b j‖ := by rw [b.sum_repr y]
      _ ≤ ∑ j, ‖b.repr y j • b j‖ := norm_sum_le _ _
      _ = ∑ j, |l j y| * w j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hlw, norm_smul, Real.norm_eq_abs]
  refine ⟨K, l, ((K : ℝ) + 1) ^ N * W ^ N, hl, fun y => ?_⟩
  have hS : 0 ≤ ∑ j, |l j y| ^ N := Finset.sum_nonneg fun j _ => by positivity
  rcases N with _ | n
  · simp only [pow_zero, one_mul]
    have : (0:ℝ) ≤ ∑ _x : Fin K, (1:ℝ) := by positivity
    linarith
  let f : Option (Fin K) → ℝ := fun o => Option.elim o 1 fun j => |l j y| * w j
  have hf : ∀ o ∈ (Finset.univ : Finset (Option (Fin K))), 0 ≤ f o := by
    intro o _; cases o with
    | none => simp [f]
    | some j => simp only [f, Option.elim_some]; exact mul_nonneg (abs_nonneg _) (hw j)
  have h1 : 1 + ‖y‖ ≤ ∑ o, f o := by
    rw [Fintype.sum_option]; simp only [f, Option.elim_none, Option.elim_some]
    linarith [hnorm y]
  have h2 := pow_sum_le_card_mul_sum_pow hf n
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin, Fintype.sum_option] at h2
  simp only [f, Option.elim_none, Option.elim_some, one_pow] at h2
  have h3 : ∑ j, (|l j y| * w j) ^ (n + 1) ≤ W ^ (n + 1) * ∑ j, |l j y| ^ (n + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hw j) (hwW j) _) (by positivity)
  have hW : 1 ≤ W ^ (n + 1) := one_le_pow₀ hW1
  have hK : ((K : ℝ) + 1) ^ n ≤ ((K : ℝ) + 1) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith [(K.cast_nonneg : (0:ℝ) ≤ K)]) (Nat.le_succ n)
  have hKn : 0 ≤ ((K : ℝ) + 1) ^ n := by positivity
  calc (1 + ‖y‖) ^ (n + 1) ≤ (∑ o, f o) ^ (n + 1) :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ ≤ ((K : ℝ) + 1) ^ n * (1 + ∑ j, (|l j y| * w j) ^ (n + 1)) := by
        rw [Fintype.sum_option]; simpa [f] using h2
    _ ≤ ((K : ℝ) + 1) ^ n * (W ^ (n + 1) * (1 + ∑ j, |l j y| ^ (n + 1))) := by
        gcongr; nlinarith
    _ ≤ ((K : ℝ) + 1) ^ (n + 1) * W ^ (n + 1) * (1 + ∑ j, |l j y| ^ (n + 1)) := by
        rw [← mul_assoc]; gcongr

end GlobalTheory.ArchDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateSecond
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.BaseId

variable {D : D7}

section Row

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem tie_baseChange {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r n : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {Γ : Type} [Group Γ]
    {act : Γ → Rul Xo c →ₗ[c.F] Rul Xo c} {act' : Γ → Rul Xo c' →ₗ[c'.F] Rul Xo c'}
    {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] {Tup : Type} {dδ : Tup → DeltaDat Xo c' n}
    {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
    {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat D.host.E n} {Nc : ∀ t, Cl' t → ℕ}
    {gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
    {cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ} {ph : ℂ}
    (htie : OneMapTieC hle LL U σ' V dict mu xr a act act' dδ Cl' w La Nc gam vol ep io thAd Pl cc ph) (t : Tup) :
    ∃ z ∈ Subgroup.center Γ, ∃ ze ∈ LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      ∃ (f' : Rul Xo c') (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), f' ∈ sec Xo c' a n ∧
        IsThClsD Xo c' (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f' ∧ (∀ k, fs k ∈ cusp Xo c U a n) ∧
        IsBC hle f' as fs ∧ ∀ q : AutQ V, ph * thAd t x q = ∑ k, ze * σ' (as k) * ((lieFac Dw xr a : ℂ) *
          adel V dict (muPin V dict mu cc) (rdU (U (σ'.comp (incF c c' hle))) (act z (fs k))) q.out) := by
  obtain ⟨-, hC, hA, -, -, z, hz, hrow⟩ := htie
  obtain ⟨ze, hze, hroot, hrow⟩ := hrow t
  refine ⟨z, hz, ze, hze, hroot, fun x hx => ?_⟩
  obtain ⟨⟨f', hf', hcl⟩, hall⟩ := hrow x hx
  have hf's := cusp_le_sec _ _ _ _ _ hf'
  obtain ⟨m, as, fs, hfs, hBC⟩ := hC a n f' hf'
  have hBCz := hA a n z m as fs f' hf's (fun k => cusp_le_sec _ _ _ _ _ (hfs k)) hBC
  refine ⟨f', m, as, fs, hf's, hcl, hfs, hBC, fun q => ?_⟩
  have h1 := hall f' hf's hcl q
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC hle U σ' hBCz (dict q.out).1 (dict q.out).2
  have h3 : jFn V σ' (rdU (unfBC hle U σ')) dict mu (act' z f') q = mu q.out * ∑ k, σ' (as k) *
      rdU (U (σ'.comp (incF c c' hle))) (act z (fs k)) (dict q.out).1 (dict q.out).2 :=
    congrArg (mu q.out * ·) h2
  rw [h1, h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adel_muPin]
  change ze * cc (dict q.out).1 * _ * _ = _
  ring

end Row

theorem phiC_congr (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem proj_model {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {X G : Type} [AddCommGroup X] [Module ℂ X] [Fintype G]
    (e : X →ₗ[ℂ] MMap M) (he : Function.Injective e) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (c : G → ℂ)
    (ρ : G → X →ₗ[ℂ] X) (hρ : ∀ g x, e (ρ g x) = postOn M (L g) (e x)) (ph : ℂ) (y y' w : X)
    (hy : e y' = postOn M (∑ g, c g • L g) (e y)) (hw : ph • y = w) : ph • y' = ∑ g, c g • ρ g w := by
  have h1 : y' = ∑ g, c g • ρ g y := by
    apply he
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum]
    simp only [map_smul, hρ]
    ext v x
    simp [postOn, LinearMap.sum_apply, Finset.sum_apply]
  rw [h1, ← hw, Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, smul_comm]

theorem eq_of_reps {V : HSp D} {S : D.what₂.Tau → SPar} {θ} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] MMap M) (hr : LinearMap.range e = Mult.Mult θ M J χ) (v : M.Vec)
    (hinj : Function.Injective fun x => e x v) (ph : ℂ) (y : X) {n : ℕ} (b : Fin n → ℂ) (u : Fin n → X)
    (h : ∀ q : AutQ V, ph * e y v q.out = ∑ k, b k * e (u k) v q.out) : ph • y = ∑ k, b k • u k := by
  apply hinj
  funext g
  refine GlobalTheory.PhaseRational.eq_of_out
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v)
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v) (fun q => ?_) g
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, Finset.sum_apply] using h q

end GlobalTheory.GalLift.BaseId

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartREqPartLSwap
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.BlockSwap

section Generic

variable {A : Type} {κ κ' κ₁' : Type}

def swapV (z : κ' ⊕ κ → A) : κ ⊕ κ' → A := z ∘ Sum.swap

theorem partR_eq_partL_swap (T : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) (y : κ ⊕ κ₁' → A) :
    partR T Φ y = partL T (fun z : κ' ⊕ κ → A => Φ (swapV z)) (swapV y) := by
  simp only [partR, partL, swapV]
  congr 1
  funext x
  congr 1
  funext i
  cases i <;> rfl

end Generic

section Adelic

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def swapCLE (M : Type) [NormedAddCommGroup M] [NormedSpace ℝ M] (κ κ' : Type) : (κ' ⊕ κ → M) ≃L[ℝ] (κ ⊕ κ' → M) :=
  { LinearEquiv.funCongrLeft ℝ M (Equiv.sumComm κ κ') with
    continuous_toFun := continuous_pi fun _ => continuous_apply _
    continuous_invFun := continuous_pi fun _ => continuous_apply _ }

def swapH (X : Type) [TopologicalSpace X] (κ κ' : Type) : (κ' ⊕ κ → X) ≃ₜ (κ ⊕ κ' → X) where
  toFun := swapV
  invFun := swapV
  left_inv z := by funext i; cases i <;> rfl
  right_inv z := by funext i; cases i <;> rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem sb_swap {X : Type} [TopologicalSpace X] {κ κ' : Type} {g : (κ ⊕ κ' → X) → ℂ} (hg : g ∈ SB (κ ⊕ κ' → X)) :
    (fun z : κ' ⊕ κ → X => g (swapV z)) ∈ SB (κ' ⊕ κ → X) :=
  ⟨hg.1.comp_continuous (swapH X κ κ').continuous, hg.2.comp_homeomorph (swapH X κ κ')⟩

theorem partR_of_partL {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ)
    (hL : ∃ P : SInf F (κ' ⊕ κ) →L[ℂ] SInf F (κ₁' ⊕ κ), ∀ g ∈ SB (κ' ⊕ κ → Af F), ∃ g₁ ∈ SB (κ₁' ⊕ κ → Af F),
      ∀ f : SInf F (κ' ⊕ κ), partL e (pureA F f g) = pureA F (P f) g₁) :
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F),
      ∀ f : SInf F (κ ⊕ κ'), partR e (pureA F f g) = pureA F (P f) g₁ := by
  obtain ⟨PL, hPL⟩ := hL
  refine ⟨(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ₁' κ)).comp
    (PL.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ κ'))), fun g hg => ?_⟩
  obtain ⟨g₁, hg₁, h⟩ := hPL _ (sb_swap hg)
  refine ⟨fun w => g₁ (swapV w), sb_swap hg₁, fun f => ?_⟩
  funext y
  rw [partR_eq_partL_swap]
  have hpure : (fun z : κ' ⊕ κ → AF F => pureA F (⇑f) g (swapV z)) =
      pureA F (⇑(SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE _ κ κ') f)) (fun w => g (swapV w)) := rfl
  rw [hpure, h]
  rfl

end Adelic

end GlobalTheory.DblEval.BlockSwap

end
end

