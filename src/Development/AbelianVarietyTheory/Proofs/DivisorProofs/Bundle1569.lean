module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacCocycle

section General

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem _root_.GlobalTheory.VacCocycle.conj_hTens (hc : ∀ z, c (c z) = z) {JA : Matrix α α A}
    {JB : Matrix β β A} (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j)
    (x y : Matrix α β A) :
    c (_root_.GlobalTheory.WeilM.hTens c JA JB y x) = -_root_.GlobalTheory.WeilM.hTens c JA JB x y := by
  unfold _root_.GlobalTheory.WeilM.hTens
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc, hA, hB]
  simp only [← Finset.sum_neg_distrib]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, k, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem _root_.GlobalTheory.VacCocycle.trace_conj (hc : ∀ z, c (c z) = z) (z : A) :
    Algebra.trace R A (c z) = Algebra.trace R A z :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z

end General

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
omit [DecidableEq α] [DecidableEq β] in
private lemma hTens_add_add (JA : Matrix α α A) (JB : Matrix β β A)
    (x y : Matrix α β A) :
    _root_.GlobalTheory.WeilM.hTens c JA JB (x + y) (x + y) =
      _root_.GlobalTheory.WeilM.hTens c JA JB x x + _root_.GlobalTheory.WeilM.hTens c JA JB x y +
        _root_.GlobalTheory.WeilM.hTens c JA JB y x + _root_.GlobalTheory.WeilM.hTens c JA JB y y := by
  unfold _root_.GlobalTheory.WeilM.hTens
  simp only [Matrix.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]
  ring

set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
private lemma addChar_symp_add_add (hc : ∀ z, c (c z) = z) {JA : Matrix α α A}
    {JB : Matrix β β A} (hA : ∀ i j, c (JA j i) = JA i j) (hB : ∀ i j, c (JB j i) = -JB i j)
    (ψ : AddChar R ℂ) {h : R} (hh : h * 2 = 1) {ξ : A} (hξ : c ξ = 1 - ξ) (x y : Matrix α β A)
    (h1 : ψ (_root_.GlobalTheory.WeilM.symp c ξ JA JB x y) = 1)
    (h2 : ψ (_root_.GlobalTheory.WeilM.symp c (-1) JA JB x y) = 1) :
    ψ (h * _root_.GlobalTheory.WeilM.symp c ξ JA JB (x + y) (x + y)) =
      ψ (h * _root_.GlobalTheory.WeilM.symp c ξ JA JB x x) *
        ψ (h * _root_.GlobalTheory.WeilM.symp c ξ JA JB y y) *
        ψ (-(h * _root_.GlobalTheory.WeilM.symp c (-1) JA JB x y)) := by
  unfold _root_.GlobalTheory.WeilM.symp at *
  have hswap : _root_.GlobalTheory.WeilM.hTens c JA JB y x =
      -c (_root_.GlobalTheory.WeilM.hTens c JA JB x y) := by
    rw [_root_.GlobalTheory.VacCocycle.conj_hTens c hc hA hB y x, neg_neg]
  have hconj : Algebra.trace R A (ξ * c (_root_.GlobalTheory.WeilM.hTens c JA JB x y)) =
      Algebra.trace R A (_root_.GlobalTheory.WeilM.hTens c JA JB x y) -
        Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x y) := by
    rw [← _root_.GlobalTheory.VacCocycle.trace_conj c hc, map_mul, hc, hξ, sub_mul, one_mul, map_sub]
  have hm1 : Algebra.trace R A (-1 * _root_.GlobalTheory.WeilM.hTens c JA JB x y) =
      -Algebra.trace R A (_root_.GlobalTheory.WeilM.hTens c JA JB x y) := by
    rw [neg_one_mul, map_neg]
  have key : h * Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB (x + y) (x + y)) =
      h * Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x x) +
        h * Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB y y) +
        -(h * Algebra.trace R A (-1 * _root_.GlobalTheory.WeilM.hTens c JA JB x y)) +
        (Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x y) +
          Algebra.trace R A (-1 * _root_.GlobalTheory.WeilM.hTens c JA JB x y)) := by
    rw [hTens_add_add, hswap]
    simp only [mul_add, map_add (f := _), mul_neg, map_neg]
    rw [hconj]
    linear_combination (Algebra.trace R A (ξ * _root_.GlobalTheory.WeilM.hTens c JA JB x y) -
      Algebra.trace R A (_root_.GlobalTheory.WeilM.hTens c JA JB x y)) * hh + (h - 1) * hm1
  rw [key]
  simp only [AddChar.map_add_eq_mul]
  rw [h1, h2, mul_one, mul_one]


set_option autoImplicit false in
open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
theorem _root_.GlobalTheory.VacCocycle.psi_half_symp_add : ∀ {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E))
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E))
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E))
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) * _root_.GlobalTheory.WeilM.symp
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY θ hθ v γ hγ γ' hγ'
  have hσ : ∀ z, σ (σ z) = z := by
    have hcm := hB.cm
    unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt at hcm
    obtain ⟨-, -, -, hτ⟩ := hcm
    intro z
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
    apply τ.injective
    rw [hτ, hτ, star_star]
  have hcc : ∀ z, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := by
    have hcomp : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ).comp (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = AlgHom.id _ _ := by
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA
      rw [← Algebra.TensorProduct.map_comp]
      have hσσ : σ.comp σ = AlgHom.id F E := AlgHom.ext hσ
      rw [hσσ, AlgHom.comp_id]
      exact Algebra.TensorProduct.map_id
    intro z
    exact DFunLike.congr_fun hcomp z
  have hinc : ∀ x : E, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) =
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (σ x) := by
    intro x
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR
    simp
  have hA : ∀ i j, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J j i) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J i j := by
    intro i j
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [Matrix.map_apply, Matrix.map_apply, hinc, hX.herm]
  have hB' : ∀ i j, _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J j i) =
      -_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J i j := by
    intro i j
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [Matrix.map_apply, Matrix.map_apply, hinc, hY.skew, map_neg]
  have hξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E)) =
      1 - _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (θ : E) := by
    rw [hinc, eq_sub_of_add_eq' hθ, map_sub, map_one]
  have hone : (_root_.GlobalTheory.AdelicU.evFin F v) 1 ∈
      HeightOneSpectrum.adicCompletionIntegers F v := by
    rw [map_one]
    exact one_mem _
  have h1 := _root_.GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v θ 1
    hone γ hγ γ' hγ'
  have h2 := _root_.GlobalTheory.LatVacArith.psi_symp_latAtV σ B X Y r s r' s' hB hX hY v (-1) 1
    hone γ hγ γ' hγ'
  rw [one_mul] at h1 h2
  have hm : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (((-1 : 𝓞 E) : E)) = -1 := by
    simp
  rw [hm] at h2
  exact addChar_symp_add_add (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) hcc hA hB' B.ψ
    (invOf_mul_self (2 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) hξ γ γ' h1 h2

end GlobalTheory.VacCocycle

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocal
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

def intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) : Af F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
    (fun v => ⟨(y v).1, (y v).2⟩)

theorem continuous_intFin : Continuous (intFin (F := F)) :=
  RestrictedProduct.isEmbedding_structureMap.continuous

theorem evalV_intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F))
    (w : HeightOneSpectrum (𝓞 F)) : evalV F w (intFin y) = (y w : Fv F w) := rfl

theorem intFin_nsmul (n : ℕ) (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) :
    intFin (n • y) = n • intFin y := by
  refine GlobalTheory.AdelicU.af_ext fun w => ?_
  rw [map_nsmul, evalV_intFin, evalV_intFin]
  rfl

theorem exists_finset_trivial (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ I : Finset (HeightOneSpectrum (𝓞 F)), ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1 := by
  let ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F := fun y =>
    LinearMap.inr F (Ainf F) (Af F) (intFin y)
  have hι : Continuous ι := continuous_const.prodMk continuous_intFin
  have hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2} :=
    isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const
  have h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2} := by
    have : ι 0 = 0 := by
      have h : intFin (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) = 0 := by
        simpa using intFin_nsmul (F := F) 0 0
      show LinearMap.inr F (Ainf F) (Af F) (intFin 0) = (0 : AF F)
      rw [h, map_zero]
    simp [this, AddChar.map_zero_eq_one]
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0
  refine ⟨I, fun y hy => GlobalTheory.eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_⟩
  have hmem : n • y ∈ (I : Set _).pi u := by
    intro a ha
    have : (n • y) a = 0 := by rw [Pi.smul_apply, hy a ha, smul_zero]
    rw [this]; exact (hu a ha).2
  have e : (ι (n • y) : AF F) = n • (ι y : AF F) := by
    show LinearMap.inr F (Ainf F) (Af F) (intFin (n • y)) = _
    rw [intFin_nsmul, map_nsmul]
  have h := hsub hmem
  simp only [Set.mem_setOf_eq] at h
  rwa [e, AddChar.map_nsmul_eq_pow] at h

end GlobalTheory.PsiProd

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem addChar_sum {A ι : Type} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem psiAt_eq_one_of_integral {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (I : Finset (HeightOneSpectrum (𝓞 F)))
    (hI : ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ I) (a : Fv F v) (ha : a ∈ v.adicCompletionIntegers F) :
    GlobalTheory.LatVac.psiAt ψ v a = 1 := by
  classical
  let y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F) := Pi.single v ⟨a, ha⟩
  have hy : ∀ u ∈ I, y u = 0 := fun u hu => Pi.single_eq_of_ne (by rintro rfl; exact hv hu) _
  have hfin : intFin y = GlobalTheory.AdelicU.singleFin v a := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_
    rw [evalV_intFin]
    by_cases e : w = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [y]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e]
      simp [y, Pi.single_eq_of_ne e]
  have := hI y hy
  rw [hfin] at this
  exact this

theorem psi_prod : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : AF F,
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)).Finite ∧
    ψ x = ψ (pairA F (fstA F x) 0) * ∏ᶠ v : Pl (F := F), GlobalTheory.LatVac.psiAt ψ v (evFin F v x) := by
  intro F _ _ ψ hψ x
  classical
  obtain ⟨I, hI⟩ := exists_finset_trivial ψ hψ
  set xf : Af F := sndA F x with hxf
  have hT : {v : HeightOneSpectrum (𝓞 F) | evalV F v xf ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 xf.2
  let S : Finset (HeightOneSpectrum (𝓞 F)) := I ∪ hT.toFinset
  have hev : ∀ v, evFin F v x = evalV F v xf := fun v => rfl
  have hsupp : (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    apply hv
    simp only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      not_or, not_not] at hvS
    show GlobalTheory.LatVac.psiAt ψ v (evFin F v x) = 1
    rw [hev]
    exact psiAt_eq_one_of_integral ψ I hI v hvS.1 _ hvS.2
  refine ⟨(S.finite_toSet).subset hsupp, ?_⟩
  let j : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)
  let χ : AddChar (Af F) ℂ := ψ.compAddMonoidHom j.toAddMonoidHom
  have hχ : ∀ a, χ a = ψ (j a) := fun a => rfl
  have hloc : ∀ v (a : Fv F v), GlobalTheory.LatVac.psiAt ψ v a = χ (GlobalTheory.AdelicU.singleFin v a) := fun v a => rfl
  have hx : x = pairA F (fstA F x) 0 + j xf := by
    refine Prod.ext ?_ ?_
    · show x.1 = x.1 + (0 : Ainf F)
      rw [add_zero]
    · show x.2 = (0 : Af F) + x.2
      rw [zero_add]
  let r : ∀ w : HeightOneSpectrum (𝓞 F), ↥(w.adicCompletionIntegers F) := fun w =>
    if hw : w ∈ S then 0 else ⟨evalV F w xf, by
      have : w ∉ hT.toFinset := fun h => hw (Finset.mem_union_right _ h)
      simpa using this⟩
  have hr : ∀ v ∈ I, r v = 0 := fun v hv => dif_pos (Finset.mem_union_left _ hv)
  have hdec : xf = ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (evalV F v xf) + intFin r := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, evalV_intFin]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun b _ hb => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _)
        (fun h => absurd hw h), GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [r, hw]
    · rw [Finset.sum_eq_zero (fun b hb => GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _)]
      simp [r, hw]
  have hrr : χ (intFin r) = 1 := hI r hr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  conv_lhs => rw [hx]
  rw [AddChar.map_add_eq_mul]
  congr 1
  rw [← hχ, hdec, AddChar.map_add_eq_mul, hrr, mul_one, addChar_sum]
  exact Finset.prod_congr rfl fun v _ => by rw [hloc, hev]

end GlobalTheory.PsiProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFixatorEqUnipotentRadicalMulCommonFixator
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem fixG_eq_unipRad_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ u ∈ unipRad σ J C, ∃ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), g = u * x ∧ (g ∈ ratPts σ J → x ∈ ratPts σ J) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g hg
  obtain ⟨g₀, b, hgZ, -, -, hrat⟩ := _root_.GlobalTheory.SphEis.core_isom F E σ n J j m C D Z J₀ hF g hg
  obtain ⟨e, -, he, herat⟩ := _root_.GlobalTheory.SphEis.core_embeds F E σ n J j m C D Z J₀ hF
  obtain ⟨hxC, hxD, hxZ⟩ := he g₀
  set x := e g₀ with hx
  refine ⟨g * x⁻¹, ?_, x, ⟨hxC, hxD⟩, by group, fun h => herat g₀ (hrat h)⟩
  rw [_root_.GlobalTheory.SphEis.mem_unipRad_iff_frame F E σ n J j m C D Z J₀ hF]
  have hxiC : x⁻¹ ∈ fixG σ J C := inv_mem hxC
  have hC' : (matHom _ σ J x⁻¹).1 * adMat F C = adMat F C := hxiC
  have hgC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg

  have hxiZ : (matHom _ σ J x⁻¹).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g₀⁻¹).1 := by
    have h1 : (matHom _ σ J x⁻¹).1 * ((matHom _ σ J x).1 * adMat F Z) * (matHom _ σ J₀ g₀⁻¹).1
        = (matHom _ σ J x⁻¹).1 * (adMat F Z * (matHom _ σ J₀ g₀).1) * (matHom _ σ J₀ g₀⁻¹).1 := by rw [hxZ]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.mul_one] at h1
    exact h1.symm
  refine ⟨?_, b * (matHom _ σ J₀ g₀⁻¹).1, ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hC', hgC]
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hxiZ, ← Matrix.mul_assoc, hgZ, Matrix.add_mul, Matrix.mul_assoc,
      ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.mul_one, Matrix.mul_assoc]

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignaturesStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSchwartz_genuineUnitaryRep_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGenD τ C γ Y → ∀ (T : TensD F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  first | exact @GlobalTheory.ArchRepD.archRepD | exact GlobalTheory.ArchRepD.archRepD | (intros; apply GlobalTheory.ArchRepD.archRepD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base PsiUnr stepFac)

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}


open Classical in
def chs (G : GridData Lc sc) (i j : Fin D.R.m) (t : T) : Chars D.host.F D.host.E where
  α := Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)
  β := G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)
  S₀ := G.pl.S0
  Q := (twPl G t).image fun w => w.under (𝓞 D.host.F)

def BaseFits (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (t : T) (B : Base D.host.F D.host.E) : Prop :=
  B.ψ = W.ψ ∧ (chs G i j t).T ⊆ B.P ∧ (∀ v ∈ B.P, PsiUnr B.ψ v) ∧
    ∀ v : B.P, v.1 ∈ (chs G i j t).T → GlobalTheory.AdelicU.splitPrime (B.τ v) ∈ locPl G t

end GlobalTheory.SqStep
end
end

