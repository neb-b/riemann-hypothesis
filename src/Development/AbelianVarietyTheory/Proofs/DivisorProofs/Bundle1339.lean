module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEllipticReproducingTestFunctionLaplacian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses.BaseChangeSign

section Gen
variable {L : Type} [Field L] (τ : L →+* L) {n : ℕ}

theorem hform_eq_mat (J : Matrix (Fin n) (Fin n) L) {ι : Type} [Fintype ι] (f : ι → Fin n → L) (i j : ι) :
    hform τ J (f i) (f j) = (cT τ (Matrix.of fun r i => f i r) * J * Matrix.of fun r i => f i r) i j := by
  simp only [hform, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_det_change (J : Matrix (Fin n) (Fin n) L) (V : Submodule L (Fin n → L)) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c b : Module.Basis ι L V) :
    (Matrix.of fun i j => hform τ J (b i).1 (b j).1).det =
      τ (c.toMatrix b).det * (Matrix.of fun i j => hform τ J (c i).1 (c j).1).det * (c.toMatrix b).det := by
  have hM : (Matrix.of fun r i => ((b i : V) : Fin n → L) r) =
      (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * c.toMatrix b := by
    ext r j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    have h := c.sum_toMatrix_smul_self b j
    calc ((b j : V) : Fin n → L) r = ((∑ i, c.toMatrix b i j • c i : V) : Fin n → L) r := by rw [h]
      _ = _ := by
        simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e1 : (Matrix.of fun i j => hform τ J (b i).1 (b j).1) =
      cT τ (Matrix.of fun r i => ((b i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((b i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((b i : V) : Fin n → L)) i j
  have e2 : (Matrix.of fun i j => hform τ J (c i).1 (c j).1) =
      cT τ (Matrix.of fun r i => ((c i : V) : Fin n → L) r) * J * Matrix.of fun r i => ((c i : V) : Fin n → L) r := by
    ext i j; exact hform_eq_mat τ J (fun i => ((c i : V) : Fin n → L)) i j
  have hdet : ∀ P : Matrix ι ι L, (cT τ P).det = τ P.det := by
    intro P; unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl
  rw [e1, e2, hM, cT_mul]
  set Mc := Matrix.of fun r i => ((c i : V) : Fin n → L) r
  set P := c.toMatrix b
  have : cT τ P * cT τ Mc * J * (Mc * P) = cT τ P * (cT τ Mc * J * Mc) * P := by
    simp only [Matrix.mul_assoc]
  rw [this, Matrix.det_mul, Matrix.det_mul, hdet]

theorem toMatrix_det_ne {V : Submodule L (Fin n → L)} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c b : Module.Basis ι L V) : (c.toMatrix b).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (c.toMatrix_mul_toMatrix_flip b)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end Gen

section BC
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ}

theorem mem_ker_map {A : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hx : x ∈ LinearMap.ker (Matrix.toLin' A)) :
    (φ ∘ x) ∈ LinearMap.ker (Matrix.toLin' (A.map φ)) := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
  funext i
  rw [← RingHom.map_mulVec, hx]; simp

theorem finrank_ker_map (A : Matrix (Fin n) (Fin n) K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (A.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (A.map φ))
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  have h3 : (A.map φ).rank = A.rank := GlobalTheory.Core.Rk.rank_map_field φ A
  change (A.map φ).rank + _ = _ at h1
  change A.rank + _ = _ at h2
  simp only [Module.finrank_fin_fun] at h1 h2
  omega

end BC

section Val
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]; ring

theorem sign_conj_mul {τ : L →+* L} (hv : ∀ x, Valued.v (τ x) = Valued.v x) {t : L} (ht : t ≠ 0) (a : L) :
    (-1 : ℂ) ^ ordL (τ t * a * t) = (-1) ^ ordL a := by
  by_cases ha : a = 0
  · simp [ha]
  have hτ : τ t ≠ 0 := (map_ne_zero τ).2 ht
  have ho : ordL (τ t) = ordL t := by
    unfold ordL; simp only [hv]
  rw [ordL_mul (mul_ne_zero hτ ha) ht, ordL_mul hτ ha, ho,
    show ordL t + ordL a + ordL t = ordL a + 2 * ordL t by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
  norm_num

end Val

section Main
variable {K L : Type} [Field K] [Field L] (σ : K →+* K) (τ : L →+* L) (φ : K →+* L) {n : ℕ}

theorem gram_det_map (hφ : ∀ x, τ (φ x) = φ (σ x)) (H A : Matrix (Fin n) (Fin n) K) :
    ∃ t : L, t ≠ 0 ∧ (gramOn τ (H.map φ) (LinearMap.ker (Matrix.toLin' (A.map φ)))).det =
      τ t * φ (gramOn σ H (LinearMap.ker (Matrix.toLin' A))).det * t := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 φ.injective
  set V := LinearMap.ker (Matrix.toLin' A) with hV
  set V' := LinearMap.ker (Matrix.toLin' (A.map φ)) with hV'
  have hk : Module.finrank L V' = Module.finrank K V := finrank_ker_map φ A
  rcases isEmpty_or_nonempty (Fin (Module.finrank L V')) with he | hne
  · haveI : IsEmpty (Fin (Module.finrank K V)) := hk ▸ he
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Matrix.det_isEmpty, Matrix.det_isEmpty]; simp
  let b := Module.finBasis K V
  let v : Fin (Module.finrank L V') → V' := fun i =>
    ⟨φ ∘ ((b (Fin.cast hk i) : V) : Fin n → K), mem_ker_map φ (b (Fin.cast hk i)).2⟩
  have hli : LinearIndependent L v := by
    apply LinearIndependent.of_comp V'.subtype
    have h0 : LinearIndependent K (fun i => ((b (Fin.cast hk i) : V) : Fin n → K)) :=
      (b.linearIndependent.map' V.subtype V.ker_subtype).comp _ (Fin.cast_injective hk)
    exact linearIndependent_algebraMap_comp_iff.2 h0
  let c := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _)
  have hc : ∀ i, c i = v i := fun i => by simp [c]
  refine ⟨(c.toMatrix (Module.finBasis L V')).det, toMatrix_det_ne c _, ?_⟩
  have e1 : gramOn τ (H.map φ) V' =
      Matrix.of fun i j => hform τ (H.map φ) (Module.finBasis L V' i).1 (Module.finBasis L V' j).1 := rfl
  rw [e1, gram_det_change τ (H.map φ) V' c (Module.finBasis L V')]
  have e2 : (Matrix.of fun i j => hform τ (H.map φ) (c i).1 (c j).1) =
      ((gramOn σ H V).map φ).submatrix (finCongr hk) (finCongr hk) := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, hc, v, Matrix.submatrix_apply, Matrix.map_apply, gramOn, hform, map_sum, map_mul,
      Function.comp_apply, hφ, finCongr_apply]
    rfl
  rw [e2, Matrix.det_submatrix_equiv_self,
    show ((gramOn σ H V).map φ).det = φ (gramOn σ H V).det from (RingHom.map_det φ _).symm]

end Main

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E),
    (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E)))
      (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det =
    (-1) ^ ordL (algebraMap E (w.adicCompletion E)
      (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := by
  intro E _ _ _ hU w hw n H A
  have hc := GlobalTheory.ConjAtPlace.main E hU w
  have hφ : ∀ x : E, cj w (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) :=
    fun x => (hc.2.2.2.1 hw).1 x
  obtain ⟨t, ht, hdet⟩ := gram_det_map (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w)
    (algebraMap E (w.adicCompletion E)) hφ H A
  rw [hdet, sign_conj_mul hc.2.2.1 ht]

end GlobalTheory.UnitaryClasses.BaseChangeSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfSkewUnipotentMemDoubledLatticeStabilizerStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  first | exact @GlobalTheory.DblVacUnip.unip_mem | exact GlobalTheory.DblVacUnip.unip_mem | (intros; apply GlobalTheory.DblVacUnip.unip_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraExistsReproducingTestFunctionGL
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCAlphaGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_alpha : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
    ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite →
    ∀ N : ℕ, ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]
    (μ : Measure (GL (Fin a) (Cinf E))), μ.IsHaarMeasure → ∃ α : GL (Fin a) (Cinf E) → ℂ, Continuous α ∧
      HasCompactSupport α ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ g, ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g :=
  _root_.GlobalTheory.HCAlphaGLC.exists_alpha

end GlobalTheory.HCAlphaGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraUniformSmoothingTestFunction
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.HCAlphaEll

theorem chart_sum {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (s : Finset ℕ) (c : ℕ → ℂ)
    (ψ : ℕ → Sm E a) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    chart (∑ k ∈ s, c k • ψ k).1 g y = ∑ k ∈ s, c k * chart (ψ k).1 g y := by
  have hy' : IsUnit (Matrix.of y) := hy
  simp only [chart, dif_pos hy', Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem reproduce_of_lap : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∀ p : Polynomial ℂ, p ≠ 0 → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ φ : Sm E a, Polynomial.aeval (lapOp E a) p φ = 0 → smoothing ν α φ.1 = φ.1 := by
  intro E _ _ _ a ν hν p hp
  obtain ⟨α, hα, h⟩ := _root_.GlobalTheory.HCParam.reproduce E a ν hν p hp
  refine ⟨α, hα, fun φ hφ => funext fun x => ?_⟩
  have h1 := h (chart φ.1 x) (φ.2 x) (fun y hy => by
    rw [Polynomial.aeval_eq_sum_range] at hφ
    have e := congrArg (fun ψ : Sm E a => chart ψ.1 x y) hφ
    rw [LinearMap.sum_apply] at e
    simp only [LinearMap.smul_apply] at e
    rw [chart_sum _ _ (fun k => (lapOp E a ^ k) φ) _ hy] at e
    have e0 : chart (0 : Sm E a).1 x y = 0 := by simp [chart]
    rw [e0] at e
    rw [← e, polyF, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, _root_.GlobalTheory.HCAlpha.chart_lapOp_pow E a φ x k y hy])
  rw [smoothing, h1]
  have := chart_val φ.1 x 1
  simpa using this

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_lieS {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (i j : Fin a) (x : Cinf E) :
    Commute z (lieS E a i j x) := by
  rw [lieS_apply]; exact hz _

theorem commute_casKOp {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) :
    Commute z (casKOp E a) := by
  unfold casKOp
  refine Commute.sum_right _ _ _ fun τ _ => Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  refine Commute.smul_right (Commute.add_right (Commute.pow_right ?_ 2) (Commute.pow_right ?_ 2)) _
  · exact (commute_lieS hz _ _ _).sub_right (commute_lieS hz _ _ _)
  · exact (commute_lieS hz _ _ _).add_right (commute_lieS hz _ _ _)

theorem commute_cas {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (τ : E →+* ℂ) :
    Commute z (Formalism.REAL.Cas (Eop (a := a) τ)) := by
  have hE : ∀ i j, Commute z (Eop τ i j) := fun i j =>
    Commute.smul_right ((commute_lieS hz _ _ _).sub_right ((commute_lieS hz _ _ _).smul_right _)) _
  unfold Formalism.REAL.Cas
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (hE i j).mul_right (hE j i)

theorem commute_lie_of_mem {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (X : Lie E a) :
    Commute z (lie E a X) := Zalg_mul_lie E a X z hz

theorem foldr_replicate (z : Module.End ℂ (Sm E a)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (φ : Sm E a) :
    (List.replicate N z).foldr (fun z f => z f - χ z • f) φ =
      Polynomial.aeval z ((Polynomial.X - Polynomial.C (χ z)) ^ N) φ := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', map_mul, Module.End.mul_apply]
    simp [sub_smul, Polynomial.aeval_X, Polynomial.aeval_C]

theorem exists_alpha_smoothing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ),
    FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1 := by
  intro E _ _ _ a L _ W hW χ N ν hν
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.T.exists_poly_maximalCompactCasimir_kills_KType E a W hW
  let A : Option (E →+* ℂ) → Module.End ℂ (Sm E a) := fun o => o.elim (casKOp E a) fun τ => Formalism.REAL.Cas (Eop τ)
  let c : Option (E →+* ℂ) → ℂ := fun o => o.elim 2 fun _ => 4
  let P : Option (E →+* ℂ) → Polynomial ℂ := fun o =>
    o.elim q fun τ => (Polynomial.X - Polynomial.C (χ (Formalism.REAL.Cas (Eop (a := a) τ)))) ^ N
  have hZ : ∀ τ : E →+* ℂ, ∀ X, Commute (Formalism.REAL.Cas (Eop (a := a) τ)) (lie E a X) := fun τ =>
    commute_lie_of_mem (GlobalTheory.T.casimir_glFactor_embedding_mem_capelliAlgebra E a τ)
  have hc : ∀ i j, Commute (A i) (A j) := by
    rintro (_ | τ) (_ | τ')
    · exact Commute.refl _
    · exact (commute_casKOp (hZ τ')).symm
    · exact commute_casKOp (hZ τ)
    · exact commute_cas (hZ τ) τ'
  have hP : ∀ i, P i ≠ 0 := by
    rintro (_ | τ)
    · exact hq0
    · exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  obtain ⟨p, hp0, hp⟩ := _root_.GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination A hc c P hP
  obtain ⟨α, hα, hsm⟩ := reproduce_of_lap E a ν hν p hp0
  refine ⟨α, hα, fun φ hφ => hsm φ ?_⟩
  have e : ∑ i, c i • A i = lapOp E a := by
    rw [GlobalTheory.T.leftInvariantLaplacian_eq_casimir_decomposition E a, Fintype.sum_option]; rfl
  rw [← e]
  refine hp φ ?_
  rintro (_ | τ)
  · exact hq φ hφ.2.2.1
  · obtain ⟨χ', hχ', hN⟩ := hφ.2.2.2
    rw [Set.mem_singleton_iff] at hχ'
    subst hχ'
    have h := hN (List.replicate N (Formalism.REAL.Cas (Eop τ))) (List.length_replicate ..)
      (fun z hz => (List.eq_of_mem_replicate hz) ▸ GlobalTheory.T.casimir_glFactor_embedding_mem_capelliAlgebra E a τ)
    rw [foldr_replicate] at h
    exact h

end GlobalTheory.HCAlphaEll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorHigherLevelPointsEqOfSameImage
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.UPel.HT.LiftUniq

theorem eq_of_same_image : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (M' : Model b N') (π : M'.X ⟶ S), π ≫ s = M'.s → ∀ (om : ObjMap (M'.univ.forget N hd hc) o π) (T : Scheme.{0}) (g₁ g₂ : T ⟶ M'.X), g₁ ≫ π = g₂ ≫ π → (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ om.φ = g₂ ≫ (M'.univ.eta a).left ≫ om.φ) → g₁ = g₂ := by
  intro p _ D R _ b N N' hd hc S s o M' π hπ om T g₁ g₂ hg hη
  obtain ⟨o₁, ⟨m₁⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D R b N' M'.X T M'.s g₁ M'.univ
  obtain ⟨ψ, ψ₂, hcart, hsq, hact0, hpol, hη'⟩ : ∃ (ψ : M'.univ.A.left ⟶ o.A.left)
      (ψ₂ : (M'.univ.A ⊗ M'.univ.A).left ⟶ (o.A ⊗ o.A).left), IsGrpPullback M'.univ.A o.A π ψ ∧
      IsSquare ψ ψ₂ ∧ (∀ c, (M'.univ.act.act c).left ≫ ψ = ψ ≫ (o.act.act c).left) ∧
      Nonempty (LBIso M'.univ.P (o.P.pull ψ₂)) ∧
      (∀ a, g₁ ≫ (M'.univ.eta a).left ≫ ψ = g₂ ≫ (M'.univ.eta a).left ≫ ψ) :=
    ⟨om.φ, om.φ₂, om.cart, om.sq, om.act, ⟨om.pol⟩, hη⟩
  obtain ⟨hpol⟩ := hpol
  clear hη
  have hpb : IsPullback ψ M'.univ.A.hom o.A.hom π := hcart.1
  have w : (m₁.φ ≫ ψ) ≫ o.A.hom = (o₁.A.hom ≫ g₂) ≫ π := by
    have h2 : m₁.φ ≫ M'.univ.A.hom = o₁.A.hom ≫ g₁ := m₁.cart.1.w
    rw [Category.assoc, hpb.w, ← Category.assoc, h2, Category.assoc, hg, Category.assoc]
  obtain ⟨φ, hφ, hφ'⟩ : ∃ φ : o₁.A.left ⟶ M'.univ.A.left, φ ≫ ψ = m₁.φ ≫ ψ ∧
      φ ≫ M'.univ.A.hom = o₁.A.hom ≫ g₂ :=
    ⟨hpb.lift _ _ w, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have n : IsGrpPullback o₁.A o.A (g₂ ≫ π) (φ ≫ ψ) := by
    rw [hφ, ← hg]; exact m₁.cart.comp hcart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m₁.φ₂ ≫ ψ₂ = φ₂ ≫ ψ₂ :=
    isSquare_unique (isSquare_comp m₁.sq hsq) (hφ ▸ isSquare_comp sq hsq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (M'.univ.act.act c).left := by
    intro c
    apply hpb.hom_ext
    · rw [Category.assoc, hφ, ← Category.assoc, m₁.act, Category.assoc, hact0, Category.assoc, hact0,
        ← Category.assoc, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = g₂ ≫ (M'.univ.eta y).left := by
    intro y
    apply hpb.hom_ext
    · rw [Category.assoc, hφ, ← Category.assoc, m₁.eta, Category.assoc, Category.assoc]
      exact hη' y
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ g₂ = g₂ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  have pol : LBIso o₁.P (M'.univ.P.pull φ₂) :=
    LBIso.trans o₁.isLB (pull_isLB o.isLB _) (pull_isLB M'.univ.isLB _)
      (LBIso.trans o₁.isLB (pull_isLB M'.univ.isLB _) (pull_isLB o.isLB _) m₁.pol
        (lbIso_pull_comp hpol m₁.φ₂ rfl))
      (LBIso.symm (lbIso_pull_comp hpol φ₂ e))
  let m₂ : ObjMap o₁ M'.univ g₂ :=
    { φ := φ, φ₂ := φ₂, cart := hcart.cancel n hφ', sq := sq, act := hact, pol := pol, eta := heta }
  have h2 : g₂ ≫ M'.s = g₁ ≫ M'.s := by rw [← hπ, ← Category.assoc, ← hg, Category.assoc]
  exact ((M'.rep T (g₁ ≫ M'.s) o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨h2, ⟨m₂⟩⟩)

end GlobalTheory.UPel.HT.LiftUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundle
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.DiagComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

theorem diag_comp (m : ObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply pullback.hom_ext
  · have h1 := m.sq.1
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (fst o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (fst o.A o.A).left = _ ≫ (fst o.A o.A).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := m.sq.2
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (snd o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (snd o.A o.A).left = _ ≫ (snd o.A o.A).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso (m : ObjMap o' o f) :
    LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) := by
  have h₁ : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp m.pol _ (diag_comp m).symm
  have h₂ : LBIso ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ)
      (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB o.isLB _)) m.φ rfl
  exact LBIso.trans (pull_isLB o'.isLB _) (pull_isLB o.isLB _) (pull_isLB (pull_isLB o.isLB _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.DiagComp

namespace GlobalTheory.UPel.HT

theorem objMap_comp_diag_lbIso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), (Nonempty (ObjMap o'' o' f') → Nonempty (ObjMap o' o f) → Nonempty (ObjMap o'' o (f' ≫ f))) ∧ ∀ m : ObjMap o' o f, LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨MapComp.comp m₁ m₂⟩, fun m => DiagComp.diag_lbIso m⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyBoundTwistNegOfRegularSectionStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherCohomology_bound_twist_neg_of_regular_section' : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (B : LB X) (hB : B.IsLB) (s : B.Sec), Mono (cutHom F hB s) → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twistZ F B (-1)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.higherCohomology_bound_twist_neg_of_regular_section | exact GlobalTheory.higherCohomology_bound_twist_neg_of_regular_section | (intros; apply GlobalTheory.higherCohomology_bound_twist_neg_of_regular_section <;> assumption)
end

