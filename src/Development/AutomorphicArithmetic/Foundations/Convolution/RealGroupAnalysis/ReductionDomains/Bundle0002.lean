module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import GroundTheory.AutomorphicForms.Bundle0022
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
public import GroundTheory.AutomorphicForms.GL2Classical.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.InfNorm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.R2.M

variable {F : Type} [Field F] [NumberField F]

private theorem int_det {R : Type*} [CommRing R] (S : Subring R) {m : Matrix (Fin 2) (Fin 2) R}
    (h : ∀ i j, m i j ∈ S) : m.det ∈ S := by
  rw [Matrix.det_fin_two]
  exact S.sub_mem (S.mul_mem (h 0 0) (h 1 1)) (S.mul_mem (h 0 1) (h 1 0))

private theorem fin_int {k : GL (Fin 2) (A F)} (hk : k ∈ Reduction.maxCompact (K := F) (n := 2))
    (v : HeightOneSpectrum (𝓞 F)) :
    (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer := by
  have h := ((GLnLocal.mem_integralGL_iff _ _).1 (hk.2 v)).1
  have e := GL2Classical.det_finAt_eq v k
  have e' : (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).2 v =
      ((Reduction.finAt v k : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := e
  rw [e']
  exact int_det _ h

private theorem inf_norm {k : GL (Fin 2) (A F)} (hk : k ∈ Reduction.maxCompact (K := F) (n := 2))
    (w : InfinitePlace F) : ‖(((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).1 w‖ = 1 := by
  have e := GL2Classical.det_infAt_eq w k
  have e' : (((Matrix.GeneralLinearGroup.det k : (A F)ˣ) : A F)).1 w =
      ((Reduction.infAt w k : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det := e
  rw [e']
  exact Reduction.norm_det_infAt_of_mem_maxCompact hk w

private theorem dM_mem (t : (A F)ˣ) (h1 : ∀ w : InfinitePlace F, ‖((t : A F)).1 w‖ = 1)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 F), ((t : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 F), (((t⁻¹ : (A F)ˣ) : A F)).2 v ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer) :
    dM t ∈ Reduction.maxCompact (K := F) (n := 2) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · intro y
    have key : Reduction.euclidNorm (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion)) ^ 2 = Reduction.euclidNorm y ^ 2 := by
      rw [Reduction.euclidNorm_sq, Reduction.euclidNorm_sq, Fin.sum_univ_two, Fin.sum_univ_two]
      have a0 : (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion)) 0 = y 0 := by
        simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, dM]
        exact Or.inr rfl
      have a1 : (y ᵥ* ((Reduction.infAt w (dM t) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion)) 1 = y 1 * ((t : A F)).1 w := by
        simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, dM]
        exact Or.inr rfl
      rw [a0, a1, norm_mul, h1 w, mul_one]
    exact (sq_eq_sq₀ (Reduction.euclidNorm_nonneg _) (Reduction.euclidNorm_nonneg _)).1 key
  · rw [GLnLocal.mem_integralGL_iff, ← Reduction.finAt_inv]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [dM, h2 v] <;> change (0 : v.adicCompletion F) ∈ _ <;> exact Subring.zero_mem _
    · fin_cases i <;> fin_cases j <;> simp [dM, h3 v] <;> change (0 : v.adicCompletion F) ∈ _ <;> exact Subring.zero_mem _

end UpperTheory.ConvolutionTheory.R2.M

theorem UpperTheory.ConvolutionTheory.R2.M.detK :
    ∀ (F : Type) [Field F] [NumberField F], ∀ k ∈ Reduction.maxCompact (K := F) (n := 2), dM (Matrix.GeneralLinearGroup.det k) ∈ Reduction.maxCompact (K := F) (n := 2) ∧ ab (Matrix.GeneralLinearGroup.det k) = 1 := by
  intro F _ _ k hk
  refine ⟨dM_mem _ (inf_norm hk) (fin_int hk) fun v => ?_, ?_⟩
  · have := fin_int (inv_mem hk) v
    rwa [map_inv] at this
  · have := GJGlobal.Modulus.ideleModule_det_of_mem_maxCompact' hk
    simp [ab, this]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkFin
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.kkFin :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (k : G1 F) (v : HeightOneSpectrum (𝓞 F)), IntAt v k ↔ Reduction.finAt v (gl k) ∈ GLnLocal.integralGL (v.adicCompletion F) 2 := by
  intro F _ _ k v
  have hinv : (Reduction.finAt v (gl k))⁻¹ = Reduction.finAt v (gl k⁻¹) := by
    have e : ∀ g : GL (Fin 2) (A F), Reduction.finAt v g = Matrix.GeneralLinearGroup.map (Reduction.finEval v) g := by
      intro g; ext i j; rfl
    rw [e, e, ← map_inv, ← map_inv]
  have hent : ∀ (g : G1 F) i j, (Reduction.finAt v (gl g)) i j = (g i j).2 v := fun _ _ _ => rfl
  rw [GLnLocal.mem_integralGL_iff, hinv]
  simp only [hent, GroundTheory.Global.mem_valuationInteger_iff]
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  intro i j
  have e : (k⁻¹ : G1 F).1 = !![k.1 1 1, -k.1 0 1; -k.1 1 0, k.1 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  have hn : ∀ a b, (-(k.1 a b)).2 v ∈ v.adicCompletionIntegers F := fun a b =>
    neg_mem (h a b)
  show ((k⁻¹ : G1 F).1 i j).2 v ∈ _
  rw [e]
  fin_cases i <;> fin_cases j
  · exact h 1 1
  · exact hn 0 1
  · exact hn 1 0
  · exact h 0 0
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.OneVar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem oneVar {F : Type} [Field F] [NumberField F] (f w : A F → ℝ≥0∞) (hf : Measurable f) (hw : Measurable w)
    (hinv : ∀ (ξ : F) b, f (rt ξ + b) = f b) (hsum : ∀ b, ∑' ξ : F, w (rt ξ + b) = 1) :
    ∫⁻ b, f b * w b ∂(adeleMeasure F) = ∫⁻ b in fundamentalSet F, f b ∂(adeleMeasure F) := by
  have hD := isAddFundamentalDomain_fundamentalSet F
  let φ : F → AdeleRing.principalSubgroup (𝓞 F) F := fun ξ => ⟨rt ξ, ξ, rfl⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y h
      exact AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h)
    · rintro ⟨_, ξ, rfl⟩
      exact ⟨ξ, rfl⟩
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := hφ.2.countable
  rw [hD.lintegral_eq_tsum'' (fun b => f b * w b), ← lintegral_tsum]
  · refine lintegral_congr fun x => ?_
    rw [← (Equiv.ofBijective φ hφ).tsum_eq]
    have h1 : ∀ ξ : F, f ((Equiv.ofBijective φ hφ ξ) +ᵥ x) * w ((Equiv.ofBijective φ hφ ξ) +ᵥ x) = f x * w (rt ξ + x) := by
      intro ξ
      change f (rt ξ + x) * w (rt ξ + x) = _
      rw [hinv]
    simp only [h1]
    rw [ENNReal.tsum_mul_left, hsum, mul_one]
  · intro γ
    exact ((hf.mul hw).comp (measurable_const_add (γ : A F))).aemeasurable

theorem UpperTheory.ConvolutionTheory.R2.M.wtInt :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (β u : G1 F → ℝ≥0∞), M.NWt β → Measurable u → (∀ (ξ : F) g, u (nU (rt ξ) * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = M.J0 M₀ fun g => ∫⁻ b in fundamentalSet F, u (nU b * g) ∂(adeleMeasure F) := by
  intro F _ _ M₀ β u hβ hu hinv
  haveI := M₀.prob
  have hnU : Measurable (nU : A F → G1 F) := M.continuous_nU.measurable
  have hmD : Measurable (mD : IdeleGroup F → G1 F) := M.continuous_mD.measurable
  have hy : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    (hmD.comp measurable_fst).mul measurable_snd
  have hI : Measurable fun p : IdeleGroup F × G1 F =>
      ∫⁻ b in fundamentalSet F, u (nU b * (mD p.1 * p.2)) ∂(adeleMeasure F) :=
    Measurable.lintegral_prod_right' (ν := (adeleMeasure F).restrict (fundamentalSet F))
      (f := fun q : (IdeleGroup F × G1 F) × A F => u (nU q.2 * (mD q.1.1 * q.1.2)))
      (hu.comp ((hnU.comp measurable_snd).mul (hy.comp measurable_fst)))
  have hJ : Measurable fun p : IdeleGroup F × G1 F =>
      M.wt p.1 * ∫⁻ b in fundamentalSet F, u (nU b * (mD p.1 * p.2)) ∂(adeleMeasure F) :=
    (M.measurable_wt.comp measurable_fst).mul hI
  rw [M₀.iwasawa (fun g => u g * β g) (hu.mul hβ.1), M.J0, Meas.ν, lintegral_prod_symm _ hJ.aemeasurable]
  refine lintegral_congr fun k => lintegral_congr fun a => ?_
  have hsh : ∀ (ξ : F) (b : A F) (y : G1 F), nU (rt ξ + b) * y = nU (rt ξ) * (nU b * y) := by
    intro ξ b y
    rw [M.nU_add, mul_assoc]
  have hmy : ∀ v : G1 F → ℝ≥0∞, Measurable v → Measurable fun b : A F => v (nU b * (mD a * k)) :=
    fun v hv => hv.comp (hnU.mul_const _)
  have key := oneVar (fun b => u (nU b * (mD a * k))) (fun b => β (nU b * (mD a * k)))
    (hmy u hu) (hmy β hβ.1) (fun ξ b => by simp only [hsh, hinv])
    (fun b => by simp only [hsh]; exact hβ.2 _)
  simp only [mul_assoc (nU _) (mD a) k]
  rw [lintegral_mul_const (f := fun b => u (nU b * (mD a * k)) * β (nU b * (mD a * k))) _
    ((hmy u hu).mul (hmy β hβ.1)), key, mul_comm]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RedDet
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.redDet :
    ∀ (F : Type) [Field F] [NumberField F], ∀ (g : G1 F) (γ : GL (Fin 2) F), ∀ b ∈ Reduction.adelicBorel (K := F) (n := 2), ∀ k : GL (Fin 2) (A F), AdelicGLn.diagonal F 2 γ * gl g = b * k → ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) F, ∃ b' ∈ Reduction.adelicBorel (K := F) (n := 2), gl (ratS F γ' * g) = b' * k ∧ b'.val 0 0 = b.val 0 0 ∧ Reduction.adeleAbs (b'.val 1 1) = Reduction.adeleAbs (b.val 1 1) := by
  intro F _ _ g γ b hb k h
  set d : Fˣ := Matrix.GeneralLinearGroup.det γ with hd
  have hdet : γ.val.det = (d : F) := rfl
  set t : (A F)ˣ := (IdeleGroup.diagonal F d)⁻¹ with ht
  have htv : ((t : (A F)ˣ) : A F) = algebraMap F (A F) ((d⁻¹ : Fˣ) : F) := by
    simp [ht, IdeleGroup.diagonal, ← map_inv]
  let γ' : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![1, 0; 0, ((d⁻¹ : Fˣ) : F)] * γ.val, by
      rw [Matrix.det_mul, hdet, Matrix.det_fin_two_of]; simp⟩
  have hg : gl (ratS F γ') = dM t * AdelicGLn.diagonal F 2 γ := by
    refine Units.ext ?_
    rw [Units.val_mul, val_gl, val_ratS]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [γ', dM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, htv, map_mul]
  obtain ⟨u, hu⟩ := Reduction.isUnit_apply_self_of_mem_adelicBorel hb 1
  have hlow : b.val 1 0 = 0 := Reduction.mem_adelicBorel.1 hb (by decide)
  refine ⟨γ', dM t * b, ?_, ?_, ?_, ?_⟩
  · refine mul_mem (Reduction.mem_adelicBorel.2 ?_) hb
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | (simp [dM]; done) | (simp at hij)
  · have hm : gl (ratS F γ' * g) = gl (ratS F γ') * gl g := map_mul _ _ _
    rw [hm, hg, mul_assoc, h, mul_assoc]
  · simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  · have e : (dM t * b).val 1 1 = ((t * u : (A F)ˣ) : A F) := by
      simp [dM, Matrix.mul_apply, Fin.sum_univ_two, hu]
    rw [e, ← hu, Reduction.adeleAbs_units, Reduction.adeleAbs_units]
    have := ab_mul t u
    have h1 : ab t = 1 := by rw [ht, ab_inv, ab_diag, inv_one]
    rw [h1, one_mul] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.RowCosets
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private def upS {F : Type} [Field F] (ξ : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, ξ; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem upS_val {F : Type} [Field F] (ξ : F) : (upS ξ).1 = !![1, ξ; 0, 1] := rfl

private theorem ratS_upS {F : Type} [Field F] [NumberField F] (ξ : F) : ratS F (upS ξ) = nU (rt ξ) :=
  M.ratS_up ξ

private theorem specialLinear_upper_unipotent {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (h0 : g.1 1 0 = 0) (h1 : g.1 1 1 = 1) : g = upS (g.1 0 1) := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two, h0, h1] at hd
  have hd' : g.1 0 0 = 1 := by simpa using hd
  refine Subtype.ext ?_
  change g.1 = (upS (g.1 0 1)).1
  rw [upS_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, hd']

private theorem ratS_inj {F : Type} [Field F] [NumberField F] :
    Function.Injective (ratS F) := by
  intro a b h
  have hinj : Function.Injective (algebraMap F (A F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  refine Subtype.ext ?_
  ext i j
  apply hinj
  have h2 := congrArg (fun g : G1 F => g.1 i j) h
  simpa [M.val_ratS] using h2

private theorem row_up {F : Type} [Field F] (ξ : F) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (upS ξ * g).1 1 = g.1 1 := by
  ext j
  change ((upS ξ).1 * g.1) 1 j = _
  rw [upS_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.ConvolutionTheory.R2.M.rowCosets :
    ∀ (F : Type) [Field F] [NumberField F], (∃ σ, M.RowSec (F := F) σ) ∧ ∀ σ, M.RowSec (F := F) σ → ∀ γ : Gam F, ∃! p : {r : Fin 2 → F // r ≠ 0} × F, (γ : G1 F) = nU (rt p.2) * ratS F (σ p.1) := by
  intro F _ _
  refine ⟨?_, ?_⟩
  · have hex : ∀ r : {r : Fin 2 → F // r ≠ 0}, ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, g.1 1 = r.1 := by
      rintro ⟨r, hr⟩
      by_cases hc : r 0 = 0
      · have hd : r 1 ≠ 0 := fun hd => hr (by ext i; fin_cases i <;> simp [hc, hd])
        refine ⟨⟨!![(r 1)⁻¹, 0; r 0, r 1], by simp [Matrix.det_fin_two, hd]⟩, ?_⟩
        ext i; fin_cases i <;> simp
      · refine ⟨⟨!![0, -(r 0)⁻¹; r 0, r 1], by simp [Matrix.det_fin_two, hc]⟩, ?_⟩
        ext i; fin_cases i <;> simp
    choose σ hσ using hex
    exact ⟨σ, hσ⟩
  · rintro σ hσ ⟨_, γ0, rfl⟩
    have hr : γ0.1 1 ≠ 0 := by
      intro h
      have hd := γ0.det_coe
      rw [Matrix.det_fin_two] at hd
      have h0 : γ0.1 1 0 = 0 := congrFun h 0
      have h1 : γ0.1 1 1 = 0 := congrFun h 1
      simp [h0, h1] at hd
    obtain ⟨r, hrdef⟩ : ∃ r : {r : Fin 2 → F // r ≠ 0}, r = ⟨γ0.1 1, hr⟩ := ⟨_, rfl⟩
    have hs : (σ r).1 1 = γ0.1 1 := by rw [hσ r, hrdef]
    have hs0 : (σ r).1 1 0 = γ0.1 1 0 := congrFun hs 0
    have hs1 : (σ r).1 1 1 = γ0.1 1 1 := congrFun hs 1
    have hdet : (σ r).1 0 0 * (σ r).1 1 1 - (σ r).1 0 1 * (σ r).1 1 0 = 1 := by
      have hd := (σ r).det_coe
      rwa [Matrix.det_fin_two] at hd
    have e0 : (γ0 * (σ r)⁻¹).1 1 0 = 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp [hs0, hs1]
      ring
    have e1 : (γ0 * (σ r)⁻¹).1 1 1 = 1 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp
      linear_combination hdet - (σ r).1 0 0 * hs1 + (σ r).1 0 1 * hs0
    obtain ⟨ξ, hξ⟩ : ∃ ξ : F, γ0 * (σ r)⁻¹ = upS ξ := ⟨_, specialLinear_upper_unipotent _ e0 e1⟩
    have hγ : γ0 = upS ξ * σ r := by
      rw [← hξ, inv_mul_cancel_right]
    refine ⟨(r, ξ), ?_, ?_⟩
    · show ratS F γ0 = nU (rt ξ) * ratS F (σ r)
      conv_lhs => rw [hγ]
      rw [map_mul, ratS_upS]
    · rintro ⟨r', ξ'⟩ heq
      have heq' : ratS F γ0 = nU (rt ξ') * ratS F (σ r') := heq
      rw [← ratS_upS, ← map_mul] at heq'
      have hγ' := ratS_inj heq'
      have hrr : r' = r := by
        refine Subtype.ext ?_
        rw [← hσ r', ← row_up ξ' (σ r'), ← hγ', hrdef]
      subst hrr
      have hU : upS ξ = upS ξ' := mul_right_cancel (hγ.symm.trans hγ')
      have hξξ : ξ = ξ' := by
        have h2 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.1 0 1) hU
        simpa [upS_val] using h2
      rw [hξξ]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.SumSide
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.sumSide :
    ∀ (X ι : Type) [MeasurableSpace X] [Countable ι] (m : Measure X) (e : ι → X → X), (∀ i, Measurable (e i)) → (∀ u : X → ℝ≥0∞, Measurable u → ∫⁻ x, u x ∂(Measure.sum fun i => m.map (e i)) = ∫⁻ x, ∑' i, u (e i x) ∂m) ∧ ∀ u : X → ℂ, Measurable u → Integrable u (Measure.sum fun i => m.map (e i)) → (∀ᵐ x ∂m, Summable fun i => ‖u (e i x)‖) ∧ Integrable (fun x => ∑' i, u (e i x)) m ∧ ∫ x, ∑' i, u (e i x) ∂m = ∫ x, u x ∂(Measure.sum fun i => m.map (e i)) := by
  intro X ι _ _ m e he
  have hL : ∀ u : X → ℝ≥0∞, Measurable u →
      ∫⁻ x, u x ∂(Measure.sum fun i => m.map (e i)) = ∫⁻ x, ∑' i, u (e i x) ∂m := by
    intro u hu
    have hm : ∀ i, AEMeasurable (fun x => u (e i x)) m := fun i => (hu.comp (he i)).aemeasurable
    rw [lintegral_sum_measure, lintegral_tsum hm]
    exact tsum_congr fun i => lintegral_map hu (he i)
  refine ⟨hL, fun u hu hint => ?_⟩
  have hum : Measurable fun x => ‖u x‖ₑ := hu.enorm
  have hfin : ∫⁻ x, ∑' i, ‖u (e i x)‖ₑ ∂m < ⊤ := by
    rw [← hL _ hum]
    exact hint.2
  have hmeas : Measurable fun x => ∑' i, ‖u (e i x)‖ₑ :=
    Measurable.tsum fun i => hum.comp (he i)
  have hsum : ∀ᵐ x ∂m, Summable fun i => ‖u (e i x)‖ := by
    filter_upwards [ae_lt_top hmeas hfin.ne] with x hx
    have h1 : ∑' i, ((‖u (e i x)‖₊ : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := hx.ne
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  have hsm : ∀ i, AEStronglyMeasurable (fun x => u (e i x)) m := fun i =>
    (hu.comp (he i)).aestronglyMeasurable
  have hlim : ∀ᵐ x ∂m, Tendsto (fun s : Finset ι => ∑ i ∈ s, u (e i x)) atTop
      (𝓝 (∑' i, u (e i x))) := by
    filter_upwards [hsum] with x hx
    exact hx.of_norm.hasSum
  have hae : AEStronglyMeasurable (fun x => ∑' i, u (e i x)) m :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s : Finset ι => Finset.aestronglyMeasurable_fun_sum s fun i _ => hsm i) hlim
  have hI : Integrable (fun x => ∑' i, u (e i x)) m := by
    refine ⟨hae, lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin⟩
    exact enorm_tsum_le_tsum_enorm
  refine ⟨hsum, hI, ?_⟩
  have hne : ∑' i, ∫⁻ x, ‖u (e i x)‖ₑ ∂m ≠ ⊤ := by
    have hm : ∀ i, AEMeasurable (fun x => ‖u (e i x)‖ₑ) m := fun i =>
      (hum.comp (he i)).aemeasurable
    rw [← lintegral_tsum hm]
    exact hfin.ne
  rw [integral_tsum hsm hne, integral_sum_measure hint]
  exact tsum_congr fun i => (integral_map (he i).aemeasurable hu.aestronglyMeasurable).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtA
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtA :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (β u : G1 F → ℝ≥0∞) (c : ℝ≥0∞), Measurable β → (∀ g, ∫⁻ b, β (nU b * g) ∂(adeleMeasure F) = c) → Measurable u → (∀ b g, u (nU b * g) = u g) → ∫⁻ g, u g * β g ∂M₀.μ = c * M.J0 M₀ u := by
  intro F _ _ M₀ β u c hβ hc hu hinv
  haveI := M₀.prob
  have hm : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    ((M.continuous_mD.comp continuous_fst).mul continuous_snd).measurable
  have hJ : Measurable fun p : IdeleGroup F × G1 F => M.wt p.1 * u (mD p.1 * p.2) :=
    (M.measurable_wt.comp measurable_fst).mul (hu.comp hm)
  have hin : ∀ (a : IdeleGroup F) (k : G1 F),
      ∫⁻ b, u (nU b * mD a * k) * β (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2) ∂(adeleMeasure F)
        = c * (M.wt a * u (mD a * k)) := by
    intro a k
    have h1 : ∀ b, u (nU b * mD a * k) * β (nU b * mD a * k) * ENNReal.ofReal ((ab a)⁻¹ ^ 2)
        = (M.wt a * u (mD a * k)) * β (nU b * (mD a * k)) := fun b => by
      rw [mul_assoc (nU b), hinv, M.wt]; ring
    simp_rw [h1]
    have hb : Measurable fun b : A F => β (nU b * (mD a * k)) :=
      hβ.comp ((M.continuous_nU.mul continuous_const).measurable)
    rw [lintegral_const_mul _ hb, hc, mul_comm]
  have hk : Measurable fun k : G1 F => ∫⁻ a, M.wt a * u (mD a * k) ∂(ideleMeasure F) :=
    hJ.lintegral_prod_left'
  have hsec : ∀ k : G1 F, Measurable fun a : IdeleGroup F => M.wt a * u (mD a * k) :=
    fun k => M.measurable_wt.mul (hu.comp ((M.continuous_mD.mul continuous_const).measurable))
  rw [M₀.iwasawa (fun g => u g * β g) (hu.mul hβ), M.J0, Meas.ν, lintegral_prod_symm _ hJ.aemeasurable,
    ← lintegral_const_mul _ hk]
  refine lintegral_congr fun k => ?_
  rw [← lintegral_const_mul _ (hsec k)]
  exact lintegral_congr fun a => hin a k
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.WtEx
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.wtEx :
    ∀ (F : Type) [Field F] [NumberField F], ∃ β : G1 F → ℝ≥0∞, M.NWt β := by
  intro F _ _
  have hinj : Function.Injective (fun ξ : F => (nU (rt ξ : A F) : G1 F)) := by
    intro a b h
    have h1 : (nU (rt a : A F) : G1 F) 0 1 = (nU (rt b : A F) : G1 F) 0 1 := by
      rw [show (nU (rt a : A F) : G1 F) = nU (rt b : A F) from h]
    have h2 : (rt a : A F) = rt b := by simpa [nU] using h1
    exact AdeleRing.algebraMap_injective (𝓞 F) F h2
  let N : Subgroup (G1 F) :=
    { carrier := Set.range fun ξ : F => (nU (rt ξ : A F) : G1 F)
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp only [rt, map_add (f := _), M.nU_add]⟩
      one_mem' := ⟨0, by simp only [rt, map_zero, M.nU_zero]⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, by simp only [rt, map_neg, M.nU_neg]⟩ }
  have hle : N ≤ Gam F := by
    rintro _ ⟨ξ, rfl⟩
    exact M.nU_rt_mem ξ
  haveI : DiscreteTopology N :=
    DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  obtain ⟨D, hD, hu, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup N
  refine ⟨D.indicator 1, measurable_one.indicator hD, fun g => ?_⟩
  obtain ⟨n, hn, huniq⟩ := hu g
  obtain ⟨ξ₀, hξ₀⟩ := n.2
  have hn' : (nU (rt ξ₀ : A F) : G1 F) * g ∈ D := by
    have : (n : G1 F) * g ∈ D := hn
    rwa [← hξ₀] at this
  rw [tsum_eq_single ξ₀]
  · rw [Set.indicator_of_mem hn']
    rfl
  · intro ξ hξ
    refine Set.indicator_of_notMem (fun hmem => hξ ?_) _
    have h1 : (⟨nU (rt ξ : A F), ⟨ξ, rfl⟩⟩ : N) = n := huniq _ hmem
    have h2 : (nU (rt ξ : A F) : G1 F) = n := congrArg Subtype.val h1
    exact hinj (h2.trans hξ₀.symm)
end

