module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0002
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0003
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamFour
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.ChirpCharacterAdd

variable {F : Type} [Field F] [NumberField F]

private noncomputable def eM (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-2⁻¹, 2⁻¹, 0, 0; 2⁻¹, 2⁻¹, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private noncomputable def eN (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-1, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem two_ne (F : Type) [Field F] [NumberField F] : (2 : F) ≠ 0 := two_ne_zero

private theorem eNM (F : Type) [Field F] [NumberField F] : eN F * eM F = 1 := by
  have h := two_ne F
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eN, eM, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private theorem eMN (F : Type) [Field F] [NumberField F] : eM F * eN F = 1 := by
  have h := two_ne F
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eN, eM, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private theorem e_apply (v : V4 F) :
    (eM F).map (algebraMap F (A F)) *ᵥ v =
      ![rt (2⁻¹ : F) * (v 1 - v 0), rt (2⁻¹ : F) * (v 1 + v 0), v 2, v 3] := by
  ext1 i
  fin_cases i <;>
    simp [eM, Matrix.mulVec, dotProduct, Fin.sum_univ_four, rt] <;> ring

private theorem psi_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem q_eq (δ : F) (b : A F) (v : V4 F) :
    b * q4 δ v = b * (rt (2⁻¹ : F) * (v 1 - v 0)) ^ 2 + (-b) * (rt (2⁻¹ : F) * (v 1 + v 0)) ^ 2
      + b * (v 2) ^ 2 + (-(rt δ * b)) * (v 3) ^ 2 := by
  have h : rt (2⁻¹ : F) * 2 = 1 := by
    have h2 : rt (2 : F) = 2 := map_ofNat _ 2
    rw [← h2, rt, rt, ← map_mul, inv_mul_cancel₀ (two_ne F), map_one]
  unfold q4
  linear_combination ((b * v 1 * v 0) * (rt (2⁻¹ : F) * 2 + 1)) * h

end UpperTheory.ConvolutionTheory.R2.C.ChirpCharacterAdd

open UpperTheory.ConvolutionTheory.R2.C.ChirpCharacterAdd in
theorem UpperTheory.ConvolutionTheory.R2.C.lamFour :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : A F) (φ : A F → ℂ), Lam4 δ b (four φ) = Lam1 b φ * Lam1 (-b) φ * Lam1 b φ * Lam1 (-(rt δ * b)) φ := by
  intro F _ _ δ b φ
  have hp := GroundTheory.Heights₂.Theta.measurePreserving_mulVec (K := F) (ι := Fin 4) (κ := Fin 4)
    (eM F) (eN F) (eNM F) (eMN F)
  let e : V4 F ≃ᵐ V4 F :=
    (GroundTheory.Heights₂.Theta.mulVecHomeomorph (eM F) (eN F) (A F) (eNM F) (eMN F)).toMeasurableEquiv
  have he : ∀ v, e v = ![rt (2⁻¹ : F) * (v 1 - v 0), rt (2⁻¹ : F) * (v 1 + v 0), v 2, v 3] :=
    fun v => e_apply v
  have hadd : ∀ x y, e (x + y) = e x + e y := fun x y =>
    Matrix.mulVec_add _ x y
  have hmap : (adeleMeasurePi F (ι := Fin 4)).map e = (1 : ENNReal) • adeleMeasurePi F (ι := Fin 4) := by
    rw [one_smul]
    exact hp.map_eq
  let γ : Fin 4 → A F → ℂ :=
    ![fun x => ψ (b * x ^ 2), fun x => ψ ((-b) * x ^ 2), fun x => ψ (b * x ^ 2),
      fun x => ψ ((-(rt δ * b)) * x ^ 2)]
  have h3 := ((UpperTheory.ConvolutionTheory.R2.C.lamGen.2.2 (V4 F) (V4 F) (adeleMeasurePi F (ι := Fin 4))
    (adeleMeasurePi F (ι := Fin 4)) e 1 hadd hmap (fun v => ∏ i, γ i (v i))
    (fun v => ∏ i, φ (v i))).1)
  have h2 := UpperTheory.ConvolutionTheory.R2.C.lamGen.2.1 (Fin 4) (A F) (adeleMeasure F) γ (fun _ => φ)
  have hγ : (fun x : V4 F => ∏ i, γ i (e x i)) = fun v => ψ (b * q4 δ v) := by
    funext v
    rw [q_eq, psi_add, psi_add, psi_add, Fin.prod_univ_four, he]
    rfl
  have hφ : (fun x : V4 F => ∏ i, φ (e x i)) = four φ := by
    funext v
    rw [Fin.prod_univ_four, he]
    rfl
  rw [hγ, hφ] at h3
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_pow, one_mul] at h3
  unfold Lam4
  rw [h3]
  change abelian₂ (Measure.pi fun _ : Fin 4 => adeleMeasure F) _ _ = _
  rw [h2, Fin.prod_univ_four]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamOne
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.lamOne :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : FiniteAdeleRing (𝓞 F) F → ℂ), ∃ C : FiniteAdeleRing (𝓞 F) F → ℂ, ∀ b : (A F)ˣ, Lam1 (b : A F) (g1 g) = C (b : A F).2 * ∏ w, lamR (TR.pInf F (b : A F) w) := by
  intro F _ _ _ g
  obtain ⟨⟨e, c, he, hmap⟩, hψ⟩ := splitA F
  refine ⟨fun β => ((c.toReal : ℝ) : ℂ) ^ 2 * abelian₂ (finiteAdeleMeasure F)
    (fun x => ((finiteAdelicChar F (β * x ^ 2) : Circle) : ℂ)) g, fun b => ?_⟩
  have hne : ∀ w, TR.pInf F (b : A F) w ≠ 0 := by
    intro w h0
    have h1 : TR.pInf F (b : A F) * TR.pInf F ((b⁻¹ : (A F)ˣ) : A F) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrFun h1 w
    rw [Pi.mul_apply, h0, zero_mul] at h2
    exact zero_ne_one h2
  let γi : InfinitePlace F → ℝ → ℂ := fun w x =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F (b : A F) w : ℝ) : ℂ) * (x : ℂ) ^ 2)
  let φi : InfinitePlace F → ℝ → ℂ := fun _ x => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)
  let γf : FiniteAdeleRing (𝓞 F) F → ℂ := fun x => ((finiteAdelicChar F ((b : A F).2 * x ^ 2) : Circle) : ℂ)
  have hadd : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    simp only [he, map_add (f := _)]
    rfl
  have h3 := (lamGen.2.2 (A F) ((InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F) (adeleMeasure F) _ e c hadd hmap
    (fun p => (∏ w, γi w (p.1 w)) * γf p.2) (fun p => (∏ w, φi w (p.1 w)) * g p.2)).1
  have h1 := lamGen.1 (InfinitePlace F → ℝ) (FiniteAdeleRing (𝓞 F) F) volume (finiteAdeleMeasure F)
    (fun v => ∏ w, γi w (v w)) (fun v => ∏ w, φi w (v w)) γf g
  have h2 := lamGen.2.1 (InfinitePlace F) ℝ volume γi φi
  have h4 : ∀ w, abelian₂ (volume : Measure ℝ) (γi w) (φi w) = lamR (TR.pInf F (b : A F) w) :=
    fun w => lamReal _ (hne w)
  have hγ : (fun x : A F => ψ ((b : A F) * x ^ 2)) =
      fun x => (∏ w, γi w ((e x).1 w)) * γf (e x).2 := by
    funext x
    rw [hψ, he]
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      have : TR.pInf F ((b : A F) * x ^ 2) w = TR.pInf F (b : A F) w * (TR.pInf F x w) ^ 2 := by
        rw [map_mul, map_pow]
        rfl
      simp only [γi]
      rw [this]
      push_cast
      ring_nf
  have hφ : g1 g = fun x : A F => (∏ w, φi w ((e x).1 w)) * g (e x).2 := by
    funext x
    rw [he]
    rfl
  have hL : Lam1 (b : A F) (g1 g) = abelian₂ (adeleMeasure F) (fun x : A F => ψ ((b : A F) * x ^ 2)) (g1 g) := rfl
  have hv : (volume : Measure (InfinitePlace F → ℝ)) = Measure.pi fun _ => volume := volume_pi
  rw [hL, hγ, hφ, h3, h1, hv, h2]
  simp only [h4]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NbBasis
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem val_coe {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a : F) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) a) v) = v.valuation F a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a

private theorem dv_iff {F : Type} [Field F] [NumberField F] (m : F) (hm : m ≠ 0) (x : A F) :
    Dv m x ↔ algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2 ∈ integralFiniteAdeles (𝓞 F) F := by
  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) v) ≤ 1 ↔
        Valued.v (x.2 v) ≤ v.valuation F m) := by
    intro v
    have h0 : v.valuation F m ≠ 0 := (Valuation.ne_zero_iff _).2 hm
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) v =
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹) v * x.2 v := rfl
    rw [e, Valuation.map_mul, val_coe, map_inv₀, mul_comm, ← div_eq_mul_inv]
    exact div_le_one₀ (zero_lt_iff.2 h0)
  constructor
  · intro h v
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ((key v).2 (h v))
  · intro h v
    exact (key v).1 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h v))

theorem UpperTheory.ConvolutionTheory.R2.C.nbBasis :
    ∀ (F : Type) [Field F] [NumberField F], (∀ U ∈ 𝓝 (0 : A F), ∃ m : F, m ≠ 0 ∧ Dv 1 (rt m) ∧ ∀ x : A F, x.1 = 0 → Dv m x → x ∈ U) ∧
    ∀ m : F, m ≠ 0 → ∀ᶠ x in 𝓝 (0 : A F), Dv m x := by
  intro F _ _
  constructor
  · intro U hU
    have hc : Continuous (fun y : FiniteAdeleRing (𝓞 F) F => ((0, y) : A F)) :=
      continuous_const.prodMk continuous_id
    have hW : (fun y : FiniteAdeleRing (𝓞 F) F => ((0, y) : A F)) ⁻¹' U ∈
        𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := hc.continuousAt.preimage_mem_nhds hU
    obtain ⟨d, hd0, hd⟩ := exists_forall_mul_mem_of_mem_nhds hW
    have hm : algebraMap (𝓞 F) F d ≠ 0 := by
      simpa using hd0
    refine ⟨algebraMap (𝓞 F) F d, hm, ?_, ?_⟩
    · intro v
      have : Valued.v ((rt (algebraMap (𝓞 F) F d) : A F).2 v) = v.valuation F (algebraMap (𝓞 F) F d) :=
        val_coe v _
      rw [this, map_one]
      exact v.valuation_le_one d
    · intro x hx1 hx
      have hy := hd _ ((dv_iff _ hm x).1 hx)
      have e : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
          (algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d)⁻¹ * x.2) = x.2 := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hm, map_one, one_mul]
      rw [e] at hy
      have h3 : ((0, x.2) : A F) ∈ U := hy
      rwa [show ((0, x.2) : A F) = x from Prod.ext hx1.symm rfl] at h3
  · intro m hm
    have hc : Continuous (fun x : A F => algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) :=
      continuous_const.mul continuous_snd
    have hO : IsOpen ((fun x : A F => algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) ⁻¹'
        (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
      isOpen_integralFiniteAdeles.preimage hc
    have h0 : (0 : A F) ∈ ((fun x : A F => algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * x.2) ⁻¹'
        (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) := by
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) m⁻¹ * (0 : FiniteAdeleRing (𝓞 F) F) ∈
        (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
      rw [mul_zero]
      exact (integralFiniteAdeles (𝓞 F) F).zero_mem
    filter_upwards [hO.mem_nhds h0] with x hx
    exact (dv_iff m hm x).2 hx
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Place
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem place {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (val : Valuation K Γ)
    (c d mm : K) (hc : val c ≤ 1) (hm : val mm ≤ 1) (hd : val (d - 1) ≤ val mm ^ 2)
    (hcd : val c = 1 ∨ val d = 1) (e : K) (he : e = if val d = 1 then 0 else 1) :
    val (d + c * e) = 1 ∧ val e ≤ val mm ∧ val ((d + c * e)⁻¹ - 1) ≤ val mm ^ 2 := by
  have hm2 : val mm ^ 2 ≤ 1 := pow_le_one' hm 2
  have hd1 : val d ≤ 1 := by
    have : d = (d - 1) + 1 := by ring
    rw [this]
    refine (val.map_add _ _).trans (max_le (hd.trans hm2) (by simp))
  by_cases h : val d = 1
  · simp only [h, if_true] at he
    subst he
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at h
    refine ⟨by simpa using h, by simp, ?_⟩
    have : (d + c * 0)⁻¹ - 1 = (-(d - 1)) * d⁻¹ := by
      rw [mul_zero, add_zero, neg_sub, sub_mul, mul_inv_cancel₀ hd0, one_mul]
    rw [this, map_mul, map_inv₀, Valuation.map_neg, h]
    simpa using hd
  · simp only [h, if_false] at he
    subst he
    have hlt : val d < 1 := lt_of_le_of_ne hd1 h
    have hc1 : val c = 1 := hcd.resolve_right h
    have hv1 : val (d - 1) = 1 := by
      rw [Valuation.map_sub_eq_of_lt_right val (by simpa using hlt)]
      simp
    have hmm : 1 ≤ val mm ^ 2 := hv1 ▸ hd
    have hm1 : val mm ^ 2 = 1 := le_antisymm hm2 hmm
    have hmv : val mm = 1 := by
      refine le_antisymm hm ?_
      by_contra hlt'
      have : val mm < 1 := not_le.mp hlt'
      have := pow_lt_one₀ zero_le' this (two_ne_zero)
      exact absurd hm1 this.ne
    have hu : val (d + c * 1) = 1 := by
      rw [mul_one, Valuation.map_add_eq_of_lt_right val (by rwa [hc1]), hc1]
    refine ⟨hu, by simp [hmv], ?_⟩
    rw [hm1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (by simp))
    rw [map_inv₀, hu]
    simp

theorem UpperTheory.ConvolutionTheory.R2.C.lvEps :
    ∀ (F : Type) [Field F] [NumberField F] (m : F), m ≠ 0 → Dv 1 (rt m) → ∀ c d : A F, c.1 = 0 → d.1 = 1 → Dv 1 c → Dv (m ^ 2) (d - 1) →
    (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (c.2 v) = 1 ∨ Valued.v (d.2 v) = 1) →
    ∃ (u : (A F)ˣ) (ε x y : A F), Dv 1 (u : A F) ∧ Dv 1 ((u⁻¹ : (A F)ˣ) : A F) ∧ (ε.1 = 0 ∧ Dv m ε) ∧ (x.1 = 0 ∧ Dv m x) ∧ (y.1 = 0 ∧ Dv m y) ∧
      d + c * ε = u ∧ ((u⁻¹ : (A F)ˣ) : A F) = 1 + x * y := by
  intro F _ _ m hm0 hm c d hc1 hd1 hc hd hcd
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((rt m).2 v) = v.valuation F m :=
    fun v => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v m
  have hminv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((rt m⁻¹).2 v) = (v.valuation F m)⁻¹ :=
    fun v => (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v m⁻¹).trans (map_inv₀ _ _)
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (1 : F) = 1 := fun v => map_one _
  let e : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F :=
    fun v => if Valued.v (d.2 v) = 1 then 0 else 1
  have he_int : ∀ v : HeightOneSpectrum (𝓞 F), e v ∈ v.adicCompletionIntegers F := by
    intro v
    by_cases h : Valued.v (d.2 v) = 1
    · simp only [e, h, if_true]
      exact zero_mem _
    · simp only [e, h, if_false]
      exact one_mem _
  let ef : FiniteAdeleRing (𝓞 F) F := ⟨e, Filter.Eventually.of_forall he_int⟩
  let ε : A F := ((0 : InfiniteAdeleRing F), ef)
  have key : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (d.2 v + c.2 v * e v) = 1 ∧ Valued.v (e v) ≤ Valued.v ((rt m).2 v) ∧
      Valued.v ((d.2 v + c.2 v * e v)⁻¹ - 1) ≤ Valued.v ((rt m).2 v) ^ 2 := by
    intro v
    refine place Valued.v (c.2 v) (d.2 v) ((rt m).2 v) ?_ ?_ ?_ (hcd v) (e v) rfl
    · have := hc v
      rwa [hone] at this
    · have := hm v
      rwa [hone] at this
    · have := hd v
      rw [map_pow, ← hmv] at this
      exact this
  have hinf : (d + c * ε).1 = 1 := by
    show d.1 + c.1 * ε.1 = 1
    rw [hd1, hc1, zero_mul, add_zero]
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), (d + c * ε).2 v = d.2 v + c.2 v * e v := fun v => rfl
  have hU : IsUnit (d + c * ε) := by
    refine (UpperTheory.ConvolutionTheory.R2.C.unitA F _).2 ⟨fun w => ?_, fun v => ?_, Filter.Eventually.of_forall fun v => ?_⟩
    · rw [hinf]
      exact one_ne_zero
    · intro h0
      have := (key v).1
      rw [← hfin, h0, map_zero] at this
      exact zero_ne_one this
    · rw [hfin]
      exact (key v).1
  obtain ⟨u, hu⟩ := hU
  have huv : ∀ v : HeightOneSpectrum (𝓞 F), (u : A F).2 v = d.2 v + c.2 v * e v := by
    intro v
    rw [hu]
    rfl
  have hui : ∀ v : HeightOneSpectrum (𝓞 F), ((u⁻¹ : (A F)ˣ) : A F).2 v = ((u : A F).2 v)⁻¹ := by
    intro v
    have h1 : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := u.mul_inv
    have h2 : (u : A F).2 v * ((u⁻¹ : (A F)ˣ) : A F).2 v = 1 := congrArg (fun z : A F => z.2 v) h1
    exact (inv_eq_of_mul_eq_one_right h2).symm
  have hu1 : (u : A F).1 = 1 := by rw [hu, hinf]
  have hui1 : ((u⁻¹ : (A F)ˣ) : A F).1 = 1 := by
    have h1 : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := u.mul_inv
    have h2 : (u : A F).1 * ((u⁻¹ : (A F)ˣ) : A F).1 = 1 := congrArg Prod.fst h1
    rwa [hu1, one_mul] at h2
  have hpq : (rt m).2 * (rt m⁻¹).2 = (1 : FiniteAdeleRing (𝓞 F) F) := by
    have h1 : rt m * rt m⁻¹ = (1 : A F) := by
      rw [← map_mul, mul_inv_cancel₀ hm0, map_one]
    exact congrArg Prod.snd h1
  refine ⟨u, ε, ((0 : InfiniteAdeleRing F), (rt m).2),
    ((0 : InfiniteAdeleRing F), (((u⁻¹ : (A F)ˣ) : A F) - 1).2 * (rt m⁻¹).2), ?_, ?_, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, hu.symm, ?_⟩
  · intro v
    rw [huv, (key v).1, hone]
  · intro v
    rw [hui, map_inv₀, huv, (key v).1, hone, inv_one]
  · intro v
    rw [← hmv]
    exact (key v).2.1
  · intro v
    exact (hmv v).le
  · intro v
    have hne : v.valuation F m ≠ 0 := (Valuation.ne_zero_iff _).2 hm0
    have h1 : Valued.v ((((u⁻¹ : (A F)ˣ) : A F) - 1).2 v) ≤ v.valuation F m ^ 2 := by
      have h2 : (((u⁻¹ : (A F)ˣ) : A F) - 1).2 v = (d.2 v + c.2 v * e v)⁻¹ - 1 := by
        rw [← huv, ← hui]
        rfl
      rw [h2, ← hmv]
      exact (key v).2.2
    have h3 : ((((0 : InfiniteAdeleRing F), (((u⁻¹ : (A F)ˣ) : A F) - 1).2 * (rt m⁻¹).2) : A F)).2 v =
        (((u⁻¹ : (A F)ˣ) : A F) - 1).2 v * (rt m⁻¹).2 v := rfl
    rw [h3, map_mul, hminv]
    calc _ ≤ v.valuation F m ^ 2 * (v.valuation F m)⁻¹ := mul_le_mul_left h1 _
      _ = v.valuation F m := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  · refine Prod.ext ?_ ?_
    · show ((u⁻¹ : (A F)ˣ) : A F).1 = 1 + 0 * _
      rw [hui1, zero_mul, add_zero]
    · show ((u⁻¹ : (A F)ˣ) : A F).2 = 1 + (rt m).2 * ((((u⁻¹ : (A F)ˣ) : A F).2 - 1) * (rt m⁻¹).2)
      linear_combination (-(((u⁻¹ : (A F)ˣ) : A F).2 - 1)) * hpq
end

