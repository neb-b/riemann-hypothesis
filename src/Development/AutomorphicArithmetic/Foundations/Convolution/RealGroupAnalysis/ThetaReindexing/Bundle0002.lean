module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierEqAdelic
public import GroundTheory.HeightsAndTheta.Theta.Weil.PartialFourierCoordinates
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.AbMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

private theorem exHom {G V : Type} [Group G] (S : Submodule ℂ (V → ℂ)) (c : G → ℂ) (a : G → V → V)
    (c1 : c 1 = 1) (cm : ∀ g h, c (g * h) = c g * c h) (a1 : ∀ v, a 1 v = v)
    (am : ∀ g h v, a (g * h)⁻¹ v = a h⁻¹ (a g⁻¹ v))
    (hm : ∀ g, ∀ f ∈ S, (fun v => f (a g⁻¹ v)) ∈ S) :
    ∃ L : G →* Module.End ℂ S, ∀ g f v, (L g f).1 v = c g * f.1 (a g⁻¹ v) := by
  have hmem : ∀ (g : G) (f : S), (fun v => c g * f.1 (a g⁻¹ v)) ∈ S := fun g f =>
    S.smul_mem (c g) (hm g f.1 f.2)
  let T : G → Module.End ℂ S := fun g =>
    { toFun := fun f => ⟨_, hmem g f⟩
      map_add' := by
        intro f f'
        apply Subtype.ext
        funext v
        simp [mul_add]
      map_smul' := by
        intro k f
        apply Subtype.ext
        funext v
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine ⟨{ toFun := T, map_one' := ?_, map_mul' := ?_ }, fun g f v => rfl⟩
  · apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext v
    show c 1 * f.1 (a 1⁻¹ v) = f.1 v
    rw [c1, one_mul, inv_one, a1]
  · intro g h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext v
    show c (g * h) * f.1 (a (g * h)⁻¹ v) = c g * (c h * f.1 (a h⁻¹ (a g⁻¹ v)))
    rw [cm, am, mul_assoc]

private theorem abMul {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) : ab (s * t) = ab s * ab t := by
  simp only [ab, map_mul]
  rfl

private theorem abOne {F : Type} [Field F] [NumberField F] : ab (1 : (A F)ˣ) = 1 := by
  simp only [ab, map_one]
  rfl

private theorem nuMul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (g h : GL (Fin 2) (A E)) : nu F (g * h) = nu F g * nu F h := by
  simp only [nu, map_mul]

private theorem nuOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    nu F (1 : GL (Fin 2) (A E)) = 1 := by
  simp only [nu, map_one]

theorem UpperTheory.ConvolutionTheory.R2.D.lEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), ∃ L : GL (Fin 2) (A E) →* Module.End ℂ (S4 F),
    ∀ h φ v, (L h φ).1 v = (((ab (nu F h))⁻¹ : ℝ) : ℂ) * φ.1 (D.act h⁻¹ v) := by
  intro F E _ _ _ _ _ D
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  refine exHom (schwartzBruhatPi (K := F) (ι := Fin 4)) (fun h => (((ab (nu F h))⁻¹ : ℝ) : ℂ)) D.act ?_ ?_ ?_ ?_ ?_
  · show (((ab (nu F (1 : GL (Fin 2) (A E))))⁻¹ : ℝ) : ℂ) = 1
    rw [nuOne, abOne]
    simp
  · intro g h
    show (((ab (nu F (g * h)))⁻¹ : ℝ) : ℂ) = (((ab (nu F g))⁻¹ : ℝ) : ℂ) * (((ab (nu F h))⁻¹ : ℝ) : ℂ)
    rw [nuMul, abMul, mul_inv]
    push_cast
    rfl
  · intro v
    rw [hρ, map_one]
    exact Matrix.one_mulVec v
  · intro g h v
    rw [hρ, hρ, hρ, _root_.mul_inv_rev, map_mul]
    exact (Matrix.mulVec_mulVec v _ _).symm
  · intro g f hf
    have h1 := UpperTheory.ConvolutionTheory.R2.D.sClos F (Fin 4) (ρ g⁻¹) f hf
    have h2 : (fun v => f (D.act g⁻¹ v)) = fun v => f ((ρ g⁻¹).val *ᵥ v) := by
      funext v
      rw [hρ]
    rw [h2]
    exact h1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActRat
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem mkE_rt (D : Dat F E) (u t : F) :
    D.mkE (rt u) (rt t) = rt (algebraMap F E u + algebraMap F E t * D.θ) := by
  simp only [Dat.mkE, rt, AdeleBaseChange.adeleMap_algebraMap, map_add (f := _), map_mul]

private theorem bar_rt (D : Dat F E) (z : E) : D.bar (rt z) = rt (D.σ z) :=
  AdeleBaseChange.smul_algebraMap D.σ z

private theorem co_rt (D : Dat F E) (z : E) (i : Fin 2) : D.co (rt z) i = rt (D.b.repr z i) :=
  AdeleBaseChange.adeleBasis_repr_algebraMap D.b z i

private theorem herm_rt (D : Dat F E) (ξ : Fin 4 → F) :
    D.herm (fun i => rt (ξ i)) =
      (!![algebraMap F E (ξ 1) + algebraMap F E 0 * D.θ, algebraMap F E (ξ 2) + algebraMap F E (ξ 3) * D.θ;
        algebraMap F E (ξ 2) + algebraMap F E (-ξ 3) * D.θ, algebraMap F E (ξ 0) + algebraMap F E 0 * D.θ]).map
        (algebraMap E (A E)) := by
  have e0 : ∀ u : F, D.mkE (rt u) 0 = rt (algebraMap F E u + algebraMap F E 0 * D.θ) := fun u => by
    rw [← mkE_rt, show (rt (0 : F) : A F) = 0 from map_zero _]
  have e3 : D.mkE (rt (ξ 2)) (-rt (ξ 3)) = rt (algebraMap F E (ξ 2) + algebraMap F E (-ξ 3) * D.θ) := by
    rw [← mkE_rt, show (rt (-ξ 3) : A F) = -rt (ξ 3) from map_neg _ _]
  ext i j
  fin_cases i <;> fin_cases j
  · exact e0 _
  · exact mkE_rt D _ _
  · exact e3
  · exact e0 _

variable [_root_.NumberField.IsTotallyComplex E]

private theorem ab_nu (γ : GL (Fin 2) E) : ab (nu F (ratGL E 2 γ)) = 1 := by
  have hd : Matrix.GeneralLinearGroup.det (ratGL E 2 γ) =
      IdeleGroup.diagonal E (Matrix.GeneralLinearGroup.det γ) := Units.ext (by
    change (ratGL E 2 γ).val.det = algebraMap E (A E) γ.val.det
    rw [RingHom.map_det]
    rfl)
  rw [nu, hd, ideleNorm_diagonal, ab, IdeleGroup.ideleModule_diagonal]
  rfl

private theorem act_rat (D : Dat F E) (γ : GL (Fin 2) E) (ξ : Fin 4 → F) :
    ∃ ξ' : Fin 4 → F, D.act (ratGL E 2 γ) (fun i => rt (ξ i)) = fun i => rt (ξ' i) := by
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) E, D.herm (fun i => rt (ξ i)) = X.map (algebraMap E (A E)) := ⟨_, herm_rt D ξ⟩
  have hh : (ratGL E 2 γ).val = γ.val.map (algebraMap E (A E)) := rfl
  have hb : (ratGL E 2 γ).val.map D.bar = (γ.val.map D.σ).map (algebraMap E (A E)) := by
    ext i j
    exact bar_rt D (γ.val i j)
  set P : Matrix (Fin 2) (Fin 2) E := γ.val * X * (γ.val.map D.σ)ᵀ with hP
  have hm : (ratGL E 2 γ).val * D.herm (fun i => rt (ξ i)) * ((ratGL E 2 γ).val.map D.bar)ᵀ =
      P.map (algebraMap E (A E)) := by
    rw [hX, hb, hh, hP, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  refine ⟨![D.b.repr (P 1 1) 0, D.b.repr (P 0 0) 0, D.b.repr (P 0 1) 0, D.b.repr (P 0 1) 1], ?_⟩
  rw [Dat.act, hm]
  funext i
  fin_cases i
  · exact co_rt D _ _
  · exact co_rt D _ _
  · exact co_rt D _ _
  · exact co_rt D _ _

end

end UpperTheory.ConvolutionTheory.R2.D

theorem UpperTheory.ConvolutionTheory.R2.D.thL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (γ : GL (Fin 2) E) (φ : V4 F → ℂ),
    Th (fun v => (((ab (nu F (ratGL E 2 γ)))⁻¹ : ℝ) : ℂ) * φ (D.act (ratGL E 2 γ)⁻¹ v)) = Th φ := by
  intro F E _ _ _ _ _ _ D γ φ
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hmul : ∀ h h' v, D.act (h * h') v = D.act h (D.act h' v) := by
    intro h h' v
    rw [hρ, hρ, hρ, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  have hone : ∀ v, D.act 1 v = v := by
    intro v
    rw [hρ, map_one, Units.val_one, Matrix.one_mulVec]
  have hinj : Function.Injective (fun (ξ : Fin 4 → F) (i : Fin 4) => (rt (ξ i) : A F)) := by
    intro a b hab
    funext i
    exact AdeleRing.algebraMap_injective (𝓞 F) F (congrFun hab i)
  choose f hf using fun (g : GL (Fin 2) E) (ξ : Fin 4 → F) => UpperTheory.ConvolutionTheory.R2.D.act_rat D g ξ
  have hinv : ∀ (g : GL (Fin 2) E) ξ, f g⁻¹ (f g ξ) = ξ := by
    intro g ξ
    apply hinj
    change (fun i => (rt (f g⁻¹ (f g ξ) i) : A F)) = fun i => rt (ξ i)
    rw [← hf g⁻¹ (f g ξ), ← hf g ξ, ← hmul, ← map_mul, inv_mul_cancel, map_one, hone]
  let e : (Fin 4 → F) ≃ (Fin 4 → F) :=
    ⟨f γ⁻¹, f γ, fun ξ => by simpa using hinv γ⁻¹ ξ, hinv γ⟩
  simp only [Th, UpperTheory.ConvolutionTheory.R2.D.ab_nu, inv_one, Complex.ofReal_one, one_mul, ← map_inv, hf]
  exact e.tsum_eq fun ξ => φ fun i => rt (ξ i)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.FinSumFinEquiv
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv

private theorem slice_mem {F : Type} [Field F] [NumberField F] {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (a b : A F) :
    (fun z : Fin 2 → A F => f ![a, b, z 0, z 1]) ∈ schwartzBruhatPi (K := F) (ι := Fin 2) := by
  let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv
  let M : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix id e
  let N : Matrix (Fin 2 ⊕ Fin 2) (Fin 4) F := (1 : Matrix (Fin 4) (Fin 4) F).submatrix e id
  have hNM : N * M = 1 := by
    ext i j
    simp [M, N, Matrix.mul_apply, Matrix.one_apply]
  have hMN : M * N = 1 := by
    ext i j
    have h := Equiv.sum_comp e
      (fun k => (1 : Matrix (Fin 4) (Fin 4) F) i k * (1 : Matrix (Fin 4) (Fin 4) F) k j)
    rw [Matrix.mul_apply]
    refine h.trans ?_
    simp [Matrix.one_apply]
  have hv : ∀ x : Fin 2 ⊕ Fin 2 → A F, M.map (algebraMap F (A F)) *ᵥ x = fun i => x (e.symm i) := by
    intro x
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.submatrix_apply, id]
    rw [← Equiv.sum_comp e.symm]
    simp [Matrix.one_apply, apply_ite]
  have h1 := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi M N hNM hMN hf
  have h2 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 ![a, b]
  have h3 : (fun z : Fin 2 → A F => f ![a, b, z 0, z 1]) =
      fun x : Fin 2 → A F => f (M.map (algebraMap F (A F)) *ᵥ Sum.elim ![a, b] x) := by
    funext z
    rw [hv]
    congr 1
    funext i
    fin_cases i <;> simp [e, finSumFinEquiv] <;> rfl
  rw [h3]
  exact h2

private def scaleEquiv {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) :
    (Fin 2 → F) ≃ (Fin 2 → F) where
  toFun ξ := ![2 * ξ 0, -2 * δ * ξ 1]
  invFun ξ := ![ξ 0 / 2, -(ξ 1) / (2 * δ)]
  left_inv ξ := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
  right_inv ξ := by
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp

end UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv

open UpperTheory.ConvolutionTheory.R2.D.SliceScalingEquiv in
theorem UpperTheory.ConvolutionTheory.R2.D.rowW :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (r₀ r₁ : F) φ, ThRow (rt r₀) (rt r₁) (W.Om (wW F) φ).1 = ThRow (rt (-r₁)) (rt r₀) φ.1 := by
  intro F E _ _ _ _ _ _ _ D W r₀ r₁ φ
  have hδ : D.δ ≠ 0 := by
    intro h0
    have hθ : D.θ = 0 := by
      have h := D.sq
      rw [h0, map_zero] at h
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    have hb : D.b 1 = 0 := by rw [D.b1, hθ]
    exact D.b.ne_zero 1 hb
  have hS : (W.Om (wW F) φ).1 = ft4 D.δ φ.1 := funext (W.Om_w φ)
  set G : (Fin 2 → A F) → ℂ := fun z => hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] with hGdef
  have hG : G ∈ schwartzBruhatPi (K := F) (ι := Fin 2) :=
    slice_mem (UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1 (-rt r₁) (rt r₀)
  have hR : ThRow (rt (-r₁)) (rt r₀) φ.1 = ∑' ξ : Fin 2 → F, G fun i => algebraMap F (A F) (ξ i) := by
    simp only [ThRow, hGdef, map_neg]
  rw [hR, tsum_algebraMap_eq_tsum_adelicFourierPi hG,
    ← (scaleEquiv D.δ hδ).tsum_eq (fun ξ : Fin 2 → F => adelicFourierPi F G fun i => algebraMap F (A F) (ξ i))]
  unfold ThRow
  refine tsum_congr fun ξ => ?_
  rw [hS, UpperTheory.ConvolutionTheory.R2.D.hatW F D.δ φ _ hδ]
  simp only [adelicFourierPi, Fin.sum_univ_two]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hGdef, ψ, scaleEquiv, Equiv.coe_fn_mk]
  have key : 2 * (z 0 * rt (ξ 0) - rt D.δ * (z 1 * rt (ξ 1))) =
      z 0 * algebraMap F (A F) (2 * ξ 0) + z 1 * algebraMap F (A F) (-2 * D.δ * ξ 1) := by
    simp only [rt, map_mul, map_neg, map_ofNat]
    ring
  show hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] *
      ((adelicChar F (2 * (z 0 * rt (ξ 0) - rt D.δ * (z 1 * rt (ξ 1)))) : Circle) : ℂ) =
    hat φ.1 ![-rt r₁, rt r₀, z 0, z 1] *
      ((adelicChar F (z 0 * algebraMap F (A F) (2 * ξ 0) +
        z 1 * algebraMap F (A F) (-2 * D.δ * ξ 1)) : Circle) : ℂ)
  rw [key]
end

