module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.GaussAct
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private noncomputable def cwH (w : InfinitePlace F) : A F →+* ℂ :=
  Complex.ofRealHom.comp ((Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w).comp (TR.pInf F))

private theorem cw_eq (w : InfinitePlace F) (a : A F) : cw w a = cwH w a := rfl

private theorem conj_cw (w : InfinitePlace F) (a : A F) : starRingEnd ℂ (cw w a) = cw w a :=
  Complex.conj_ofReal _

private noncomputable def cE (τ : E →+* ℂ) : A E →+* ℂ := (coord τ).comp (pInf E)

private theorem cE_mk (D : Dat F E) (τ : E →+* ℂ) (u t : A F) :
    cE τ (D.mkE u t) = cw (pl F τ) u + τ D.θ * cw (pl F τ) t :=
  (coordMk F E D).1 τ u t

private theorem cE_bar (D : Dat F E) (τ : E →+* ℂ) (z : A E) :
    cE τ (D.bar z) = starRingEnd ℂ (cE τ z) := by
  obtain ⟨-, hbar, hmk, -⟩ := hermAct F E D
  have hθ := ((coordMk F E D).2.1 τ).2.1
  have hz := hmk z
  generalize D.co z 0 = u at hz
  generalize D.co z 1 = t at hz
  subst hz
  rw [hbar, cE_mk, cE_mk, map_add (f := _), map_mul, hθ, conj_cw, conj_cw, cw_eq _ (-t), map_neg, ← cw_eq]
  ring

private theorem trace_herm (D : Dat F E) (τ : E →+* ℂ) (v : V4 F) :
    Matrix.trace (((D.herm v).map (cE τ)) * ((D.herm v).map (cE τ))) =
      cw (pl F τ) (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) := by
  have hθ := ((coordMk F E D).2.1 τ).1
  have h0 : cw (pl F τ) (0 : A F) = 0 := by rw [cw_eq, map_zero]
  have hn : cw (pl F τ) (-v 3) = -cw (pl F τ) (v 3) := by rw [cw_eq, map_neg, ← cw_eq]
  have hR : cw (pl F τ) (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) =
      cw (pl F τ) (v 0) ^ 2 + cw (pl F τ) (v 1) ^ 2 +
        2 * (cw (pl F τ) (v 2) ^ 2 - cw (pl F τ) (rt D.δ) * cw (pl F τ) (v 3) ^ 2) := by
    simp only [cw_eq, map_add (f := _), map_mul, map_pow, map_sub, map_ofNat]
  rw [hR, ← hθ]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Dat.herm,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    cE_mk, h0, hn]
  ring

private theorem pres (D : Dat F E) (h : GL (Fin 2) (A E))
    (hu : (Matrix.GeneralLinearGroup.map (pInf E) h).val ∈ Matrix.unitaryGroup (Fin 2) (Cinf E))
    (τ : E →+* ℂ) (v : V4 F) :
    Matrix.trace (((D.herm (D.act h v)).map (cE τ)) * ((D.herm (D.act h v)).map (cE τ))) =
      Matrix.trace (((D.herm v).map (cE τ)) * ((D.herm v).map (cE τ))) := by
  set K : Matrix (Fin 2) (Fin 2) ℂ := h.val.map (cE τ) with hK
  set X : Matrix (Fin 2) (Fin 2) ℂ := (D.herm v).map (cE τ) with hX
  have hKK : Kᴴ * K = 1 := by
    have h1 := Matrix.mem_unitaryGroup_iff'.1 hu
    have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Cinf E) => M.map (coord τ)) h1
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, map_sum, map_mul,
      UpperTheory.V.FieldIso.coord_star] at h3
    rw [Matrix.mul_apply]
    simp only [hK, Matrix.conjTranspose_apply, Matrix.map_apply]
    refine h3.trans ?_
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hY : (D.herm (D.act h v)).map (cE τ) = K * X * Kᴴ := by
    rw [((hermAct F E D).1 h v)]
    have hm : ((h.val.map D.bar)ᵀ).map (cE τ) = Kᴴ := by
      ext i j
      simp only [hK, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, cE_bar]
      rfl
    rw [Matrix.map_mul, Matrix.map_mul, hm]
  rw [hY]
  calc Matrix.trace (K * X * Kᴴ * (K * X * Kᴴ))
      = Matrix.trace (K * (X * (Kᴴ * K) * X * Kᴴ)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((X * (Kᴴ * K) * X * Kᴴ) * K) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (X * X * (Kᴴ * K)) := by rw [hKK]; simp only [Matrix.mul_one, Matrix.mul_assoc, hKK]
    _ = Matrix.trace (X * X) := by rw [hKK, Matrix.mul_one]

end

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.gaussAct :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (h : GL (Fin 2) (A E)), (Matrix.GeneralLinearGroup.map (pInf E) h).val ∈ Matrix.unitaryGroup (Fin 2) (Cinf E) →
    ∀ v, gauss D.δ (D.act h v) = gauss D.δ v := by
  intro F E _ _ _ _ _ _ _ D h hu v
  have key : ∀ w : InfinitePlace F,
      TR.pInf F ((D.act h v) 0 ^ 2 + (D.act h v) 1 ^ 2 + 2 * ((D.act h v) 2 ^ 2 - rt D.δ * (D.act h v) 3 ^ 2)) w =
        TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt D.δ * v 3 ^ 2)) w := by
    intro w
    obtain ⟨τ, rfl⟩ := (coordMk F E D).2.2.2 w
    have h1 := pres D h hu τ v
    rw [trace_herm, trace_herm] at h1
    exact Complex.ofReal_injective h1
  unfold gauss
  rw [Finset.sum_congr rfl fun w _ => key w]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.opsEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Nonempty (Ops F) := by
  intro F _ _ _
  have hd : ∀ (w : InfinitePlace F) (i : Fin 4) (φ : S4 F), ∃ φ' : S4 F, ∀ v,
      HasDerivAt (fun t : ℝ => φ.1 (v + Pi.single i (at1 w t))) (φ'.1 v) 0 := by
    intro w i φ
    obtain ⟨φ', h, hs⟩ := dEx F w i φ.1 φ.2
    exact ⟨⟨φ', h⟩, hs⟩
  choose dd hdd using hd
  refine ⟨{
    x := fun w i =>
      { toFun := fun φ => ⟨fun v => cw w (v i) * φ.1 v, xEx F w i φ.1 φ.2⟩
        map_add' := fun φ ψ => by
          apply Subtype.ext
          funext v
          change cw w (v i) * (φ.1 v + ψ.1 v) = cw w (v i) * φ.1 v + cw w (v i) * ψ.1 v
          rw [mul_add]
        map_smul' := fun c φ => by
          apply Subtype.ext
          funext v
          change cw w (v i) * (c * φ.1 v) = c * (cw w (v i) * φ.1 v)
          rw [mul_left_comm] }
    d := fun w i =>
      { toFun := dd w i
        map_add' := fun φ ψ => by
          apply Subtype.ext
          funext v
          have h1 := (hdd w i φ v).add (hdd w i ψ v)
          exact (hdd w i (φ + ψ) v).unique h1
        map_smul' := fun c φ => by
          apply Subtype.ext
          funext v
          have h1 := (hdd w i φ v).const_mul c
          exact (hdd w i (c • φ) v).unique h1 }
    x_apply := fun w i φ v => rfl
    d_spec := fun w i φ v => hdd w i φ v }⟩
end

