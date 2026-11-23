module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0001
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0200
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructure
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ConjTransposeMemGLs
section
noncomputable section

open MeasureTheory Matrix Finset Filter
open scoped ContDiff ComplexConjugate Topology ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.UnitaryConjTransposeTrace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contOn_inv : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have h : ∀ y ∈ GLs n, y⁻¹ = (y.det)⁻¹ • y.adjugate := fun y _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContinuousOn.congr ?_ h
  exact ContinuousOn.smul ((continuous_id.matrix_det).continuousOn.inv₀ fun y hy => hy)
    (continuous_id.matrix_adjugate).continuousOn

theorem mem_GLs_mul {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n :=
  (Matrix.isUnit_nonsing_inv_det x (isUnit_iff_ne_zero.2 hx)).ne_zero

theorem conjTranspose_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : xᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_conjTranspose, star_ne_zero] at *
  exact hx

theorem tw_mem {x d : Mat n} (hx : x ∈ GLs n) (hd : d ∈ GLs n) : x⁻¹ * d * xᴴ⁻¹ ∈ GLs n :=
  mem_GLs_mul (mem_GLs_mul (inv_mem_GLs hx) hd) (inv_mem_GLs (conjTranspose_mem_GLs hx))

theorem val_mem (x : G n) : (x : Mat n) ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit x)).ne_zero

theorem tw_val (x d : G n) : ((tw x d : G n) : Mat n) = (x : Mat n)⁻¹ * d * (x : Mat n)ᴴ⁻¹ := by
  simp only [tw, th, Units.val_mul, Matrix.coe_units_inv, Units.coe_star, Matrix.star_eq_conjTranspose]

def trL (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] : (V →L[ℂ] V) →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ)

theorem trL_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (A : V →L[ℂ] V) :
    trL V A = LinearMap.trace ℂ V (A : V →ₗ[ℂ] V) := rfl

theorem trL_cont (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] : Continuous (trL V) :=
  LinearMap.continuous_of_finiteDimensional _

theorem trL_mul_comm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A B : V →L[ℂ] V) : trL V (A * B) = trL V (B * A) := by
  simp only [trL_apply, ContinuousLinearMap.toLinearMap_mul]
  exact LinearMap.trace_mul_comm ℂ _ _

theorem sigma_mem {σ : (Fin n × Fin n → ℝ) → Mat n} (hσ2 : ∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) {v} (hv : v ∈ cone n) :
    σ v ∈ GLs n := by
  have h1 : (hOf v).det ≠ 0 := (show (hOf v).PosDef from hv).det_pos.ne'
  rw [← hσ2 v hv, Matrix.det_mul] at h1
  exact left_ne_zero_of_mul h1

theorem end1 : End1 := by
  intro n lam E Fr ε ι S Γ T hCx _ _ μ _ σ c hσ hσ2 hform k hk hkeq hkΓ d R hR
  set Fm : Mat n → ℂ := fun y => trL E.V (k (y⁻¹ * d.val * yᴴ⁻¹) * T) with hFm
  have hdG := val_mem d
  have harg : ContinuousOn (fun y : Mat n => y⁻¹ * d.val * yᴴ⁻¹) (GLs n) :=
    (contOn_inv.mul continuousOn_const).mul
      (contOn_inv.comp (continuous_id.matrix_conjTranspose).continuousOn fun y hy => conjTranspose_mem_GLs hy)
  have hFmcont : ContinuousOn Fm (GLs n) :=
    (trL_cont E.V).comp_continuousOn ((hk.comp harg fun y hy => tw_mem hy hdG).mul continuousOn_const)
  have hFmsupp : ∃ R, ∀ y ∈ GLs n, R < lg y → Fm y = 0 :=
    ⟨R, fun y hy h => by simp only [hFm, hR y hy h, zero_mul, map_zero]⟩
  have hFmK : ∀ y ∈ GLs n, ∀ kk : Matrix.unitaryGroup (Fin n) ℂ, Fm (y * kk.1) = Fm y := by
    intro y hy kk
    have hu : kk.1ᴴ * kk.1 = 1 := Matrix.UnitaryGroup.star_mul_self kk
    have hu' : kk.1 * kk.1ᴴ = 1 := by
      have := Matrix.mem_unitaryGroup_iff.mp kk.2
      simpa [Matrix.star_eq_conjTranspose] using this
    have hinv : kk.1⁻¹ = kk.1ᴴ := Matrix.inv_eq_left_inv hu
    have hinvH : kk.1ᴴ⁻¹ = kk.1 := Matrix.inv_eq_left_inv hu'
    have e : (y * kk.1)⁻¹ * d.val * (y * kk.1)ᴴ⁻¹ = (kk⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 * (y⁻¹ * d.val * yᴴ⁻¹) * kk.1 := by
      rw [Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_inv_rev, hinvH, hinv]
      have : (kk⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = kk.1ᴴ := by
        rw [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose]
      rw [this]
      simp only [Matrix.mul_assoc]
    simp only [hFm]
    rw [e, hkeq _ (tw_mem hy hdG)]
    rw [show E.ρ kk⁻¹ * k (y⁻¹ * d.val * yᴴ⁻¹) * E.ρ kk * T = E.ρ kk⁻¹ * (k (y⁻¹ * d.val * yᴴ⁻¹) * T) * E.ρ kk by
      rw [mul_assoc (E.ρ kk⁻¹ * k _) (E.ρ kk) T, ← hCx.TK kk]; simp only [mul_assoc]]
    rw [trL_mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hcone : ∀ v ∈ cone n, trL E.V (Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v)) =
      ((c : ℂ) * ((hOf v).det ^ n)⁻¹) * Fm (σ v) := by
    intro v hv
    have hx := sigma_mem hσ2 hv
    simp only [Kc, Kf, hCx.S1, mul_one, mul_smul_comm, map_smul, smul_eq_mul, hFm]
    congr 1
    have hw := tw_mem hx hdG
    have h1 : Fr (σ v)⁻¹ * Fr (σ v) = 1 := by
      rw [← hCx.mul _ (inv_mem_GLs hx) _ hx, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hx), hCx.one]
    calc trL E.V (Γ * (Fr (σ v) * k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹))
        = trL E.V (Fr (σ v) * (Γ * k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹)) := by
          rw [show Γ * (Fr (σ v) * k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹) =
              (Γ * Fr (σ v)) * (k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹) by simp only [mul_assoc],
            hCx.ΓFr _ hx]
          simp only [mul_assoc]
      _ = trL E.V ((Γ * k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * Γ * T * Fr (σ v)⁻¹) * Fr (σ v)) := trL_mul_comm _ _
      _ = trL E.V (k ((σ v)⁻¹ * d.val * (σ v)ᴴ⁻¹) * T) := by
          rw [mul_assoc _ (Fr (σ v)⁻¹), h1, mul_one, hkΓ _ hw, mul_assoc (k _) Γ Γ, hCx.Γsq, mul_one]
  have hcontTw : Continuous (fun x : G n => (x : Mat n)⁻¹ * d.val * (x : Mat n)ᴴ⁻¹) :=
    ((contOn_inv.comp_continuous Units.continuous_val val_mem).mul continuous_const).mul
      (contOn_inv.comp_continuous (Units.continuous_val.matrix_conjTranspose) fun x => conjTranspose_mem_GLs (val_mem x))
  have hphi : (fun x : G n => phiOf E T k (tw x d)) = fun x : G n => Fm (x : Mat n) := by
    funext x
    simp only [phiOf, hFm, trL_apply, tw_val]
  have hcont : Continuous (fun x : G n => Fm (x : Mat n)) :=
    (trL_cont E.V).comp ((hk.comp_continuous hcontTw fun x => tw_mem (val_mem x) hdG).mul continuous_const)
  have hcs : HasCompactSupport (fun x : G n => Fm (x : Mat n)) := by
    refine HasCompactSupport.intro (_root_.GlobalTheory.CompanionTheory.LgBound.lgCpt n R) fun x hx => ?_
    simp only [Set.mem_ofPred_eq, not_le] at hx
    simp only [hFm, hR _ (val_mem x) hx, zero_mul, map_zero]
  refine ⟨hphi ▸ hcont.integrable_of_hasCompactSupport hcs, ?_⟩
  rw [hphi, hform Fm hFmcont hFmsupp hFmK, ← integral_const_mul]
  refine setIntegral_congr_fun (_root_.GlobalTheory.CompanionTheory.ConeHaar.coneSt n).1.measurableSet (fun v hv => ?_)
  rw [show Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v) = Γ * S 1 * Kc σ c Fr k Γ T d.val (v, v) from rfl]
  have := hcone v hv
  simp only [trL_apply] at this
  rw [this]; ring

end PositivityTheory.RgBcC.LfSt.UnitaryConjTransposeTrace
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.GelfandReading
section
noncomputable section

open Matrix Filter
open scoped ContDiff Topology ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.GelfandReading

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def coordsL (n : ℕ) : Mat n →L[ℝ] (Fin n × Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := coords
      map_add' := fun A B => by
        funext p
        simp [coords, Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun r A => by
        funext p
        simp [coords, Matrix.trace_smul] }

theorem coordsL_apply (A : Mat n) : coordsL n A = coords A := rfl

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_compl_singleton.preimage (continuous_id.matrix_det)

theorem eq_of_mul_conj {Z : Type} {F : Mat n → Z}
    (hFk : ∀ x ∈ GLs n, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, F (x * k.1) = F x)
    {a b : Mat n} (hb' : b ∈ GLs n) (h : a * aᴴ = b * bᴴ) : F a = F b := by
  have hb0 : b.det ≠ 0 := hb'
  have hd : IsUnit b.det := Ne.isUnit hb0
  have hkk : (b⁻¹ * a) * (b⁻¹ * a)ᴴ = 1 := by
    have e1 : b⁻¹ * a * (b⁻¹ * a)ᴴ = b⁻¹ * (a * aᴴ) * b⁻¹ᴴ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have e2 : b⁻¹ * (b * bᴴ) * b⁻¹ᴴ = (b⁻¹ * b) * (b⁻¹ * b)ᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [e1, h, e2, Matrix.nonsing_inv_mul b hd, conjTranspose_one, Matrix.one_mul]
  have hmem : b⁻¹ * a ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hkk
  have key := hFk b hb' ⟨_, hmem⟩
  simp only at key
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv b hd, Matrix.one_mul] at key
  exact key

theorem cone_mem_GLs {σ : (Fin n × Fin n → ℝ) → Mat n} (hσ2 : ∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) {v}
    (hv : v ∈ cone n) : σ v ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq]
  intro hdet
  have hp : PosDef (hOf v) := hv
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit
  rw [← hσ2 v hv, det_mul, hdet, zero_mul] at hu
  exact not_isUnit_zero hu

theorem frameDer_of (hHb : HbFacts) : FrameDer := by
  intro n Z _ _ σ F hσ hσ2 hF hFk v hv x hx hxv X hX
  rw [show ((2 : ℂ) • (x * X * xᴴ)) = (2 : ℕ) • (x * X * xᴴ) by rw [two_smul, two_nsmul]]
  obtain ⟨-, -, hcoords, hcoords', -, -, -, -⟩ := hHb n
  have hopen : IsOpen (cone n) := (_root_.GlobalTheory.CompanionTheory.ConeHaar.coneSt n).1
  have hexp : ∀ t : ℝ, (x + t • (x * X)) * (x + t • (x * X))ᴴ =
      x * xᴴ + t • ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • ((x * X) * (x * X)ᴴ) := by
    intro t
    simp only [conjTranspose_add, conjTranspose_smul, star_trivial, conjTranspose_mul, hX.eq,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    module
  have hw : ∀ t : ℝ, coords ((x + t • (x * X)) * (x + t • (x * X))ᴴ) =
      v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ) := by
    intro t
    rw [hexp t, ← coordsL_apply, map_add (f := _), map_add (f := _), map_smul (coordsL n) t, map_smul (coordsL n) (t ^ 2),
      coordsL_apply, coordsL_apply, coordsL_apply, hxv, hcoords']
  have hhOf : ∀ t : ℝ, hOf (v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ)) =
      (x + t • (x * X)) * (x + t • (x * X))ᴴ := by
    intro t
    rw [← hw t]
    exact hcoords _ (isHermitian_mul_conjTranspose_self _)
  have hwd : HasDerivAt (fun t : ℝ => v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ))
      (coords ((2 : ℕ) • (x * X * xᴴ))) 0 := by
    have h1 := ((hasDerivAt_id (0:ℝ)).smul_const (coords ((2 : ℕ) • (x * X * xᴴ)))).const_add v
    have h2 := (hasDerivAt_pow 2 (0:ℝ)).smul_const (coords ((x * X) * (x * X)ᴴ))
    exact (h1.add h2).congr_deriv (by simp)
  have hγd : HasDerivAt (fun t : ℝ => x + t • (x * X)) (x * X) 0 :=
    (((hasDerivAt_id (0:ℝ)).smul_const (x * X)).const_add x).congr_deriv (by simp)
  have hFx : HasFDerivAt F (fderiv ℝ F x) x :=
    ((hF.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)).hasFDerivAt
  have hmaps : Set.MapsTo σ (cone n) (GLs n) := fun w hw' => cone_mem_GLs hσ2 hw'
  have hFσ : HasFDerivAt (fun w => F (σ w)) (fderiv ℝ (fun w => F (σ w)) v) v :=
    (((hF.comp hσ hmaps).differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hv)).hasFDerivAt
  have d1 : HasDerivAt (fun t : ℝ => F (x + t • (x * X))) (fderiv ℝ F x (x * X)) 0 :=
    hFx.comp_hasDerivAt_of_eq 0 hγd (by simp)
  have d2 : HasDerivAt (fun t : ℝ => F (σ (v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ))))
      (fderiv ℝ (fun w => F (σ w)) v (coords ((2 : ℕ) • (x * X * xᴴ)))) 0 :=
    hFσ.comp_hasDerivAt_of_eq 0 hwd (by simp)
  have hev : (fun t : ℝ => F (x + t • (x * X))) =ᶠ[nhds 0]
      (fun t : ℝ => F (σ (v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ)))) := by
    have hin : ∀ᶠ t in nhds (0:ℝ),
        v + t • coords ((2 : ℕ) • (x * X * xᴴ)) + t ^ 2 • coords ((x * X) * (x * X)ᴴ) ∈ cone n :=
      hwd.continuousAt.preimage_mem_nhds (by simpa using hopen.mem_nhds hv)
    filter_upwards [hin] with t ht
    exact eq_of_mul_conj hFk (cone_mem_GLs hσ2 ht) (by rw [hσ2 _ ht, hhOf t])
  exact (d2.congr_of_eventuallyEq hev).unique d1

end PositivityTheory.RgBcC.LfSt.GelfandReading
end
end

