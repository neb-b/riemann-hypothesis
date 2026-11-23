module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdjointMemAndExistsIntegralPoint
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.RatElt

theorem hform_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

theorem cT_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT (starRingEnd E) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, conjTranspose_apply, starRingEnd_apply]

theorem unitary_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (τ : B →+* B)
    (f : A →+* B) (hf : ∀ e, τ (f e) = f (σ e)) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) : Formalism.UG.cT τ (g.map f) * J.map f * g.map f = J.map f := by
  have hc : Formalism.UG.cT τ (g.map f) = (Formalism.UG.cT σ g).map f := by
    ext i j
    simp [Formalism.UG.cT, hf]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem exists_point (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hUJ : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J := hγ
  have hγH : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * γ = I.J := by rwa [cT_eq] at hUJ
  let γA : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) :=
    Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom γ
  have hγA : (γA : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := rfl
  have hA : γA ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (γA : Matrix (Fin I.n) (Fin I.n) _) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γA = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [hγA]
    exact unitary_map (starRingEnd I.E) _ _ (fun e => Formalism.UG.P.csDual_sig_incl I.cm.sig e) _ _ hUJ

  let Mu : ∀ v, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Units.map (RingHom.mapMatrix (I.φ v)).toMonoidHom γ * (I.P_unit v).unit
  have hMu : ∀ v, (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [Mu, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hU : ∀ v, Mu v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    show Formalism.REAL.inUJ (I.ε v) (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ)
    unfold Formalism.REAL.inUJ
    set Q := I.P v with hQdef
    set G := (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) with hGdef
    have hQ : Q * Q⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
    have hQH : Q⁻¹ᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
    have hGH : Gᴴ = (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ.map (I.φ v) := by
      ext i j
      simp only [G, conjTranspose_apply, Matrix.map_apply]
      rw [I.cm.cmUnram.2.1 (I.φ v)]
      rfl
    have hGJG : Gᴴ * (I.J.map (I.φ v) * (G * Q)) = I.J.map (I.φ v) * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGH, hGdef, ← Matrix.map_mul, ← Matrix.map_mul, hγH]
    rw [hMu, ← I.P_spec v, ← hQdef, ← hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q⁻¹ᴴ Qᴴ, hQH, Matrix.one_mul, ← Matrix.mul_assoc Q Q⁻¹, hQ, Matrix.one_mul, hGJG]
  exact ⟨⟨fun v => ⟨Mu v, hU v⟩, ⟨γA, hA⟩⟩, fun v => hMu v, hγA⟩

theorem adj_mem (I : AutInst) (x : I.GA) (T : Matrix (Fin I.n) (Fin I.n) I.E)
    (hT : ∀ y ∈ lamX I x, T *ᵥ y ∈ lamX I x) : ∀ y ∈ lamX I x, (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I x := by
  intro y hy
  obtain ⟨-, -, -, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  rw [hdual]
  intro z hz
  have hJ : I.J * I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.J_det)
  have key : Formalism.UG.hform (starRingEnd I.E) I.J z ((I.J⁻¹ * Tᴴ * I.J) *ᵥ y) =
      Formalism.UG.hform (starRingEnd I.E) I.J (T *ᵥ z) y := by
    have hM : I.J * (I.J⁻¹ * Tᴴ * I.J) = Tᴴ * I.J := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
    rw [hform_eq, hform_eq, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec]
  rw [key]
  exact (hdual y).1 hy _ (hT z hz)

private lemma inv_mul_map_inclE_of_mem_lf (I : AutInst) (xf : I.Gf) (δ : Matrix (Fin I.n) (Fin I.n) I.E)
    (hδ : ∀ y ∈ lamX I (1, xf), δ *ᵥ y ∈ lamX I (1, xf))
    (x : Fin I.n → (TensorProduct I.F I.E (Af I.F))) (hx : x ∈ I.Lf) :
    ((((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)))⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * ((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *ᵥ x ∈ I.Lf := by
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds I.F I.E (Fin I.n) I.L hfin I.L_span g
  have hglob : Formalism.UG.CS.globLat g I.L = lamX I (1, xf) := (GlobalTheory.PointLattice.lamX_eq_globLat I (1, xf)).symm
  rw [hglob] at hrec

  have hspan : ∀ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))),
      δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      apply Submodule.subset_span
      refine ⟨δ *ᵥ y, hδ y hy, ?_⟩
      funext i
      exact RingHom.map_mulVec _ _ _ _
    | zero => simp
    | add w₁ w₂ _ _ h₁ h₂ =>
      rw [Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul s w _ h =>
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ s h
  have hu := (hrec ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, ← hL]
    exact hx)
  have h2 := (hrec _).1 (hspan _ hu)
  rw [← hL] at h2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact h2

theorem adj_mem_and_exists_latGroup : ∀ (I : AutInst) (xf : I.Gf), (∀ T : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ lamX I (1, xf), T *ᵥ y ∈ lamX I (1, xf)) → ∀ y ∈ lamX I (1, xf), (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I (1, xf)) ∧ ∀ γ : Matrix (Fin I.n) (Fin I.n) I.E, γᴴ * I.J * γ = I.J → (∀ y ∈ lamX I (1, xf), γ *ᵥ y ∈ lamX I (1, xf)) → ∃ g ∈ latGroup I xf, ∀ v, uMat (g v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v := by
  intro I xf
  refine ⟨fun T hT => adj_mem I (1, xf) T hT, ?_⟩
  intro γ hγJ hγL
  have hdet : γ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hγJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    exact I.J_det h1.symm
  let γu : GL (Fin I.n) I.E := Matrix.nonsingInvUnit γ (isUnit_iff_ne_zero.mpr hdet)
  have hγu : (γu : Matrix (Fin I.n) (Fin I.n) I.E) = γ := rfl
  have hmemUJ : γu ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := by
    show Formalism.UG.cT (starRingEnd I.E) (γu : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γu = I.J
    rw [cT_eq, hγu]
    exact hγJ
  obtain ⟨a, ha1, ha2⟩ := exists_point I γu hmemUJ
  refine ⟨a.1, ⟨a, ⟨γu, hmemUJ, ha1, ha2⟩, rfl, ?_⟩, ha1⟩
  have hδγ : (I.J⁻¹ * γᴴ * I.J) * γ = 1 := by
    rw [show (I.J⁻¹ * γᴴ * I.J) * γ = I.J⁻¹ * (γᴴ * I.J * γ) by simp only [Matrix.mul_assoc], hγJ,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr I.J_det)]
  have hδγA : (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
    rw [← Matrix.map_mul, hδγ]
    simp
  have ha2' : ((a.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    rw [← hγu]
    exact ha2
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hmat : (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Units.val_mul]
    rw [ha2']
  have hprod : (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *
      (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) = 1 := by
    calc _ = ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
            ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hδγA, Matrix.mul_one, Units.inv_mul]
  show ((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) ∈ Formalism.UG.stabGL I.Lf
  unfold Formalism.UG.stabGL
  intro x
  show x ∈ I.Lf ↔ (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x ∈ I.Lf
  rw [hmat]
  constructor
  · intro hx
    exact inv_mul_map_inclE_of_mem_lf I xf γ hγL x hx
  · intro hx
    have h1 := inv_mul_map_inclE_of_mem_lf I xf (I.J⁻¹ * γᴴ * I.J) (adj_mem I (1, xf) γ hγL) _ hx
    rwa [Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] at h1

end GlobalTheory.RadCov.RatElt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFolnerOverlapAverageTendstoForm
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerLimit

theorem mul_mem_GG {k r : ℕ} {g g' : Mat k r} (hg : g ∈ GG k r) (hg' : g' ∈ GG k r) : g * g' ∈ GG k r := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 : g'ᴴ * Hpk k r * g' = Hpk k r := hg'
  show (g * g')ᴴ * Hpk k r * (g * g') = Hpk k r
  calc (g * g')ᴴ * Hpk k r * (g * g') = g'ᴴ * (gᴴ * Hpk k r * g) * g' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2]

theorem DD_stable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (w : H) :
    ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  have hv' : v ∈ DD σ w := hv
  show σ g v ∈ DD σ w
  unfold DD at hv'
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', hg', rfl⟩ := hx
    have := hσ.1.2 g hg g' hg'
    have h2 : σ g (σ g' w) = σ (g * g') w := by rw [this]; rfl
    rw [h2]
    exact mem_DD σ w (mul_mem_GG hg hg')
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add (f := _)]; exact (DD σ w).add_mem (ihx hx) (ihy hy)
  | smul c x hx ih => rw [map_smul]; exact (DD σ w).smul_mem c (ih hx)

theorem measurable_overlap {k r : ℕ} (μ : Measure (Mt k r)) [SFinite μ] {Ω : Set (Mt k r)}
    (hΩ : MeasurableSet Ω) :
    Measurable fun p : Mt k r => μ {s | s ∈ Ω ∧ lmulM (Matrix.of p) s ∈ Ω} := by
  have hc : Continuous fun q : Mt k r × Mt k r => lmulM (Matrix.of q.1) q.2 :=
    Continuous.matrix_mul (A := fun q : Mt k r × Mt k r => (Matrix.of q.1 : Mat k r))
      (B := fun q : Mt k r × Mt k r => (Matrix.of q.2 : Mat k r)) continuous_fst continuous_snd
  have hm : MeasurableSet {q : Mt k r × Mt k r | q.2 ∈ Ω ∧ lmulM (Matrix.of q.1) q.2 ∈ Ω} :=
    (measurable_snd hΩ).inter (hc.measurable hΩ)
  exact measurable_measure_prodMk_left hm

theorem tendsto_of_integrable {k r : ℕ} {S : Set (Mat k r)} {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {Om : ℕ → Set (Mt k r)} (hO : IsFolner S μ Om) {f : Mt k r → ℂ} (hf : Integrable f μ) :
    Filter.Tendsto (fun j => (∫ p, ((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * f p ∂μ)
      / ((μ (Om j)).toReal : ℂ)) Filter.atTop (nhds (∫ p, f p ∂μ)) := by
  haveI : SigmaFinite μ := hμ.1
  have hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
  have heq : ∀ j, (∫ p, ((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * f p ∂μ)
      / ((μ (Om j)).toReal : ℂ) =
      ∫ p, (((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j)).toReal : ℝ) : ℂ) * f p ∂μ := by
    intro j
    rw [← integral_div]
    congr 1
    funext p
    rw [ENNReal.toReal_div]
    push_cast
    ring
  simp only [heq]
  refine tendsto_integral_of_dominated_convergence (fun p => ‖f p‖) (fun j => ?_) hf.norm (fun j => ?_) ?_
  · refine AEStronglyMeasurable.mul ?_ hf.1
    have := ((measurable_overlap μ (hO.1 j).1).div_const (μ (Om j))).ennreal_toReal
    exact (Complex.measurable_ofReal.comp this).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    have h1 : μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j) ≤ 1 :=
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono fun s hs => hs.1)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  · filter_upwards [hae] with p hp
    have h1 := _root_.GlobalTheory.SgInf.folner_single_translate k r S μ Om hO _ hp
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
    have h3 := (Complex.continuous_ofReal.tendsto _).comp h2
    have h4 := h3.mul_const (f p)
    simpa [Function.comp_def] using h4

theorem folner_limit : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → ∀ y ∈ DD σ w, ∀ ξ : Wp, Filter.Tendsto (fun j => (∫ p, ((μS {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * (coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ) ∂μS) / ((μS (Om j)).toReal : ℂ)) Filter.atTop (nhds ⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide Om hO y hy ξ
  have hint := (_root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hStd hSide (DD σ w)
    (DD_stable hStd.2.1 w) hStd.2.2.2.2.2.2.2.1 y hy y hy).1
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hL : ∀ T : Wp →L[ℂ] Wp, L T = ⟪ξ, T ξ⟫_ℂ := fun T => rfl
  have hfun : (fun p : Mt k r => L (coef σ y y (Matrix.of p) • PiS (psiGen k r z c) π (Matrix.of p)⁻¹)) =
      fun p => coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ := by
    funext p
    rw [map_smul, hL, smul_eq_mul]
  have hf := L.integrable_comp hint
  have hI := L.integral_comp_comm hint
  rw [hfun] at hf hI
  have := tendsto_of_integrable hSide.2.2.2.1 hO hf
  rw [hI] at this
  exact this

end GlobalTheory.SgInf.FolnerLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselInnerIntegralEqForm
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.InnerInt

theorem hpk_det_isUnit (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem gg_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ (Hpk k r) (hpk_det_isUnit k r)).2.1 a ha b hb

theorem gg_inv {k r : ℕ} {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det ∧ a⁻¹ ∈ GG k r :=
  (uHGroup _ (Hpk k r) (hpk_det_isUnit k r)).2.2 a ha

theorem inner_map_of_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (u v : H) : ⟪T u, T v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (⟨T.toLinearMap, fun v => hT v⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v

theorem star_coef_mul_eq {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (hσ : IsURepOn (GG k r) σ) (w : H) {y s x : Mat k r}
    (hy : y ∈ GG k r) (hs : s ∈ GG k r) (hx : x ∈ GG k r) :
    star (coef σ w w (y⁻¹ * (s * x))) = coef σ (σ y w) (σ x w) s⁻¹ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  obtain ⟨hyu, hyi⟩ := gg_inv hy
  obtain ⟨hsu, hsi⟩ := gg_inv hs
  have e1 : σ (y⁻¹ * (s * x)) = (σ y⁻¹).comp ((σ s).comp (σ x)) := by
    rw [hmul _ hyi _ (gg_mul hs hx), hmul _ hs _ hx]
  have e2 : ∀ v, σ y (σ y⁻¹ v) = v := by
    intro v
    have h := hmul _ hy _ hyi
    rw [Matrix.mul_nonsing_inv _ hyu, h1] at h
    have := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using this.symm
  have e3 : ∀ v, σ s⁻¹ (σ s v) = v := by
    intro v
    have h := hmul _ hsi _ hs
    rw [Matrix.nonsing_inv_mul _ hsu, h1] at h
    have := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using this.symm
  simp only [coef]
  rw [e1, ← starRingEnd_apply, inner_conj_symm]
  simp only [ContinuousLinearMap.comp_apply]
  have i1 := inner_map_of_norm (σ y) (hiso y hy) (σ y⁻¹ (σ s (σ x w))) w
  rw [e2] at i1
  rw [← i1]
  have i2 := inner_map_of_norm (σ s⁻¹) (hiso _ hsi) (σ s (σ x w)) (σ y w)
  rw [e3] at i2
  rw [← i2]

end GlobalTheory.SgInf.InnerInt


open GlobalTheory.SgInf.InnerInt in
theorem GlobalTheory.SgInf.inner_integral_eq_be : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ W : Mat k r → Wp, IsSPsiEquiv z (psiGen k r z c) π W → ∀ y ∈ GG k r, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ∫ s, star (coef σ w w (y⁻¹ * (Matrix.of s * Matrix.of x))) • W (Matrix.of s * Matrix.of x) ∂μS = be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hstd hside W hW y hy x hx
  have hσ : IsURepOn (GG k r) σ := hstd.2.1
  have hdec : Decay σ (DD σ w : Set H) a := hstd.2.2.2.2.2.2.2.1
  have hz := hside.1
  have hT := hside.2.1
  have hπ := hside.2.2.1
  have hhaar := hside.2.2.2.1
  have hSG : Sset k r z ⊆ GG k r := (_root_.GlobalTheory.SgInf.closedSub_groups k r z hz hT).2.2.2.1.1
  have hpis := _root_.GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hz hT hπ
  have huni := (_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μS).1 hhaar
  have hstab : ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
    intro g hg v hv
    have hle : Submodule.map (σ g).toLinearMap (DD σ w) ≤ DD σ w := by
      rw [DD, Submodule.map_span_le]
      rintro _ ⟨g', hg', rfl⟩
      have : (σ g).toLinearMap (σ g' w) = σ (g * g') w := by
        rw [hσ.1.2 g hg g' hg']; rfl
      rw [this]; exact mem_DD σ w (gg_mul hg hg')
    exact hle ⟨v, hv, rfl⟩
  have hD := _root_.GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous k r σ w a μG d z c π μS hstd hside (DD σ w : Set H) hstab hdec
    (σ y w) (mem_DD σ w hy) (σ (Matrix.of x) w) (mem_DD σ w hx)
  have hFi := hD.1
  have hGi := hFi.apply_continuousLinearMap (W (Matrix.of x))
  have hm : AEStronglyMeasurable (fun s : Mt k r => (coef σ (σ y w) (σ (Matrix.of x) w) (Matrix.of s) •
      PiS (psiGen k r z c) π (Matrix.of s)⁻¹) (W (Matrix.of x))) (μS.map invM) := by
    rw [huni.2]; exact hGi.aestronglyMeasurable
  have hmap := integral_map measurable_invM.aemeasurable hm
  rw [huni.2] at hmap
  unfold be
  rw [ContinuousLinearMap.integral_apply hFi, hmap]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := ae_iff.2 hhaar.2.2.1
  filter_upwards [hae] with s hs
  have hsG := hSG hs
  have hdet := (gg_inv hsG).1
  obtain ⟨h, hh, m, hm', hsm⟩ := hs
  rw [of_invM, Matrix.nonsing_inv_nonsing_inv _ hdet, ContinuousLinearMap.smul_apply,
    star_coef_mul_eq σ hσ w hy hsG hx]
  congr 1
  rw [hsm, hW h hh m hm' _ hx, (hpis.1 h hh m hm').2, ContinuousLinearMap.smul_apply]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BiorthogonalBlockFramesTriangular
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem mul_eq_zero_of_mulVec_mulVec {p q n : ℕ} {A : Matrix (Fin p) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin q) ℂ} (h : ∀ x, A *ᵥ (B *ᵥ x) = 0) : A * B = 0 := by
  ext i j
  have hx := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hx
  simpa using hx

theorem Biorth.col_mem {n m : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (s k : ℕ) (hk : s < k) (x : Fin (r s) → ℂ) : T s *ᵥ x ∈ W k := by
  rw [hW]
  intro b hb
  rw [Matrix.mulVec_mulVec, hT.2.1 b s (by omega), Matrix.zero_mulVec]

theorem Biorth.mul_eq_block {n m p q : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (b : ℕ) {A : Matrix (Fin p) (Fin n) ℂ} {B : Matrix (Fin n) (Fin q) ℂ}
    (hA : ∀ y ∈ W b, A *ᵥ y = 0) (hB : ∀ x, B *ᵥ x ∈ W (b + 1)) :
    A * B = (A * T b) * (T' b * B) := by
  have hAT : ∀ c, c < b → A * T c = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => hA _ (Biorth.col_mem hT hW c b hc x)
  have hTB : ∀ c, b < c → T' c * B = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => (hW (b + 1) _).1 (hB x) c (by omega)
  calc A * B = A * (∑ c ∈ Finset.range m, T c * T' c) * B := by rw [hT.2.2, Matrix.mul_one]
    _ = ∑ c ∈ Finset.range m, (A * T c) * (T' c * B) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    _ = (A * T b) * (T' b * B) := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        rcases lt_or_gt_of_ne hcb with hc | hc
        · rw [hAT c hc, Matrix.zero_mul]
        · rw [hTB c hc, Matrix.mul_zero]
      · intro hb

        have hTb : T b = 0 := by
          rw [← Matrix.one_mul (T b), ← hT.2.2, Matrix.sum_mul]
          apply Finset.sum_eq_zero
          intro c hc
          rw [Matrix.mul_assoc, hT.2.1 c b (by rintro rfl; exact hb hc), Matrix.mul_zero]
        rw [hTb, Matrix.mul_zero, Matrix.zero_mul]

theorem blockFrames_triangular (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ)
    (T U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (T' U' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ)
    (hT : Biorth r m T T') (hU : Biorth r m U U')
    (hWT : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (hWU : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → U' b *ᵥ y = 0) :
    (∀ b, (U' b * T b) * (T' b * U b) = 1) ∧ ∀ c, ∀ Y ∈ lowers W c, ∀ b,
      U' b * Y * U (b + c + 1) =
        (U' b * T b) * (T' b * Y * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) := by
  refine ⟨fun b => ?_, fun c Y hY b => ?_⟩
  · rw [← Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl)
      (fun x => Biorth.col_mem hU hWU b (b + 1) (by omega) x)]
    exact hU.1 b
  · have hY' : ∀ b', ∀ y ∈ W (b' + c + 1), Y *ᵥ y ∈ W b' := mem_lowers.1 hY
    have e1 : U' b * (Y * U (b + c + 1)) = (U' b * T b) * (T' b * (Y * U (b + c + 1))) :=
      Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl) (fun x => by
        rw [← Matrix.mulVec_mulVec]
        exact hY' (b + 1) _ (Biorth.col_mem hU hWU (b + c + 1) (b + 1 + c + 1) (by omega) x))
    have e2 : (T' b * Y) * U (b + c + 1) =
        ((T' b * Y) * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) :=
      Biorth.mul_eq_block hT hWT (b + c + 1)
        (fun y hy => by
          rw [← Matrix.mulVec_mulVec]
          exact (hWT b _).1 (hY' b y hy) b le_rfl)
        (fun x => Biorth.col_mem hU hWU (b + c + 1) (b + c + 1 + 1) (by omega) x)
    calc U' b * Y * U (b + c + 1) = U' b * (Y * U (b + c + 1)) := Matrix.mul_assoc _ _ _
      _ = (U' b * T b) * (T' b * (Y * U (b + c + 1))) := e1
      _ = (U' b * T b) * ((T' b * Y) * U (b + c + 1)) := by rw [Matrix.mul_assoc (T' b)]
      _ = _ := by rw [e2]; simp only [Matrix.mul_assoc]

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLieCoordinatesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_lie_coordinates : ∀ (n d m : ℕ) (ε : Fin n → Bool) (A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), A m = ⊥ → (∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1)) → (∀ c, A (c + 1) ≤ A c) → (∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ i, E i ∈ A 0 ∧ Formalism.REAL.inG ε (E i)) → ∃ σ : (Fin d → ℝ) → Formalism.REAL.UJ ε, Continuous σ ∧ ∀ x, uMat (σ x) - 1 ∈ A 0 ∧ ∀ i, (((uMat (σ x) - 1) * (E i)ᴴ).trace).re = x i := by
  first | exact @GlobalTheory.NilCovSec.exists_continuous_section | exact GlobalTheory.NilCovSec.exists_continuous_section | (intros; apply GlobalTheory.NilCovSec.exists_continuous_section <;> assumption)
end

