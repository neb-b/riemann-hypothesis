module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
public import GroundTheory.GlobalFields.TateThesis.Bundle0005
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LevelVal
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

section Components

variable {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ}

private def cmp (j : Fin d) : S ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] S :=
  (TensorProduct.rid ℂ S).toLinearMap ∘ₗ (LinearMap.proj j : (Fin d → ℂ) →ₗ[ℂ] ℂ).lTensor S

private theorem cmp_tmul (j : Fin d) (φ : S) (v : Fin d → ℂ) : cmp j (φ ⊗ₜ[ℂ] v) = v j • φ := by
  simp [cmp]

private theorem sum_cmp (m : S ⊗[ℂ] (Fin d → ℂ)) :
    ∑ j, cmp j m ⊗ₜ[ℂ] (Pi.single j 1 : Fin d → ℂ) = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp only [cmp_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum]
    congr 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  | add x y hx hy => simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

private theorem cmp_sum (L : Module.End ℂ S) (c : ℂ) (j : Fin d) (m : S ⊗[ℂ] (Fin d → ℂ)) :
    cmp j ((L.rTensor (Fin d → ℂ) + (Matrix.toLin' (c • (1 : Matrix (Fin d) (Fin d) ℂ))).lTensor S) m) =
      L (cmp j m) + c • cmp j m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [cmp_tmul, smul_smul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), smul_add]; abel

end Components

private theorem cmp_apply {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : (cmp j m).1 g = ev m g j := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [cmp_tmul, mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem levelVal : LevelVal := by
  intro E _ _ _ a U Ξ m
  refine ⟨fun hm => ?_, fun hl hr h0 => ?_⟩
  · induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, v, hφ, rfl⟩ := hx
      refine ⟨fun γ g => ?_, fun u hu g => ?_⟩
      · rw [ev_tmul, ev_tmul, hφ.1]
      · have h : φ.1 (g * finGL E a u) = φ.1 g := congrFun (congrArg Subtype.val (hφ.2.1 u hu)) g
        rw [ev_tmul, ev_tmul, h]
    | zero => exact ⟨fun γ g => by simp, fun u _ g => by simp⟩
    | add x y _ _ hx hy =>
      exact ⟨fun γ g => by simp only [map_add (f := _), Pi.add_apply, hx.1 γ g, hy.1 γ g],
        fun u hu g => by simp only [map_add (f := _), Pi.add_apply, hx.2 u hu g, hy.2 u hu g]⟩
    | smul c x _ hx =>
      exact ⟨fun γ g => by simp only [map_smul, Pi.smul_apply, hx.1 γ g],
        fun u hu g => by simp only [map_smul, Pi.smul_apply, hx.2 u hu g]⟩
  · rw [← sum_cmp m]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨cmp j m, _, ⟨fun γ g => ?_, fun u hu => ?_, fun c hc => ?_⟩, rfl⟩
    · rw [cmp_apply, cmp_apply, hl]
    · refine Subtype.ext (funext fun g => ?_)
      change (cmp j m).1 (g * finGL E a u) = (cmp j m).1 g
      rw [cmp_apply, cmp_apply, hr u hu]
    · have h := cmp_sum (lie E a (oneL E a)) c j m
      rw [← hc] at h
      have h1 : cmp j (smLie Ξ (oneL E a) m) = 0 := by rw [h0, map_zero]
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left (h.symm.trans h1)

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af Filter Topology
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def jor (X Y : HV E a) : HV E a :=
  ⟨toL (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1), by
    have hX : star (Matrix.of X.1) = Matrix.of X.1 := X.2
    have hY : star (Matrix.of Y.1) = Matrix.of Y.1 := Y.2
    change star (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) =
      Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1
    rw [star_add, star_mul, star_mul, hX, hY, add_comm]⟩

private def jorL : HV E a →ₗ[ℝ] HV E a →ₗ[ℝ] HV E a :=
  LinearMap.mk₂ ℝ jor
    (fun X X' Y => Subtype.ext (by
      change (Matrix.of X.1 + Matrix.of X'.1) * Matrix.of Y.1 + Matrix.of Y.1 * (Matrix.of X.1 + Matrix.of X'.1) =
        (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) +
          (Matrix.of X'.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X'.1)
      rw [add_mul, mul_add]; abel))
    (fun c X Y => Subtype.ext (by
      change (c • Matrix.of X.1) * Matrix.of Y.1 + Matrix.of Y.1 * (c • Matrix.of X.1) =
        c • (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1)
      rw [smul_mul_assoc, mul_smul_comm, smul_add]))
    (fun X Y Y' => Subtype.ext (by
      change Matrix.of X.1 * (Matrix.of Y.1 + Matrix.of Y'.1) + (Matrix.of Y.1 + Matrix.of Y'.1) * Matrix.of X.1 =
        (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1) +
          (Matrix.of X.1 * Matrix.of Y'.1 + Matrix.of Y'.1 * Matrix.of X.1)
      rw [add_mul, mul_add]; abel))
    (fun c X Y => Subtype.ext (by
      change Matrix.of X.1 * (c • Matrix.of Y.1) + (c • Matrix.of Y.1) * Matrix.of X.1 =
        c • (Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1)
      rw [smul_mul_assoc, mul_smul_comm, smul_add]))

private def jorC : HV E a →L[ℝ] HV E a →L[ℝ] HV E a :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := HV E a) (F' := HV E a)).toLinearMap ∘ₗ jorL)

private theorem jorC_val (X Y : HV E a) :
    Matrix.of (jorC X Y).1 = Matrix.of X.1 * Matrix.of Y.1 + Matrix.of Y.1 * Matrix.of X.1 := rfl

private def sq2 (X : HV E a) : HV E a := (1 / 2 : ℝ) • jorC X X

private theorem square_map_val (X : HV E a) : Matrix.of (sq2 X).1 = Matrix.of X.1 * Matrix.of X.1 := by
  change (1 / 2 : ℝ) • Matrix.of (jorC X X).1 = _
  rw [jorC_val, ← two_smul ℝ, smul_smul]; norm_num

private theorem square_map_one : sq2 (hOne E a) = hOne E a := by
  apply Subtype.ext
  change Matrix.of (sq2 (hOne E a)).1 = Matrix.of (hOne E a).1
  rw [square_map_val, hOne_val, mul_one]

private theorem square_map_contDiff : ContDiff ℝ ∞ (sq2 (E := E) (a := a)) :=
  ((jorC (E := E) (a := a)).contDiff.clm_apply contDiff_id).const_smul _

private def dbl : HV E a ≃L[ℝ] HV E a :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := HV E a) (Units.mk0 (2 : ℝ) two_ne_zero)

private theorem square_map_hasFDerivAt : HasFDerivAt (sq2 (E := E) (a := a)) (dbl (E := E) (a := a) : HV E a →L[ℝ] HV E a) (hOne E a) := by
  have h := (((jorC (E := E) (a := a)).hasFDerivAt (x := hOne E a)).clm_apply (hasFDerivAt_id (hOne E a))).const_smul (1 / 2 : ℝ)
  refine HasFDerivAt.congr_fderiv h ?_
  refine ContinuousLinearMap.ext fun H => Subtype.ext ?_
  change (1 / 2 : ℝ) • (Matrix.of (jorC (hOne E a) H).1 + Matrix.of (jorC H (hOne E a)).1) = (2 : ℝ) • Matrix.of H.1
  rw [jorC_val, jorC_val, hOne_val, mul_one, one_mul]
  module

private theorem exists_sqrt : ∃ σ : HV E a → HV E a, ContDiffAt ℝ ∞ σ (hOne E a) ∧ σ (hOne E a) = hOne E a ∧
    ∀ᶠ p in 𝓝 (hOne E a), sq2 (σ p) = p := by
  have hc : ContDiffAt ℝ ∞ (sq2 (E := E) (a := a)) (hOne E a) := square_map_contDiff.contDiffAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.localInverse square_map_hasFDerivAt hn, ?_, ?_, ?_⟩
  · have := hc.to_localInverse square_map_hasFDerivAt hn
    rwa [square_map_one] at this
  · have := hc.localInverse_apply_image square_map_hasFDerivAt hn
    rwa [square_map_one] at this
  · have := (hc.hasStrictFDerivAt' square_map_hasFDerivAt hn).eventually_right_inverse
    rwa [square_map_one] at this

private theorem ev_unit : ∀ᶠ X in 𝓝 (hOne E a), IsUnit (Matrix.of X.1) := by
  have hc : Continuous fun X : HV E a => (Matrix.of X.1).det :=
    Continuous.matrix_det (A := fun X : HV E a => Matrix.of X.1) continuous_subtype_val
  have h1 : (Matrix.of (hOne E a).1).det ∈ {x : Cinf E | IsUnit x} := by
    rw [hOne_val, det_one]; exact isUnit_one
  filter_upwards [hc.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds h1)] with X hX
  exact (Matrix.isUnit_iff_isUnit_det _).2 hX

private def lmul (g : Matrix (Fin a) (Fin a) (Cinf E)) : HV E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (g * Matrix.of X.1)
      map_add' := fun X Y => by
        change g * (Matrix.of X.1 + Matrix.of Y.1) = g * Matrix.of X.1 + g * Matrix.of Y.1
        rw [mul_add]
      map_smul' := fun c X => by
        change g * (c • Matrix.of X.1) = c • (g * Matrix.of X.1)
        rw [mul_smul_comm] }

open Classical in
theorem locSec : LocSec := by
  rintro E _ _ a p₀ ⟨g, rfl⟩
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := exists_sqrt (E := E) (a := a)
  have h0 : sand g⁻¹ (sand g (hOne E a)) = hOne E a := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have hq : Tendsto (sand g⁻¹) (𝓝 (sand g (hOne E a))) (𝓝 (hOne E a)) := by
    have := (sand g⁻¹).continuous.tendsto (sand g (hOne E a))
    rwa [h0] at this
  have hs : Tendsto σ (𝓝 (hOne E a)) (𝓝 (hOne E a)) := by
    have := hσ.continuousAt.tendsto
    rwa [hσ1] at this
  have hu := (hs.comp hq).eventually ev_unit
  let u : HV E a → GL (Fin a) (Cinf E) := fun X => if h : IsUnit (Matrix.of X.1) then h.unit else 1
  have hval : ∀ X : HV E a, IsUnit (Matrix.of X.1) → (u X).val = Matrix.of X.1 := fun X h => by
    simp only [u, dif_pos h, IsUnit.unit_spec]
  refine ⟨fun p => g * u (σ (sand g⁻¹ p)), ?_, ?_⟩
  · have h1 : ContDiffAt ℝ ∞ (fun p => σ (sand g⁻¹ p)) (sand g (hOne E a)) :=
      ContDiffAt.comp (g := σ) _ (h0.symm ▸ hσ) (sand g⁻¹).contDiff.contDiffAt
    refine ((lmul g.val).contDiff.contDiffAt.comp _ h1).congr_of_eventuallyEq ?_
    filter_upwards [hu] with p hp
    rw [Units.val_mul, hval (σ (sand g⁻¹ p)) hp]; rfl
  · filter_upwards [hu, hq.eventually hσ2] with p hp hp2
    have h2 : sand (u (σ (sand g⁻¹ p))) (hOne E a) = sand g⁻¹ p := by
      rw [← hp2]
      apply Subtype.ext
      change Matrix.of (sand _ _).1 = Matrix.of (sq2 _).1
      have hX : star (Matrix.of (σ (sand g⁻¹ p)).1) = Matrix.of (σ (sand g⁻¹ p)).1 := (σ (sand g⁻¹ p)).2
      rw [sand_val, square_map_val, hOne_val, mul_one, hp2, hval (σ (sand g⁻¹ p)) hp, hX]
    rw [map_mul, ContinuousLinearMap.mul_apply, h2, ← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.MatSmooth
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem smooth_of_formula {f : GL (Fin a) (Cinf E) → ℂ} {F : Lie E a → ℂ} (h : ∀ y, f y = F (toL y.val))
    (hF : ContDiffOn ℝ ∞ F (invSet E a)) : ContDiffOn ℝ ∞ (extGL f) (invSet E a) :=
  hF.congr fun _ hx => (extGL_eventuallyEq h hx).self_of_nhds

private theorem smooth_reg (σ : GL (Fin a) (Cinf E) → GL (Fin a) (Cinf E))
    (h1 : ∀ τ i j, ContDiffOn ℝ ∞ (extGL fun y => coord τ ((σ y).val i j)) (invSet E a))
    (h2 : ∀ τ, ContDiffOn ℝ ∞ (extGL fun y => (coord τ (σ y).val.det)⁻¹) (invSet E a))
    {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    ContDiffOn ℝ ∞ (extGL fun y => f (σ y)) (invSet E a) := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩ := hf
    exacts [h1 τ i j, h2 τ]
  | algebraMap c => exact smooth_of_formula (F := fun _ => c) (fun _ => rfl) contDiffOn_const
  | add f g _ _ hf hg => exact smooth_of_formula (fun y => by simp [extGL_val]) (hf.add hg)
  | mul f g _ _ hf hg => exact smooth_of_formula (fun y => by simp [extGL_val]) (hf.mul hg)

private theorem smooth_det (τ : E →+* ℂ) : ContDiff ℝ ∞ fun x : Lie E a => coord τ (Matrix.of x).det :=
  (coordL τ).contDiff.comp contDiff_det

private theorem smooth_det_inv (τ : E →+* ℂ) :
    ContDiffOn ℝ ∞ (fun x : Lie E a => (coord τ (Matrix.of x).det)⁻¹) (invSet E a) :=
  (smooth_det τ).contDiffOn.inv fun _ hx => (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (coord τ)).ne_zero

private theorem smooth_adj (τ : E →+* ℂ) (i j : Fin a) :
    ContDiff ℝ ∞ fun x : Lie E a => coord τ ((Matrix.of x).adjugate i j) := by
  have h : ContDiff ℝ ∞ fun x : Lie E a => (Function.update x j (Pi.single i 1) : Lie E a) := by
    refine contDiff_pi.2 fun k => ?_
    by_cases hk : k = j
    · subst hk
      simpa using contDiff_const
    · simpa [Function.update_of_ne hk] using contDiff_apply ℝ _ k
  simp only [Matrix.adjugate_apply]
  exact (smooth_det τ).comp h

omit [NumberField E] in
private theorem coord_inv_entry (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) (i j : Fin a) :
    coord τ ((y⁻¹).val i j) = (coord τ y.val.det)⁻¹ * coord τ (y.val.adjugate i j) := by
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have e : y.val.adjugate = y.val.det • (y⁻¹).val := by
    calc y.val.adjugate = (y.val.adjugate * y.val) * (y⁻¹).val := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [Matrix.adjugate_mul, smul_mul_assoc, one_mul]
  rw [e, Matrix.smul_apply, smul_eq_mul, map_mul, inv_mul_cancel_left₀ (hu.map (coord τ)).ne_zero]

omit [NumberField E] in
private theorem coord_inv_det (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) :
    (coord τ (y⁻¹).val.det)⁻¹ = coord τ y.val.det := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one]

theorem matSmooth : MatSmooth := by
  intro E _ _ a Ξ i j
  refine ⟨smooth_reg id (fun τ k l => ?_) (fun τ => ?_) (Ξ.reg i j),
    smooth_reg (fun y => y⁻¹) (fun τ k l => ?_) (fun τ => ?_) (Ξ.reg i j)⟩
  · exact smooth_of_formula (F := fun x => coordL τ (x k l)) (fun _ => rfl) (by fun_prop)
  · exact smooth_of_formula (fun _ => rfl) (smooth_det_inv τ)
  · exact smooth_of_formula (fun y => coord_inv_entry τ y k l) ((smooth_det_inv τ).mul (smooth_adj τ k l).contDiffOn)
  · exact smooth_of_formula (fun y => coord_inv_det τ y) (smooth_det τ).contDiffOn

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.NormFin
section
open UpperTheory.V.Lit.Dr

private theorem one_of_compact {G : Type} [Group G] [TopologicalSpace G] (U : Subgroup G) (hU : IsCompact (U : Set G))
    (φ : G → ℝ) (hc : Continuous φ) (hp : ∀ g, 0 < φ g) (hm : ∀ g h, φ (g * h) = φ g * φ h) :
    ∀ u ∈ U, φ u = 1 := by
  obtain ⟨m, hmU, hmax⟩ := hU.exists_isMaxOn ⟨1, U.one_mem⟩ hc.continuousOn
  have hle : ∀ u ∈ U, φ u ≤ 1 := fun u hu => by
    have h : φ (u * m) ≤ φ m := hmax (U.mul_mem hu hmU)
    rw [hm] at h
    have := hp m
    nlinarith
  intro u hu
  have h1 : φ 1 = 1 := by
    have h := hm 1 1
    rw [mul_one] at h
    have := hp 1
    nlinarith
  have h2 := hm u u⁻¹
  rw [mul_inv_cancel, h1] at h2
  have h3 := hle u hu
  have h4 := hle _ (U.inv_mem hu)
  have h5 := hp u
  nlinarith

open NumberField Matrix GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.CuspRep in
theorem UpperTheory.V.Lit.Dr.normFin :
    NormFin := by
  intro E _ _ a U hU
  let φ : GL (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) → ℝ :=
    fun g => finiteModule (ofFinite (K := E) (GeneralLinearGroup.det g))
  have hc : Continuous φ :=
    continuous_finiteModule.comp (continuous_ofFinite.comp GeneralLinearGroup.continuous_det)
  have hp : ∀ g, 0 < φ g := fun g => finiteModule_pos _
  have hm : ∀ g h, φ (g * h) = φ g * φ h := fun g h => by
    simp only [φ, map_mul, finiteModule_mul]
  have h1 := one_of_compact U hU φ hc hp hm
  have hγ : ∀ γ : GL (Fin a) E, φ (GeneralLinearGroup.map (algebraMap E _) γ) =
      |((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)|⁻¹ := fun γ => by
    have e : φ (GeneralLinearGroup.map (algebraMap E _) γ) =
        finiteModule (IdeleGroup.diagonal E (GeneralLinearGroup.det γ)) := by
      have hd : ((GeneralLinearGroup.det (GeneralLinearGroup.map
          (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) γ)) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) =
          algebraMap E _ γ.val.det := by
        rw [RingHom.map_det]; rfl
      have h2 : ((ofFinite (K := E) (GeneralLinearGroup.det (GeneralLinearGroup.map
          (algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) γ))).val).2 = algebraMap E _ γ.val.det :=
        (congrArg Units.val (toFinite_ofFinite _)).trans hd
      simp only [φ, finiteModule, h2]
      rfl
    rw [e, finiteModule_diagonal, FinitePlace.prod_eq_inv_abs_norm (GeneralLinearGroup.det γ).ne_zero]
    simp
  refine ⟨Quotient.lift φ fun g h hgh => ?_, fun s => ?_, fun γ s => ?_⟩
  · have h2 := h1 _ (QuotientGroup.leftRel_apply.1 hgh)
    have h3 := hm g (g⁻¹ * h)
    rw [mul_inv_cancel_left, h2, mul_one] at h3
    exact h3.symm
  · induction s using QuotientGroup.induction_on with
    | H g => exact hp g
  · induction s using QuotientGroup.induction_on with
    | H g => exact (hm _ g).trans (by rw [hγ]; rfl)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.NormInf
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private def detProd (p : HV E a) : ℝ := ∏ w : InfinitePlace E, ((Matrix.of p.1).det w).re

private theorem detProd_sand (g : GL (Fin a) (Cinf E)) (p : HV E a) :
    detProd (sand g p) = (∏ w : InfinitePlace E, ‖g.val.det w‖ ^ 2) * detProd p := by
  unfold detProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [sand_val, det_mul, det_mul, star_eq_conjTranspose, det_conjTranspose, mul_right_comm]
  have h : (g.val.det * star g.val.det * (Matrix.of p.1).det) w =
      ((‖g.val.det w‖ ^ 2 : ℝ) : ℂ) * (Matrix.of p.1).det w := by
    rw [Pi.mul_apply, Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.re_ofReal_mul]

private theorem contDiff_detProd : ContDiff ℝ ∞ (detProd (E := E) (a := a)) := by
  unfold detProd
  refine contDiff_prod fun w _ => Complex.reCLM.contDiff.comp (f := fun p : HV E a => (Matrix.of p.1).det w) ?_
  simp only [det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  have h : ContDiff ℝ ∞ (fun p : HV E a => p.1) := (HV E a).subtypeL.contDiff
  exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 h _) _) _

private theorem detProd_smul (t : ℝ) (p : HV E a) :
    detProd (t • p) = t ^ (a * Fintype.card (InfinitePlace E)) * detProd p := by
  unfold detProd
  have h : ∀ w : InfinitePlace E, ((Matrix.of (t • p).1).det w).re = t ^ a * ((Matrix.of p.1).det w).re := by
    intro w
    have h1 : Matrix.of (t • p).1 = (algebraMap ℝ (Cinf E) t) • Matrix.of p.1 := by
      rw [algebraMap_smul]; rfl
    rw [h1, det_smul, Fintype.card_fin, ← map_pow, ← Algebra.smul_def, Pi.smul_apply, Complex.smul_re, smul_eq_mul]
  simp only [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, pow_mul]

theorem normInf : NormInf := by
  intro E _ _ _ a
  refine ⟨detProd, contDiff_detProd, ?_, detProd_smul, ?_⟩
  · rintro p ⟨g, rfl⟩
    rw [detProd_sand]
    have h1 : detProd (hOne E a) = 1 := by
      unfold detProd
      rw [hOne_val, det_one]
      simp
    rw [h1, mul_one]
    refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) 2
    have hu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact (hu.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)).ne_zero
  · intro γ p
    rw [detProd_sand]
    congr 1
    have hd : (GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val.det = pInf E (algebraMap E (Ad E) γ.val.det) := by
      rw [RingHom.map_det, RingHom.map_det]
      rfl
    rw [hd, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq, IsTotallyComplex.mult_eq]

end UpperTheory.V.Lit.Dr
end
end

