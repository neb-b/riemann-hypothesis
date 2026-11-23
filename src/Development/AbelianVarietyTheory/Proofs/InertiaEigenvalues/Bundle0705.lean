module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPetersson
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthOfAvTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0275
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallySemistableReducibleUnramifiedSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneConjLowerUnipotentSchurBlocksSmall
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt Filter
open scoped ContDiff Topology

namespace GlobalTheory.SchurNear

variable {E : Type} [Field E] [NumberField E] {α : Type}

theorem continuous_pLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (pLoc E w) :=
  RestrictedProduct.continuous_eval w

theorem exists_inv (x : Af E) (h0 : ∀ w, pLoc E w x ≠ 0)
    (h1 : ∀ w : HeightOneSpectrum (𝓞 E), (pLoc E w x)⁻¹ ∈ w.adicCompletionIntegers E) :
    ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, x * y = 1 := by
  refine ⟨⟨fun w => (pLoc E w x)⁻¹, Eventually.of_forall h1⟩, h1, ?_⟩
  refine Subtype.ext (funext fun w => ?_)
  exact mul_inv_cancel₀ (h0 w)

theorem eventually_inv (S : Finset (HeightOneSpectrum (𝓞 E))) {l : Filter α} {f : α → Af E}
    (hf : Tendsto f l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (f a) = 1) :
    ∀ᶠ a in l, ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, f a * y = 1 := by
  have h : ∀ w ∈ S, ∀ᶠ a in l, pLoc E w (f a) ≠ 0 ∧ (pLoc E w (f a))⁻¹ ∈ w.adicCompletionIntegers E := by
    intro w _
    have h1 : Tendsto (fun a => pLoc E w (f a)) l (𝓝 1) := by
      have := ((continuous_pLoc w).tendsto 1).comp hf
      rwa [map_one] at this
    have h2 : Tendsto (fun a => (pLoc E w (f a))⁻¹) l (𝓝 1) := by
      have := h1.inv₀ one_ne_zero
      rwa [inv_one] at this
    refine (h1.eventually_ne one_ne_zero).and ?_
    exact h2.eventually ((Valued.isOpen_valuationSubring _).mem_nhds (one_mem (w.adicCompletionIntegers E)))
  filter_upwards [(eventually_all_finset S).2 h, hS] with a ha hb
  refine exists_inv _ (fun w => ?_) (fun w => ?_)
  · by_cases hw : w ∈ S
    · exact (ha w hw).1
    · rw [hb w hw]; exact one_ne_zero
  · by_cases hw : w ∈ S
    · exact (ha w hw).2
    · rw [hb w hw, inv_one]; exact one_mem _

theorem tendsto_inverse (S : Finset (HeightOneSpectrum (𝓞 E))) {l : Filter α} {f : α → Af E}
    (hf : Tendsto f l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (f a) = 1) :
    Tendsto (fun a => Ring.inverse (f a)) l (𝓝 1) := by
  intro W hW
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles E
  have hN : ∀ᶠ c in 𝓝 (1 : Af E), ∀ y ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)),
      1 + (1 - c) * y ∈ W := by
    refine hO.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : Af E × Af E => 1 + (1 - z.1) * z.2 := by fun_prop
    have h := hc.tendsto ((1 : Af E), y)
    simp only [sub_self, zero_mul, add_zero] at h
    exact h hW
  change ∀ᶠ a in l, Ring.inverse (f a) ∈ W
  filter_upwards [hf.eventually hN, eventually_inv S hf hS] with a ha ⟨y, hy, hxy⟩
  have hu : IsUnit (f a) := IsUnit.of_mul_eq_one y hxy
  have : Ring.inverse (f a) = 1 + (1 - f a) * y := by
    have h1 := Ring.inverse_mul_cancel _ hu
    linear_combination (1 - Ring.inverse (f a)) * hxy + y * h1
  rw [this]; exact ha y hy

theorem matrix_near (S : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} {l : Filter α}
    {g : α → Matrix (Fin n) (Fin n) (Af E)}
    (hg : Tendsto g l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, (g a).map (pLoc E w) = 1) :
    (∀ᶠ a in l, IsUnit (g a).det) ∧ Tendsto (fun a => (g a)⁻¹) l (𝓝 1) ∧
      Tendsto (fun a => mkGL (g a)) l (𝓝 1) := by
  have hd : Tendsto (fun a => (g a).det) l (𝓝 1) := by
    have := ((continuous_id.matrix_det (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg
    simpa [Function.comp_def] using this
  have hdS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (g a).det = 1 := by
    filter_upwards [hS] with a ha w hw
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ha w hw, Matrix.det_one]
  have hu : ∀ᶠ a in l, IsUnit (g a).det := by
    filter_upwards [eventually_inv S hd hdS] with a ⟨y, _, hy⟩
    exact IsUnit.of_mul_eq_one y hy
  have hadj : Tendsto (fun a => (g a).adjugate) l (𝓝 1) := by
    have := ((continuous_id.matrix_adjugate (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg
    simpa [Function.comp_def] using this
  have hi : Tendsto (fun a => (g a)⁻¹) l (𝓝 1) := by
    have := (tendsto_inverse S hd hdS).smul hadj
    simpa only [one_smul, Matrix.inv_def] using this
  refine ⟨hu, hi, ?_⟩
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  have h2 := (MulOpposite.continuous_op.tendsto _).comp hi
  have h3 := hg.prodMk_nhds h2
  refine Tendsto.congr' ?_ h3
  filter_upwards [hu] with a ha
  simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, coe_mkGL ha]

section Alg
variable {R T : Type} [CommRing R] [CommRing T] {m r : ℕ}

theorem blk_one : blk (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = Matrix.fromBlocks 1 0 0 1 := by
  rw [blk, Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]

theorem Aof_one : Aof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Aof, blk_one, Matrix.toBlocks_fromBlocks₁₁]
theorem Bof_one : Bof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Bof, blk_one, Matrix.toBlocks_fromBlocks₁₂]
theorem Cof_one : Cof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Cof, blk_one, Matrix.toBlocks_fromBlocks₂₁]
theorem Dof_one : Dof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Dof, blk_one, Matrix.toBlocks_fromBlocks₂₂]

theorem conj_one (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : conjLowUni Y 1 = 1 := by
  rw [conjLowUni, mul_one, lowUni, lowUni, unblk, unblk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem lowUni_map (p : R →+* T) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) :
    (lowUni Y).map p = lowUni (Y.map p) := by
  rw [lowUni, lowUni, unblk, unblk, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

theorem conj_map (p : R →+* T) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R)
    (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hk : k.map p = 1) :
    (conjLowUni Y k).map p = 1 := by
  rw [← conj_one (Y.map p), conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, hk,
    Matrix.map_neg _ (map_neg p)]

theorem Dof_map (p : R →+* T) (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map p = 1) :
    (Dof M).map p = 1 := by
  rw [← Dof_one (m := m), ← h]; rfl

theorem Scof_map (p : R →+* T) (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map p = 1) :
    (Scof M).map p = 1 := by
  have hA : (Aof M).map p = 1 := by rw [← Aof_one (r := r), ← h]; rfl
  have hB : (Bof M).map p = 0 := by rw [← Bof_one (m := m) (r := r), ← h]; rfl
  rw [Scof, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, hA, hB]
  simp

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_lowUni : Continuous (lowUni : Matrix (Fin (r + 1)) (Fin (m + 1)) R → _) :=
  (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_id continuous_const).matrix_submatrix _ _

theorem continuous_conj {Z : Type} [TopologicalSpace Z] {f : Z → Matrix (Fin (r + 1)) (Fin (m + 1)) R}
    {g : Z → Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun z => conjLowUni (f z) (g z)) := by
  have h1 : Continuous fun z => lowUni (f z) := continuous_lowUni.comp hf
  have h2 : Continuous fun z => lowUni (-f z) := continuous_lowUni.comp hf.neg
  exact (h1.matrix_mul hg).matrix_mul h2

theorem tendsto_mul {a b c : ℕ} {l : Filter α} {f : α → Matrix (Fin a) (Fin b) R} {g : α → Matrix (Fin b) (Fin c) R}
    {x : Matrix (Fin a) (Fin b) R} {y : Matrix (Fin b) (Fin c) R} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun t => f t * g t) l (𝓝 (x * y)) := by
  have hc : Continuous fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1 * z.2 :=
    Continuous.matrix_mul (A := fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1)
      (B := fun z => z.2) continuous_fst continuous_snd
  have h := (hc.tendsto (x, y)).comp (hf.prodMk_nhds hg)
  simpa only [Function.comp_def] using h

end Alg

theorem blocks_near (S : Finset (HeightOneSpectrum (𝓞 E))) {m r : ℕ} {l : Filter α}
    {g : α → Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)}
    (hg : Tendsto g l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, (g a).map (pLoc E w) = 1) :
    (∀ᶠ a in l, IsUnit (Dof (g a)).det) ∧ Tendsto (fun a => mkGL (Dof (g a))) l (𝓝 1) ∧
      Tendsto (fun a => mkGL (Scof (g a))) l (𝓝 1) ∧ Tendsto (fun a => Yof (g a)) l (𝓝 0) ∧
      Tendsto (fun a => Xof (g a)) l (𝓝 0) := by
  have hA : Tendsto (fun a => Aof (g a)) l (𝓝 1) := by
    rw [← Aof_one (r := r)]
    exact (Continuous.tendsto (f := Aof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hB : Tendsto (fun a => Bof (g a)) l (𝓝 0) := by
    rw [← Bof_one]
    exact (Continuous.tendsto (f := Bof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hC : Tendsto (fun a => Cof (g a)) l (𝓝 0) := by
    rw [← Cof_one]
    exact (Continuous.tendsto (f := Cof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hD : Tendsto (fun a => Dof (g a)) l (𝓝 1) := by
    rw [← Dof_one (m := m)]
    exact (Continuous.tendsto (f := Dof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  obtain ⟨hu, hi, hm⟩ := matrix_near S hD (hS.mono fun a ha w hw => Dof_map _ _ (ha w hw))
  have hSc : Tendsto (fun a => Scof (g a)) l (𝓝 1) := by
    have := hA.sub (tendsto_mul (tendsto_mul hB hi) hC)
    simpa only [Scof, Matrix.mul_zero, sub_zero] using this
  refine ⟨hu, hm, (matrix_near S hSc (hS.mono fun a ha w hw => Scof_map _ _ (ha w hw))).2.2, ?_, ?_⟩
  · simpa only [Yof, Matrix.mul_zero] using tendsto_mul hi hC
  · simpa only [Xof, Matrix.zero_mul] using tendsto_mul hB hi

theorem conj_near (S : Finset (HeightOneSpectrum (𝓞 E))) {m r : ℕ} {Z : Type} [TopologicalSpace Z]
    (π : Z → Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E)) (hπ : Continuous π) (z₀ : Z) :
    let l : Filter (GL (Fin (m + r + 1 + 1)) (Af E) × Z) :=
      𝓝 (1, z₀) ⊓ 𝓟 {z | ∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) z.1 = 1}
    Tendsto (fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => conjLowUni (π z.2) z.1.val) l (𝓝 1) ∧
      ∀ᶠ z in l, ∀ w ∉ S, (conjLowUni (π z.2) z.1.val).map (pLoc E w) = 1 := by
  intro l
  constructor
  · have hc : Continuous fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => conjLowUni (π z.2) z.1.val :=
      continuous_conj (f := fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => π z.2) (g := fun z => z.1.val)
        (hπ.comp continuous_snd) (Units.continuous_val.comp continuous_fst)
    have := hc.tendsto (1, z₀)
    simp only [Units.val_one, conj_one] at this
    exact this.mono_left inf_le_left
  · refine eventually_inf_principal.2 (Eventually.of_forall fun z hz w hw => conj_map _ _ _ ?_)
    exact congrArg Units.val (hz w hw)

theorem blocks_small : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
  intro E _ _ m r S Uβ Ub hβ hb Krow Kcol hrow hcol
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles E
  have hOo : (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) ∈ 𝓝 (0 : Af E) :=
    GroundTheory.Global.isOpen_integralFiniteAdeles.mem_nhds (zero_mem _)
  set KY : Set (Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E)) :=
    {Y | ∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E} with hKY
  have hK : IsCompact KY := by
    have := isCompact_pi_infinite (X := fun _ : Fin (r + 1) => Fin (m + 1) → Af E)
      (fun _ => isCompact_pi_infinite (fun _ : Fin (m + 1) => hO))
    exact this
  have h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ Y ∈ KY,
      (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) →
      IsUnit (Dof (conjLowUni Y k.val)).det ∧ mkGL (Dof (conjLowUni Y k.val)) ∈ Ub ∧
        mkGL (Scof (conjLowUni Y k.val)) ∈ Uβ ∧
        ∀ i j, Yof (conjLowUni Y k.val) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    refine hK.eventually_forall_of_forall_eventually fun Y _ => ?_
    obtain ⟨a, b⟩ := conj_near S id continuous_id Y
    obtain ⟨c1, c2, c3, c4, -⟩ := blocks_near S a b
    refine eventually_inf_principal.1 (c1.and ((c2.eventually (hb.mem_nhds Ub.one_mem)).and
      ((c3.eventually (hβ.mem_nhds Uβ.one_mem)).and ?_)))
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    exact (((continuous_id.matrix_elem i j).tendsto 0).comp c4).eventually hOo
  have h2 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ z ∈ KY ×ˢ (Krow ×ˢ Kcol),
      (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) →
      (∑ j, ∑ l, z.2.1 j * Xof (conjLowUni z.1 k.val) j l * z.2.2 l) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    refine (hK.prod (hrow.prod hcol)).eventually_forall_of_forall_eventually fun z₀ _ => ?_
    obtain ⟨a, b⟩ := conj_near S Prod.fst continuous_fst z₀
    obtain ⟨-, -, -, -, c⟩ := blocks_near S a b
    have hc : Continuous fun t : Matrix (Fin (m + 1)) (Fin (r + 1)) (Af E) × (Fin (m + 1) → Af E) × (Fin (r + 1) → Af E) =>
        ∑ j, ∑ l, t.2.1 j * t.1 j l * t.2.2 l := by fun_prop
    have h3 := (hc.tendsto (0, z₀.2)).comp (c.prodMk_nhds
      (((continuous_snd.comp continuous_snd).tendsto (1, z₀)).mono_left inf_le_left))
    simp only [Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero] at h3
    exact eventually_inf_principal.1 (h3.eventually hOo)
  refine ⟨_, h1.and h2, fun k hk hS Y hY => ?_⟩
  obtain ⟨a, b, c, d⟩ := hk.1 Y hY hS
  exact ⟨a, b, c, d, fun ρ hρ γ hγ => hk.2 (Y, ρ, γ) ⟨hY, hρ, hγ⟩ hS⟩

end GlobalTheory.SchurNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGLStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_whittakerBump_adelicGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ b : GA E (a + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (a + 1)), IsCompact C ∧ ∀ p, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (a + 1)) (Af E)), IsOpen (U : Set (GL (Fin (a + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (a + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (a + 1)) := by
  first | (exact @GlobalTheory.WhitBump.exists_bump_glob) | (exact GlobalTheory.WhitBump.exists_bump_glob) | (intros; apply GlobalTheory.WhitBump.exists_bump_glob  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstColumnInvFiniteMemCompactOnSupport
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.NmUnfCol

theorem continuous_pFin (E : Type) [Field E] [NumberField E] : Continuous (pFin E) := by
  unfold pFin; exact continuous_snd

theorem col_inv_mul {E : Type} [Field E] [NumberField E] {a : ℕ}
    (u p : GA E (a + 1)) (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1))) (l : Fin (a + 1)) :
    ((p⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 =
      (((u⁻¹ * p)⁻¹ : GA E (a + 1)) : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) l 0 := by
  have e : ((u⁻¹ * p)⁻¹ : GA E (a + 1)) = p⁻¹ * u := by group
  rw [e, Units.val_mul, Matrix.mul_apply]
  have hcol : ∀ j : Fin (a + 1), (u : Matrix (Fin (a + 1)) (Fin (a + 1)) (Ad E)) j 0 = if j = 0 then 1 else 0 := by
    intro j
    by_cases hj : j = 0
    · subst hj; simp [hu.2 0]
    · rw [if_neg hj]; exact hu.1 j 0 (Fin.pos_iff_ne_zero.2 hj)
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem finite_first_col_inv_compact : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := by
  intro E _ _ r b₁ ⟨C, hC, hsupp⟩
  let f : GA E (r + 1) → (Fin (r + 1) → Af E) :=
    fun c l => pFin E (((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)
  have hf : Continuous f := by
    refine continuous_pi fun l => (continuous_pFin E).comp ?_
    have h0 : Continuous (fun c : GA E (r + 1) => ((c⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E))) :=
      Units.continuous_coe_inv
    exact (continuous_apply 0).comp ((continuous_apply l).comp h0)
  refine ⟨f '' C, hC.image hf, fun p hp => ?_⟩
  obtain ⟨u, hu, huC⟩ := hsupp p hp
  refine ⟨u⁻¹ * p, huC, funext fun l => ?_⟩
  simp only [f]
  rw [col_inv_mul u p hu l]

end GlobalTheory.NmUnfCol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameOfFst
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWLagTerms

variable {D : D7}

def blk (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank ⊕ Fin W.rank) (Fin W.rank ⊕ Fin W.rank) D.host.E :=
  g.submatrix finSumFinEquiv finSumFinEquiv

def hAdj (W : HSp D) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (HSpace.gram W)⁻¹ * (M.map star)ᵀ * HSpace.gram W

def frameOf (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (hAdj W ((blk W g).toBlocks₂₂ - (blk W g).toBlocks₁₂), hAdj W ((blk W g).toBlocks₁₁ - (blk W g).toBlocks₂₁))

theorem frameOf_fst (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    (frameOf W g).1 = hAdj W ((blk W g).toBlocks₂₂ - (blk W g).toBlocks₁₂) := rfl

theorem frameOf_snd (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    (frameOf W g).2 = hAdj W ((blk W g).toBlocks₁₁ - (blk W g).toBlocks₂₁) := rfl

end GlobalTheory.SWLagTerms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLower
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.TypeOrthClassSum

theorem typeOrth_of_classSum : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ i : D.nd.Loc, ClassSum (M.loc i) → TypeOrth D i := by
  intro D M V i hC
  obtain ⟨hbd, β, T, c, hβ, hT, hc, hin⟩ := hC
  obtain ⟨B, hB, hBc⟩ := _root_.GlobalTheory.ClassPet.classSum_eq_pet D.host.E D.R.nV (M.loc i).wt β hβ
  obtain ⟨c', hc', hcc⟩ := hBc (M.loc i).J (M.loc i).χ T hbd (M.loc i).J_open hT
  have hreal : ∀ x, (M.loc i).real x ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ := fun x => by
    rw [← (M.loc i).real_range]; exact LinearMap.mem_range_self _ x
  set r : ℝ := c * c' with hr
  have hr0 : 0 < r := mul_pos hc hc'
  have hsmul : ∀ f f', (((r : ℂ) • B) f f') = (r : ℂ) * B f f' := fun f f' => by
    simp [LinearMap.smul_apply]

  have hcls : ∃ T' : Finset (GAf D.host.E D.R.nV), ∀ g : GAf D.host.E D.R.nV, ∃ (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV)
      (t : GAf D.host.E D.R.nV) (u : GAf D.host.E D.R.nV), t ∈ T' ∧ u ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV ∧
      g = (γ : GAf D.host.E D.R.nV) * t * u := by
    classical
    obtain ⟨F, hF⟩ := hbd
    refine ⟨(T ×ˢ F).image (fun p => p.1 * p.2), fun g => ?_⟩
    obtain ⟨t, ⟨htT, γ, κ, hκ, hg⟩, -⟩ := hT g
    obtain ⟨f, hfF, hu⟩ := hF κ hκ
    refine ⟨γ, t * f, f⁻¹ * κ, Finset.mem_image.2 ⟨(t, f), Finset.mem_product.2 ⟨htT, hfF⟩, rfl⟩, hu, ?_⟩
    rw [hg]; group
  have key := GlobalTheory.ThetaExh.typeOrth_of_avTied D M V i ((r : ℂ) • B) ?_ ?_ ?_
  · exact key
  · intro f hf f' hf'
    obtain ⟨h1, h2, h3⟩ := hB f hf f' hf'
    refine ⟨?_, fun hne => ?_, fun h => ?_⟩
    · rw [hsmul, hsmul, h1, map_mul, Complex.conj_ofReal]
    · rw [hsmul, Complex.re_ofReal_mul]; exact mul_pos hr0 (h2 hne)
    · rw [hsmul, hsmul, h3]
  · intro x y
    rw [hin, hsmul, hcc _ (hreal x) _ (hreal y), hr]
    push_cast; ring
  · intro N hN
    exact GlobalTheory.AlgFormsFin.finiteDimensional_forms D D.R.nV (M.loc i).wt hcls N hN

end GlobalTheory.TypeOrthClassSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCocycleBlockLengthLeOfQuadraticRelation
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.QuadN

theorem psiChi_group {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}
    (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (c : Fin D.R.t) (g : GE D.nd) :
    S.ψχ c (fun x' => rO D.nd i r (S.p x') g) = ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
    ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
  have a1 := h1 g (S.e.symm (0, fun _ => 1))
  have a2 := h2 _ hg (S.e.symm (0, fun _ => 1))
  simp only [hp] at a2
  have a3 := congrFun (congrArg Prod.snd (a2.symm.trans a1)) c
  simp only [LinearEquiv.apply_symm_apply, mul_one] at a3
  exact IsFractionRing.injective _ _ a3

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  intro D i r ρ π Xs S hr hS hπ v hv hq c
  have hl := D.nd.SQ_l i v hv
  have hchi : ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chiU D.nd i ((c : ℕ) + 1) γ = chiU D.nd i 1 γ :=
    fun γ hγ => (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v hl γ hγ).2 _ (by omega) c.2
  have hγ0 := D.nd.locNd_chebotarevPlace_mem i v
  have htor : ∀ f ∈ cocChi i r S Xs c, (D.nd.zeta i v - 1) • f (D.nd.gam0 i v) = 0 := by
    intro f hf
    have := Check.cocW_quad i r S Xs _ hq hf _ hγ0
    rw [Check.matKO_smul_one, psiChi_group hS, hchi _ hγ0] at this
    rw [sub_smul, one_smul, sub_eq_zero]
    exact this
  have hdet : ∀ f ∈ cocChi i r S Xs c, f (D.nd.gam0 i v) = 0 →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f σ = 0 := by
    intro f hf h0
    obtain ⟨hc, hz⟩ := (GlobalTheory.Cut.CocN.main D i r ρ π Xs S hr hS hπ).2 c hf
    have : DiscreteTopology (KOG (D.nd.O i) 1) := ⟨rfl⟩
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hc
    have hadd : ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
        f (a * b) = f a + f b := by
      intro a ha b _
      have e : chiRatO D.nd i ((c : ℕ) + 1) a = (1 : D.nd.O i) • 1 := by
        change (((chiU D.nd i ((c : ℕ) + 1) a * (chiU D.nd i 1 a)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
          (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) = _
        rw [hchi a ha, mul_inv_cancel, Units.val_one]
      rw [hz, Check.WKG_eq_matKO, e, Check.matKO_smul_one, one_smul]
    exact GlobalTheory.Cut.Quad.eq_zero_of_tameGen (D.nd.restN_tameGenerator_generates i v hv) f hlc hadd (GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant D i v hl f hlc hadd) h0
  refine le_trans ?_ (GlobalTheory.Cut.Quad.length_torsionBy_le (D.nd.zeta i v - 1))
  refine Module.length_le_of_injective
    (LinearMap.restrict (LinearMap.proj (⟨D.nd.gam0 i v, hγ0⟩ : Ine (F := D.host.E) (D.nd.plOm.1 v))) ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact htor f hf
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, f, hf, rfl⟩ h0
    refine Subtype.ext (funext fun σ => ?_)
    exact hdet f hf (congrArg Subtype.val h0) σ.1 σ.2

end GlobalTheory.Cut.QuadN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixForm
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem matThm_holds : MatThm :=
  _root_.GlobalTheory.PMon.matThm_of_steps _root_.GlobalTheory.PMon.FrameEquiv.frameEx _root_.GlobalTheory.PMon.twistStep _root_.GlobalTheory.PMon.senStep _root_.GlobalTheory.PMon.Red.redStep _root_.GlobalTheory.PMon.modStep_holds

end GlobalTheory.PMon
end

