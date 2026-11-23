module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.OfFnProdSmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.DetTransposeApply
section
open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem eI_inj (k r : ℕ) : Function.Injective (eI k r) := by
  unfold eI
  intro a b h
  have h1 := congrArg Fin.val h
  simp only at h1
  exact Fin.ext h1

theorem esI_inj (k r : ℕ) : Function.Injective (esI k r) := by
  unfold esI
  intro a b h
  have h1 := congrArg Fin.val h
  simp only at h1
  have ha := a.isLt
  have hb := b.isLt
  exact Fin.ext (by omega)

theorem keyS_inj (k r : ℕ) : Function.Injective (keyS k r) := by
  unfold keyS
  intro p q h
  simp only at h
  have hp := p.isLt
  have hq := q.isLt
  split_ifs at h <;> exact Fin.ext (by omega)

theorem strictMono_val_iff {m N : ℕ} (C : Fin m → Fin N) :
    StrictMono (fun l => (C l).val) ↔ StrictMono C :=
  ⟨fun h _ _ hab => h hab, fun h _ _ hab => h hab⟩

theorem not_inj {α β : Type*} {c : α → β} (hc : ¬ Function.Injective c) :
    ∃ p q, p ≠ q ∧ c p = c q := by
  simp only [Function.Injective, not_forall] at hc
  obtain ⟨p, q, h, hne⟩ := hc
  exact ⟨p, q, hne, h⟩

theorem det_transpose_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    M.det = ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp [Units.smul_def, zsmul_eq_mul, Matrix.transpose_apply]

theorem algebra_aa : AlgAA := by
  intro A _ _ k r m hm E P Q xi u hE hQP hP
  classical
  have hrow : ∀ D : Fin m → Fin (2 * r + k + 1),
      qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) (xR k r m hm) D u =
        ∑ d : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) • qminor E (xR k r m hm) d u := by
    intro D
    rw [q_expansion A _ m E P Q _ D u hQP]
    simp only [mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [show (∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (xR k r m hm j)) • (∏ j, Q (D j) (d j)) •
        qminor E c d u) = ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) •
        (∏ j, P (c j) (xR k r m hm j)) • qminor E c d u from
      Finset.sum_congr rfl (fun c _ => smul_comm _ _ _)]
    rw [← Finset.smul_sum]
    congr 1
    exact collapse hm (eI k r) (eI_inj k r) P hP (fun c => qminor E c d u)
      (fun c hc => by
        obtain ⟨p, q, hpq, h⟩ := not_inj hc
        exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hpq h)
  simp only [hrow]
  have h1 : ∀ D : Fin m → Fin (2 * r + k + 1),
      (if StrictMono D then (Matrix.of fun a l : Fin m => xi a (D l)).det •
        ∑ d : Fin m → Fin (2 * r + k + 1), (∏ j, Q (D j) (d j)) • qminor E (xR k r m hm) d u else 0) =
      ∑ d : Fin m → Fin (2 * r + k + 1), (if StrictMono D then
        (Matrix.of fun a l : Fin m => xi a (D l)).det * ∏ j, Q (D j) (d j) else 0) •
          qminor E (xR k r m hm) d u := by
    intro D
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [grouping (fun i => i.val) Fin.val_injective (fun d => qminor E (xR k r m hm) d u)
    (fun d τ => quantumMinorColSkew_holds A _ m E hE (xR k r m hm) d τ u)
    (fun d hd => by
      obtain ⟨p, q, hpq, h⟩ := not_inj hd
      exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE (xR k r m hm) d u p q hpq h)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  simp only [strictMono_val_iff]
  split_ifs with hC
  · congr 1
    have hM : (Matrix.of fun a l : Fin m => ∑ d, Q d (C l) * xi a d) =
        (Matrix.of fun a d => xi a d) * (Matrix.of fun d l => Q d (C l)) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, cauchyBinet (fun i => i.val) Fin.val_injective]
    simp only [strictMono_val_iff, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun D _ => ?_)
    split_ifs with hD
    · simp only [Matrix.of_apply]
      rw [det_transpose_apply (Matrix.of fun i l => Q (D i) (C l)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl

theorem algebra_aa_vector : AlgAAv := by
  intro A _ _ k r m hm E P Q eta v hE hQP hQ
  classical
  have hcol : ∀ B : Fin m → Fin (2 * r + k + 1),
      qminor (fun i j => ∑ c, ∑ d, (P c i * Q j d) • E c d) B (sR k r m hm) v =
        ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (B j)) • qminor E c (sR k r m hm) v := by
    intro B
    rw [q_expansion A _ m E P Q B _ v hQP]
    simp only [mul_smul]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← Finset.smul_sum]
    congr 1
    exact collapse hm (esI k r) (esI_inj k r) (fun i j => Q j i) hQ (fun d => qminor E c d v)
      (fun d hd => by
        obtain ⟨p, q, hpq, h⟩ := not_inj hd
        exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d v p q hpq h)
  simp only [hcol]
  have h1 : ∀ B : Fin m → Fin (2 * r + k + 1),
      (if StrictMono (fun l => keyS k r (B l)) then (Matrix.of fun a l : Fin m => eta a (B l)).det •
        ∑ c : Fin m → Fin (2 * r + k + 1), (∏ j, P (c j) (B j)) • qminor E c (sR k r m hm) v else 0) =
      ∑ c : Fin m → Fin (2 * r + k + 1), (if StrictMono (fun l => keyS k r (B l)) then
        (Matrix.of fun a l : Fin m => eta a (B l)).det * ∏ j, P (c j) (B j) else 0) •
          qminor E c (sR k r m hm) v := by
    intro B
    split_ifs
    · rw [Finset.smul_sum]; simp only [smul_smul]
    · simp
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [grouping (keyS k r) (keyS_inj k r) (fun c => qminor E c (sR k r m hm) v)
    (fun c τ => quantumMinorRowSkew_holds A _ m E c (sR k r m hm) τ v)
    (fun c hc => by
      obtain ⟨p, q, hpq, h⟩ := not_inj hc
      exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c (sR k r m hm) v p q hpq h)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  split_ifs with hC
  · congr 1
    have hM : (Matrix.of fun a l : Fin m => ∑ d, P (C l) d * eta a d) =
        (Matrix.of fun a d => eta a d) * (Matrix.of fun d l => P (C l) d) := by
      ext a l; simp [Matrix.mul_apply, mul_comm]
    rw [hM, cauchyBinet (keyS k r) (keyS_inj k r)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    split_ifs with hB
    · simp only [Matrix.of_apply]
      rw [det_transpose_apply (Matrix.of fun i l => P (C l) (B i)), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      simp only [Matrix.of_apply, Function.comp_apply]
      ring
    · simp
  · rfl

end AAInvW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.SmoothLinear
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rd_extension_h : RdExtH := by
  intro n H E _ _ f F U g X hH hU hg hgH hF hfF hX
  unfold RdV
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (ana_mul hgH (ana_expt hH hX t))
  rw [hev.deriv_eq]
  exact hcomp.deriv

theorem smooth_linear' : SmoothLin := by
  unfold SmoothLin
  intro n H E _ _ f f' c hf hf'
  unfold SmoothOnH at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩, ?_, ?_⟩
  · exact (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)
  · intro g hg hgH
    simp only [hfF g hg.1 hgH, hfF' g hg.2 hgH]

theorem smooth_local : SmoothLocal := by
  unfold SmoothLocal
  intro n H E _ _ f f' hff hf
  unfold SmoothOnH at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgH => (hff g hgH).symm.trans (hfF g hg hgH)⟩

theorem smooth_right' : SmoothRight := by
  unfold SmoothRight
  intro n H E _ _ f s hH hs hf
  unfold SmoothOnH at *
  have hL : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * s) := by
    have h := (LinearMap.mulRight ℝ s).toContinuousLinearMap.contDiff (n := ∞)
    convert h using 1
    funext x
    first
    | rfl
    | simp
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀ * s) (ana_mul hg₀ hs)
  refine ⟨(fun x => x * s) ⁻¹' U, fun x => F (x * s), hU.preimage hL.continuous, hgU, ?_, ?_⟩
  · exact hF.comp hL.contDiffOn (fun x hx => hx)
  · intro g hg hgH
    exact hfF (g * s) hg (ana_mul hgH hs)

section Rd

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma ana_rdSmooth (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hX : inLH H X) : SmoothOnH H (RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    have h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U :=
      (mulRightRealCLM X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro k hk hkH
    exact rd_extension_h n H E f F U k X hH hU hk hkH hF hfF hX

lemma ana_rdLin (hH : HInvol H) {f f' : Matrix (Fin n) (Fin n) ℂ → E} (c : ℂ)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnH H f) (hf' : SmoothOnH H f') (hX : inLH H X)
    (hg : inUH H g) : RdV X (fun x => f x + c • f' x) g = RdV X f g + c • RdV X f' g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g hg
  have hd1 : DifferentiableAt ℝ F g := by
    first
    | exact (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
    | exact (hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)
    | exact (hF.differentiableOn le_top).differentiableAt (hU.mem_nhds hgU)
  have hd2 : DifferentiableAt ℝ F' g := by
    first
    | exact (hF'.differentiableOn (by simp)).differentiableAt (hU'.mem_nhds hgU')
    | exact (hF'.contDiffAt (hU'.mem_nhds hgU')).differentiableAt (by simp)
    | exact (hF'.differentiableOn le_top).differentiableAt (hU'.mem_nhds hgU')
  have e0 := rd_extension_h n H E (fun x => f x + c • f' x) (fun x => F x + c • F' x) (U ∩ U') g X hH
    (hU.inter hU') ⟨hgU, hgU'⟩ hg
    ((hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c))
    (fun h hh hhH => by simp only [hfF h hh.1 hhH, hfF' h hh.2 hhH]) hX
  rw [e0, rd_extension_h n H E f F U g X hH hU hgU hg hF hfF hX,
    rd_extension_h n H E f' F' U' g X hH hU' hgU' hg hF' hfF' hX]
  have hD : HasFDerivAt (fun x => F x + c • F' x) (fderiv ℝ F g + c • fderiv ℝ F' g) g :=
    hd1.hasFDerivAt.add (hd2.hasFDerivAt.const_smul c)
  rw [hD.fderiv]
  first
  | rfl
  | simp

lemma ana_rdAdd (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {A B g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hA : inLH H A) (hB : inLH H B) (hg : inUH H g) :
    RdV (A + B) f g = RdV A f g + RdV B f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rd_extension_h n H E f F U g (A + B) hH hU hgU hg hF hfF (ana_add hA hB), rd_extension_h n H E f F U g (A) hH hU hgU hg hF hfF (hA), rd_extension_h n H E f F U g (B) hH hU hgU hg hF hfF (hB), Matrix.mul_add, map_add (f := _)]

lemma ana_rdSub (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {A B g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hA : inLH H A) (hB : inLH H B) (hg : inUH H g) :
    RdV (A - B) f g = RdV A f g - RdV B f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rd_extension_h n H E f F U g (A - B) hH hU hgU hg hF hfF (ana_sub hA hB), rd_extension_h n H E f F U g (A) hH hU hgU hg hF hfF (hA), rd_extension_h n H E f F U g (B) hH hU hgU hg hF hfF (hB), Matrix.mul_sub, map_sub]

lemma ana_rdLocal (hH : HInvol H) {f f' : Matrix (Fin n) (Fin n) ℂ → E} {X g : Matrix (Fin n) (Fin n) ℂ}
    (hff : ∀ x, inUH H x → f x = f' x) (hX : inLH H X) (hg : inUH H g) : RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact hff _ (ana_mul hg (ana_expt hH hX t))

end Rd

theorem eab_h_local : EabHLocal := by
  unfold EabHLocal
  intro n H E _ _ f f' a b g hH hff hg
  unfold EabH
  rw [ana_rdLocal hH hff (ana_hpartMem hH _).1 hg, ana_rdLocal hH hff (ana_hpartMem hH _).2.1 hg]

theorem eab_h_smooth : EabHSmooth := by
  unfold EabHSmooth
  intro n H E _ _ f a b hH hf
  unfold EabH
  exact smooth_linear' n H E _ _ Complex.I (ana_rdSmooth hH hf (ana_hpartMem hH _).1)
    (ana_rdSmooth hH hf (ana_hpartMem hH _).2.1)

theorem eab_h_linear : EabHLin := by
  unfold EabHLin
  intro n H E _ _ f f' c a b g hH hf hf' hg
  unfold EabH
  rw [ana_rdLin hH c hf hf' (ana_hpartMem hH _).1 hg, ana_rdLin hH c hf hf' (ana_hpartMem hH _).2.1 hg]
  rw [smul_add, smul_add, smul_comm Complex.I c]
  abel

end AAInvW
end
end

