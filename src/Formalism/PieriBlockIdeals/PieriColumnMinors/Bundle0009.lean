module

public import Formalism.PieriBlockIdeals.PieriColumnMinors.Bundle0008

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.LriEVPowCoe
section
open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lri_LevZ_le (p q w : ℕ) (lam2 : Fin q → ℕ) :
    LevZ p q w lam2 ≤ (weyl ℤ (p + q) (p + q) le_rfl (LD.blockWt p q w lam2)).map (intQ (p + q) (p + q)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨ω, rfl⟩
  refine ⟨applyWord ℤ (liftWord p ω) (hw ℤ le_rfl (LD.blockWt p q w lam2)), Submodule.subset_span ⟨liftWord p ω, rfl⟩, ?_⟩
  rw [lrc_intQ_apply, ← lclosedeq_applyWord_map, lclosedeq_hw_map]

theorem MW_le_MV (p q w : ℕ) (lam2 : Fin q → ℕ) (u : (rationalBlockModuleSetting p q w lam2).W) (hu : u ∈ MW p q w lam2) :
    (u : VQ p q w lam2) ∈ MV p q w lam2 :=
  lri_LevZ_le p q w lam2 hu

theorem lri_EV_pow_coe (p q w : ℕ) (lam2 : Fin q → ℕ) (a b : Fin p ⊕ Fin q) (k : ℕ) (x : VQ p q w lam2) :
    ((((EV p q w lam2 a b) ^ k) x : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      ((der (p + q) (p + q) (idx p q a) (idx p q b) : Module.End ℚ _) ^ k) (x : MvPolynomial _ ℚ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, EV_coe, ih, pow_succ', Module.End.mul_apply]
    rfl

theorem lri_hL (p q w : ℕ) (lam2 : Fin q → ℕ) (v : Fin q × Fin p) (k : ℕ) (x : VQ p q w lam2)
    (hx : x ∈ MV p q w lam2) :
    ((k.factorial : ℚ)⁻¹) • (((rationalBlockModuleSetting p q w lam2).f v) ^ k) x ∈ MV p q w lam2 := by
  rw [mem_MV] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  have hne : Fin.natAdd p v.1 ≠ Fin.castAdd q v.2 := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
    have := v.2.isLt
    omega
  have e : (((((k.factorial : ℚ)⁻¹) • (((rationalBlockModuleSetting p q w lam2).f v) ^ k) x : VQ p q w lam2)) :
      MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      rowDiv ℚ (Fin.natAdd p v.1) (Fin.castAdd q v.2) k (x : MvPolynomial _ ℚ) := by
    rw [der_pow _ _ hne, Submodule.coe_smul]
    congr 1
    exact lri_EV_pow_coe p q w lam2 (Sum.inr v.1) (Sum.inl v.2) k x
  rw [e, ← hyx, lrc_intQ_apply, lclosedeq_rowDiv_map]
  exact ⟨_, weylRowDivStable ℤ _ _ le_rfl _ _ _ k y hy, rfl⟩

theorem lri_coe_zsmul (p q w : ℕ) (lam2 : Fin q → ℕ) (m : ℤ) (u : (rationalBlockModuleSetting p q w lam2).W) :
    ((m • u : (rationalBlockModuleSetting p q w lam2).W) : VQ p q w lam2) = m • (u : VQ p q w lam2) := by
  simp

theorem deltaAll_le (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) :
    DeltaAll (rationalBlockModuleSetting p q w lam2) (DelLR l hl p q w lam2) ≤ locSpan l hl (MV p q w lam2) := by
  refine iSup_le fun n => Submodule.span_le.mpr ?_
  rintro x ⟨m, u, hu, rfl⟩
  obtain ⟨m₀, hm₀, hmu⟩ := (mem_locSpan l hl _ u).1 hu
  have h1 := MW_le_MV p q w lam2 _ hmu
  rw [lri_coe_zsmul] at h1
  have h2 := Fs_div_mem (rationalBlockModuleSetting p q w lam2) (MV p q w lam2) (lri_hL p q w lam2) m _ h1
  refine ⟨m₀, hm₀, ?_⟩
  have e : ((Symmetrization.mfact m : ℚ)⁻¹) • (rationalBlockModuleSetting p q w lam2).Fs m (m₀ • (u : VQ p q w lam2)) =
      m₀ • (((Symmetrization.mfact m : ℚ)⁻¹) • (rationalBlockModuleSetting p q w lam2).Fs m (u : VQ p q w lam2)) := by
    rw [map_zsmul, smul_comm]
  rw [← e]
  exact h2

theorem lri_intQ_zsmul (r : ℕ) (z : ℤ) (x : MvPolynomial (Fin r × Fin r) ℤ) :
    intQ r r (z • x) = (z : ℚ) • intQ r r x := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem lri_intQ_inj (r : ℕ) : Function.Injective (intQ r r) := by
  intro x y h
  rw [lrc_intQ_apply, lrc_intQ_apply] at h
  exact MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)) h

theorem mem_dual (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) (hx : x ∈ dualWeyl ℤ (p + q) (p + q) (LD.blockWt p q w lam2))
    (hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)) :
    (⟨intQ _ _ x, hx'⟩ : VQ p q w lam2) ∈
      (formB p q w lam2).dualSubmodule (DeltaAll (rationalBlockModuleSetting p q w lam2) (DelLR l hl p q w lam2)) := by
  have hanti := LD.ld_blockWt_anti p q w lam2 ha hb
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  obtain ⟨m, hm, hmy⟩ := (mem_locSpan l hl _ y).1 (deltaAll_le l hl p q w lam2 hy)
  rw [mem_MV] at hmy
  obtain ⟨y', hy', hy'e⟩ := hmy
  obtain ⟨z, hz⟩ := fock_int (p + q) _ hanti x hx y' hy'
  rw [mem_one_iff, zl_mem_iff hl]
  refine ⟨m, hm, z, ?_⟩
  have hc := (hw_norm_pos (LD.blockWt p q w lam2)).ne'
  have e1 : (m : ℚ) * formB p q w lam2 ⟨intQ _ _ x, hx'⟩ y = formB p q w lam2 ⟨intQ _ _ x, hx'⟩ (m • y) := by
    rw [map_zsmul, zsmul_eq_mul]
  rw [e1, formB_apply]
  have e2 : (((m • y : VQ p q w lam2)) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = intQ _ _ y' := by
    rw [hy'e]
  rw [e2]
  change fockQ (intQ (p + q) (p + q) x) (intQ (p + q) (p + q) y') / _ = _
  rw [hz, mul_div_assoc, div_self hc, mul_one]

theorem concl (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ)
    (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ)
    (hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)) (E : ℕ)
    (h : ((l : Zl l) ^ E) • (⟨intQ _ _ x, hx'⟩ : VQ p q w lam2) ∈
      DeltaAll (rationalBlockModuleSetting p q w lam2) (DelLR l hl p q w lam2)) :
    ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ (m * (l : ℤ) ^ E) • x ∈ weyl ℤ (p + q) (p + q) le_rfl (LD.blockWt p q w lam2) := by
  obtain ⟨m, hm, hmv⟩ := (mem_locSpan l hl _ _).1 (deltaAll_le l hl p q w lam2 h)
  rw [mem_MV] at hmv
  obtain ⟨y, hy, hye⟩ := hmv
  refine ⟨m, hm, ?_⟩
  have e : intQ _ _ ((m * (l : ℤ) ^ E) • x) = intQ _ _ y := by
    rw [hye, lri_intQ_zsmul]
    simp only [Submodule.coe_smul_of_tower, lrc_smul_def]
    rw [← Int.cast_smul_eq_zsmul ℚ m, smul_smul]
    congr 1
    push_cast
    rfl
  rw [lri_intQ_inj _ e]
  exact hy

theorem wt_of_hom (p q w : ℕ) (lam2 : Fin q → ℕ) (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ)
    (hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)) (μ : Fin (p + q) → ℕ)
    (hμ : IsWeightedHomogeneous (rowW (p + q) (p + q)) x μ) :
    (⟨intQ _ _ x, hx'⟩ : VQ p q w lam2) ∈ (rationalBlockModuleSetting p q w lam2).wt fun a => (μ (idx p q a) : ℤ) := by
  refine (real_weight p q w lam2 _ μ).1 ?_
  intro d hd
  apply hμ
  intro h0
  apply hd
  change AddMonoidAlgebra.coeff (intQ _ _ x) d = 0
  rw [lrc_intQ_apply, coeff_map, h0, map_zero]

theorem dominant_xi {p q : ℕ} (ξ : Fin (p + q) → ℤ) (hξ : Antitone ξ) (α : Fin p) (b : Fin q) :
    0 ≤ xiOf ξ (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1) := by
  show 0 ≤ ∑ a, ξ (idx p q a) * ((Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1 : Fin p ⊕ Fin q → ℤ) a)
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine sub_nonneg.mpr (hξ ?_)
  show Fin.castAdd q α ≤ Fin.natAdd p b
  rw [Fin.le_def]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  omega

end Formalism.CohomologicalDescent.LR
end
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.LrjTransposeLift
section
open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lrj_liftWord_cons (p : ℕ) {q : ℕ} (x : Fin q × Fin q × ℕ) (ω : List (Fin q × Fin q × ℕ)) :
    liftWord p (x :: ω) = (Fin.natAdd p x.1, Fin.natAdd p x.2.1, x.2.2) :: liftWord p ω := rfl

theorem lrj_transpose_lift (p : ℕ) {q : ℕ} (ω : List (Fin q × Fin q × ℕ)) :
    transposeWord (liftWord p (transposeWord ω)) = liftWord p ω := by
  simp [transposeWord, liftWord, List.map_reverse, List.map_map, Function.comp_def]

theorem levZ_sub (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) (hf : f ∈ LevZ p q w lam2) :
    ∃ y : (rationalBlockModuleSetting p q w lam2).W, ((y : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = f := by
  let M : Submodule ℚ (MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) :=
    (W0 p q w lam2).map (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype
  have hM : ∀ (b b' : Fin q) (k : ℕ), ∀ g ∈ M, rowDiv ℚ (Fin.natAdd p b) (Fin.natAdd p b') k g ∈ M := by
    intro b b' k
    refine closed_of_der _ _ M ?_ k
    rintro g ⟨x, hx, rfl⟩
    exact ⟨EV p q w lam2 (Sum.inr b) (Sum.inr b') x, w_zero_stable_right_block p q w lam2 b b' x hx, rfl⟩
  have hgen : ∀ ω : List (Fin q × Fin q × ℕ), applyWord ℚ (liftWord p ω) (hw ℚ le_rfl (LD.blockWt p q w lam2)) ∈ M := by
    intro ω
    induction ω with
    | nil => exact ⟨hwV p q w lam2 ha hb, hwV_mem p q w lam2 ha hb, rfl⟩
    | cons x ω ih =>
      rw [lrj_liftWord_cons, applyWord_cons]
      exact hM _ _ _ _ ih
  have hle : LevZ p q w lam2 ≤ M.restrictScalars ℤ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ω, rfl⟩
    exact hgen ω
  obtain ⟨x, hx, hxf⟩ := hle hf
  exact ⟨⟨x, hx⟩, hxf⟩

theorem resInj (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (z : VQ p q w lam2) (hz : z ∈ W0 p q w lam2)
    (h0 : res ℚ p q (z : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0) : z = 0 := by
  let Z : Submodule ℚ (VQ p q w lam2) :=
    W0 p q w lam2 ⊓ LinearMap.ker ((res ℚ p q).toLinearMap.comp
      (dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)).subtype)
  have hst : ∀ b b' : Fin q, ∀ u ∈ Z, EV p q w lam2 (Sum.inr b) (Sum.inr b') u ∈ Z := by
    rintro b b' u ⟨huW, huk⟩
    have huk' : res ℚ p q (u : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0 := huk
    refine ⟨w_zero_stable_right_block p q w lam2 b b' u huW, ?_⟩
    show res ℚ p q ((EV p q w lam2 (Sum.inr b) (Sum.inr b') u : VQ p q w lam2) :
      MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = 0
    rw [EV_coe]
    show res ℚ p q (der (p + q) (p + q) (Fin.natAdd p b) (Fin.natAdd p b') u) = 0
    rw [← rowDiv_one, res_rowDiv, huk']
    simp [rowDiv]
  by_contra hne
  have hZ : Z ≠ ⊥ := by
    intro hb0
    have : z ∈ Z := ⟨hz, h0⟩
    rw [hb0, Submodule.mem_bot] at this
    exact hne this
  have hh := real_irreducible p q w lam2 ha hb Z inf_le_left hst hZ (hwV p q w lam2 ha hb) rfl
  have : res ℚ p q (hw ℚ le_rfl (LD.blockWt p q w lam2)) = 0 := hh.2
  rw [res_hw p q w lam2 ha hb] at this
  exact hwNe ℚ q q le_rfl lam2 this

theorem wt_extract (p q w : ℕ) (lam2 : Fin q → ℕ) (u : VQ p q w lam2) (hu : u ≠ 0) (κ : Fin p ⊕ Fin q → ℤ)
    (hw' : u ∈ (rationalBlockModuleSetting p q w lam2).wt κ) :
    ∃ μN : Fin (p + q) → ℕ, IsWeightedHomogeneous (rowW (p + q) (p + q))
      (u : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) μN ∧ κ = fun a => (μN (idx p q a) : ℤ) := by
  have hu' : (u : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) ≠ 0 := fun h => hu (Subtype.ext h)
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hu'
  rw [MvPolynomial.mem_support_iff] at hd
  have hκ : κ = fun a => ((Finsupp.weight (rowW (p + q) (p + q)) d (idx p q a) : ℕ) : ℤ) := by
    funext a
    have h1 := congrArg (fun x : VQ p q w lam2 => AddMonoidAlgebra.coeff (x : MvPolynomial _ ℚ) d) (((mem_wt p q w lam2 u κ).1 hw') a)
    simp only [EV_coe, coeff_der_diag, Submodule.coe_smul, coeff_smul, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hd h1
    exact_mod_cast h2.symm
  refine ⟨Finsupp.weight (rowW (p + q) (p + q)) d, ?_, hκ⟩
  rw [hκ] at hw'
  exact (real_weight p q w lam2 u _).2 hw'

theorem liftWeyl (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (y : MvPolynomial (Fin q × Fin q) ℤ) (hy : y ∈ weyl ℤ q q le_rfl lam2) :
    ∃ d ∈ LevZ p q w lam2, res ℚ p q d = intQ q q y := by
  unfold weyl at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    refine ⟨applyWord ℚ (liftWord p ω) (hw ℚ le_rfl (LD.blockWt p q w lam2)), Submodule.subset_span ⟨ω, rfl⟩, ?_⟩
    rw [res_applyWord, res_hw p q w lam2 ha hb, lrc_intQ_apply, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, h1, e1⟩ := hx
    obtain ⟨d2, h2, e2⟩ := hy
    exact ⟨d1 + d2, Submodule.add_mem _ h1 h2, by rw [map_add (f := _), map_add (f := _), e1, e2]⟩
  | smul c x _ hx =>
    obtain ⟨d1, h1, e1⟩ := hx
    exact ⟨c • d1, Submodule.smul_mem _ c h1, by rw [map_zsmul, map_zsmul, e1]⟩

theorem lrj_hom_of_smul {σ M : Type*} [AddCommMonoid M] (wt : σ → M) (g' : MvPolynomial σ ℤ) (g : MvPolynomial σ ℚ)
    (m : ℤ) (μ : M) (hg : IsWeightedHomogeneous wt g μ) (h : (m : ℚ) • g = map (Int.castRingHom ℚ) g') :
    IsWeightedHomogeneous wt g' μ := by
  intro d hd
  apply hg
  intro h0
  apply hd
  have h1 := congrArg (AddMonoidAlgebra.coeff · d) h
  rw [coeff_smul, h0, smul_zero, coeff_map] at h1
  have h2 : ((AddMonoidAlgebra.coeff g' d : ℤ) : ℚ) = 0 := by simpa using h1.symm
  exact_mod_cast h2

theorem expL_real (hC : CoeffWord) (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2)
    (hb : ∀ b, lam2 b ≤ w) (ξ : Fin (p + q) → ℤ) (i' : ℤ) (eL : ℕ)
    (heL : ∀ μ2 : Fin q → ℕ, LD.depth2 ξ (LD.blockWt p q w lam2) (LD.blockWt p q w μ2) ≤ i' →
      LD.ExpLe l q lam2 μ2 eL) :
    ∀ κ, xiOf ξ (lamOf p q w lam2 - κ) ≤ i' →
      ∀ u ∈ NablaL (rationalBlockModuleSetting p q w lam2) (formB p q w lam2) (DelLR l hl p q w lam2),
      ((u : VQ p q w lam2)) ∈ (rationalBlockModuleSetting p q w lam2).wt κ → ((l : Zl l) ^ eL) • u ∈ DelLR l hl p q w lam2 := by
  intro κ hκ u hu hwt
  have hanti := LD.ld_blockWt_anti p q w lam2 ha hb
  by_cases hu0 : u = 0
  · rw [hu0, smul_zero]; exact Submodule.zero_mem _
  have hu0' : (u : VQ p q w lam2) ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨μN, hμN, rfl⟩ := wt_extract p q w lam2 _ hu0' κ hwt
  have huW : (u : VQ p q w lam2) ∈ W0 p q w lam2 := u.2
  have hfirst : ∀ α : Fin p, μN (Fin.castAdd q α) = w := by
    intro α
    have h1 := ((mem_orthogonal_frame_iff p q w lam2 _).1 huW).2 α α
    have h2 := ((mem_wt p q w lam2 _ _).1 hwt) (Sum.inl α)
    rw [if_pos rfl, h2] at h1
    have h3 := smul_left_injective ℚ hu0' h1
    exact_mod_cast h3
  let μ2 : Fin q → ℕ := fun b => μN (Fin.natAdd p b)
  have hblock : LD.blockWt p q w μ2 = μN := by
    funext a
    refine Fin.addCases (fun α => ?_) (fun b => ?_) a
    · rw [LD.blockWt, Fin.append_left, hfirst]
    · rw [LD.blockWt, Fin.append_right]
  have hd : LD.depth2 ξ (LD.blockWt p q w lam2) (LD.blockWt p q w μ2) ≤ i' := by
    rw [hblock]
    calc LD.depth2 ξ (LD.blockWt p q w lam2) μN = _ := (xiOf_depth2 ξ (LD.blockWt p q w lam2) μN).symm
      _ ≤ i' := hκ
  set f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ :=
    ((u : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) with hf
  have hfN : f ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2) := (u : VQ p q w lam2).2
  have hg := res_mem ℚ p q w lam2 f hfN
  have hω : ∀ ω : List (Fin q × Fin q × ℕ), eval (idFrame ℚ q q) (applyWord ℚ ω (res ℚ p q f)) ∈ Zl l := by
    intro ω
    obtain ⟨y, hy⟩ := levZ_sub p q w lam2 ha hb _ (Submodule.subset_span ⟨transposeWord ω, rfl⟩)
    have hyD : y ∈ DelLR l hl p q w lam2 := le_locSpan _ _ _ ((mem_MW p q w lam2 y).2 (by
      rw [hy]; exact Submodule.subset_span ⟨transposeWord ω, rfl⟩))
    have h1 := hu y hyD
    rw [mem_one_iff] at h1
    have e1 : (formB p q w lam2).restrict (rationalBlockModuleSetting p q w lam2).W u y =
        formB p q w lam2 (u : VQ p q w lam2) (y : VQ p q w lam2) := rfl
    rw [e1, formB_apply, hy, fock_word _ _ hanti _ hfN, lrj_transpose_lift,
      mul_div_assoc, div_self (ne_of_gt (hw_norm_pos _)), mul_one, ← res_eval_id ℚ p q, res_applyWord] at h1
    exact h1
  obtain ⟨m, hm, g', hg', hmg⟩ := dual_int_loc hC lower_triangular_integral l hl q lam2 _ hg hω
  have hg'h : IsWeightedHomogeneous (rowW q q) g' μ2 :=
    lrj_hom_of_smul _ g' _ m μ2 (res_rowHom ℚ p q μN f hμN) (by rw [hmg, lrc_intQ_apply])
  obtain ⟨m', hm', hy'⟩ := heL μ2 hd g' ⟨hg', hg'h⟩
  obtain ⟨d, hdL, hdres⟩ := liftWeyl p q w lam2 ha hb _ hy'
  obtain ⟨yd, hyd⟩ := levZ_sub p q w lam2 ha hb d hdL
  set c : ℤ := m' * (l : ℤ) ^ eL * m with hc
  let zW : (rationalBlockModuleSetting p q w lam2).W := (c : ℚ) • u - yd
  have hz : (zW : VQ p q w lam2) = 0 := by
    refine resInj p q w lam2 ha hb _ zW.2 ?_
    show res ℚ p q ((((c : ℚ) • u - yd : (rationalBlockModuleSetting p q w lam2).W) : VQ p q w lam2) : MvPolynomial _ ℚ) = 0
    simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul]
    rw [hyd, hdres, map_zsmul, ← hmg, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, sub_eq_zero, hc]
    congr 1
    push_cast
    ring
  have hz2 : zW = 0 := Subtype.ext hz
  have hcu : (c : ℚ) • u = yd := sub_eq_zero.mp hz2
  rw [DelLR, mem_locSpan]
  refine ⟨m' * m, ?_, ?_⟩
  · intro h
    rcases (Nat.prime_iff_prime_int.mp hl).dvd_or_dvd h with h | h
    · exact hm' h
    · exact hm h
  · rw [← Int.cast_smul_eq_zsmul ℚ, lrc_smul_def, smul_smul]
    have hsc : ((m' * m : ℤ) : ℚ) * (((l : Zl l) ^ eL : Zl l) : ℚ) = (c : ℚ) := by
      simp [hc]
      ring
    rw [hsc, hcu]
    exact (mem_MW p q w lam2 yd).2 (by rw [hyd]; exact hdL)

end Formalism.CohomologicalDescent.LR
end
end

