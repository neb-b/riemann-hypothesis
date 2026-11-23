module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MeasurePrjFPreimage
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Imports
section
noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem core {c : ℕ} (hc : Nat.Coprime c X.B.g)
    (hec : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g)
    (hfc : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g)
    {A Ai By : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)}
    (hAL : ∀ v ∈ X.B.I.Lf, A *ᵥ v ∈ X.B.I.Lf) (hAiL : ∀ v ∈ X.B.I.Lf, Ai *ᵥ v ∈ X.B.I.Lf)
    (hByL : ∀ v ∈ X.B.I.Lf, By *ᵥ v ∈ X.B.I.Lf) (hAiA : Ai * A = 1) (hAAi : A * Ai = 1)
    (hAform : ∀ x y, hA X.B.I (A *ᵥ x) (A *ᵥ y) = hA X.B.I x y)
    (hAe : ∀ a, A *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a))
    (hN1 : ∀ a, (By - 1) *ᵥ incl X.B.I (X.eR a) ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
      ((fun b => incl X.B.I (X.eR b)) '' {b | b.1 < a.1}))
    (zz : VA X.B.I)
    (hN2 : (By - 1) *ᵥ zz ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
      (Set.range fun b => incl X.B.I (X.eR b)))
    (hN3 : ∀ v : VA X.B.I, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) v = 0) →
      (By - 1) *ᵥ v ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)))
    (hzc : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz - X.z0) ∈ mL X.B.I X.B.g) :
    (∀ a, InMod X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}) (Tm Ai By A (X.e0 a))) ∧
      InMod X.B.I X.B.g (Set.range X.e0) (Tm Ai By A X.z0) ∧
      ∀ i, InMod X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) (Tm Ai By A (X.bw i)) := by
  have hAie : ∀ a, Ai *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := by
    intro a
    conv_lhs => rw [← hAe a]
    rw [mulVec_mulVec, hAiA, one_mulVec]
  have hspan : ∀ (s : Set (Fin D.R.rS)) (w : VA X.B.I),
      w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s) →
      Ai *ᵥ w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s) := by
    intro s w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      rw [hAie]; exact Submodule.subset_span ⟨b, hb, rfl⟩
    | zero => rw [mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
    | smul r x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ r hx
  have hTL := Tm_Lf hAiL hByL hAL
  have hTmL := Tm_mL X.B.g hAiL hByL hAL
  have hmLL := mL_le_Lf X.B.I X.B.g
  have hcI := natCast_int X.B.I c
  have hWL : ∀ v ∈ X.B.I.Lf, Ai *ᵥ ((By - 1) *ᵥ v) ∈ X.B.I.Lf := fun v hv => hAiL _ (sub_one_Lf hByL _ hv)
  have heL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR b) ∈ X.B.I.Lf := by
    intro b
    have h : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR b) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b -
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) := by
      rw [← smul_sub, sub_sub_cancel]
    rw [h]; exact sub_mem (sm X.B.I hcI (X.vectorsInLattice.1 b).1) (hmLL (hec b))
  have hfL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) ∈ X.B.I.Lf := by
    intro b
    have h : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.f0 b -
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) := by
      rw [← smul_sub, sub_sub_cancel]
    rw [h]; exact sub_mem (sm X.B.I hcI (X.vectorsInLattice.1 b).2) (hmLL (hfc b))
  have hsig : starRingEnd X.B.I.E = (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) := by
    exact RingHom.ext fun _ => rfl
  have hpair (a b : Fin D.R.rS) :
      hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
    rw [hA_incl, hsig]
    change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
        (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b))) = _
    rw [MassDataLevelSSteps.FrameW.hE_crdOf X, X.ef]
    split_ifs <;> simp
  have hpair_rev (b a : Fin D.R.rS) :
      hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if b = a then 1 else 0 := by
    let : StarRing D.host.E := D.host.cmStar
    rw [hA_incl, hsig]
    change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
        (crdOf X.B.I X.ιE X.bas (X.fY b)) (crdOf X.B.I X.ιE X.bas (X.eX a))) = _
    rw [MassDataLevelSSteps.FrameW.hE_crdOf X,
      ← LinearMap.isSymm_def.1 (VS D).herm (X.eX a) (X.fY b), X.ef]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hclear {d : ℕ} {s : Set (Fin D.R.rS)} {w : VA X.B.I}
      (hw : w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s))
      (hdw : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈ X.B.I.Lf) :
      ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈
        Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' s) ⊔ mL X.B.I X.B.g := by
    classical
    obtain ⟨l, hls, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hw
    have hsum : Finsupp.linearCombination (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun b => incl X.B.I (X.eR b)) l =
        ∑ b, l b • incl X.B.I (X.eR b) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i
      exact zero_smul _ _
    rw [hsum] at hdw ⊢
    have hcoef (b : Fin D.R.rS) :
        ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b ∈ IntAf X.B.I.F X.B.I.E := by
      have h := hA_int X.B.I _ (hfL b) _ hdw
      rw [hA_nat_left, hA_smul_right, hA_sum_right] at h
      simp only [hA_smul_right, hpair_rev, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true] at h
      convert h using 1
      push_cast
      ring
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : l b = 0
    · rw [hb, zero_smul, smul_zero]
      exact zero_mem _
    have hbs : b ∈ s := hls (Finsupp.mem_support_iff.2 hb)
    have heq : ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (l b • incl X.B.I (X.eR b)) =
        (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b) -
        (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) •
          ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) := by
      rw [← smul_sub, ← smul_sub, sub_sub_cancel]
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [heq]
    refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (sm X.B.I (hcoef b) (hec b)))
    exact sm X.B.I (hcoef b) (sm X.B.I hcI (Submodule.subset_span ⟨b, hbs, rfl⟩))
  have hc3 : Nat.Coprime (c * c * c) X.B.g := Nat.Coprime.mul_left (Nat.Coprime.mul_left hc hc) hc
  refine ⟨fun a => ?_, ?_, fun i => ?_⟩
  ·
    have hv := hTL _ (X.vectorsInLattice.1 a).1
    have hTe : Tm Ai By A (incl X.B.I (X.eR a)) = Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.eR a)) := by
      simp only [Tm, hAe]
    have hsplit : Tm Ai By A (X.e0 a) =
        Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.eR a)) + Tm Ai By A (X.e0 a - incl X.B.I (X.eR a)) := by
      rw [Tm_sub, hTe]; abel
    have hw := hspan _ _ (hN1 a)
    have hdw : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.eR a))) ∈ X.B.I.Lf := by
      rw [← mulVec_smul, ← mulVec_smul]; exact hWL _ (heL a)
    have hk := hclear hw hdw
    unfold InMod
    refine close X.B.I le_sup_right hv hsplit hc hc3 hk ?_
    rw [← Tm_smul]; exact hTmL _ (hec a)
  ·
    have hv := hTL _ X.vectorsInLattice.2.1
    have hAq : A *ᵥ (Ai *ᵥ zz) = zz := by rw [mulVec_mulVec, hAAi, one_mulVec]
    have hTq : Tm Ai By A (Ai *ᵥ zz) = Ai *ᵥ ((By - 1) *ᵥ zz) := by simp only [Tm, hAq]
    have hsplit : Tm Ai By A X.z0 = Ai *ᵥ ((By - 1) *ᵥ zz) + -Tm Ai By A (Ai *ᵥ zz - X.z0) := by
      rw [Tm_sub, hTq]; abel
    have hw : Ai *ᵥ ((By - 1) *ᵥ zz) ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
        ((fun b => incl X.B.I (X.eR b)) '' Set.univ) := hspan _ _ (by rw [Set.image_univ]; exact hN2)
    have hcq : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz) ∈ X.B.I.Lf := by
      have h : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz) =
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz - X.z0) := by
        rw [← smul_add, add_sub_cancel]
      rw [h]; exact add_mem (sm X.B.I hcI X.vectorsInLattice.2.1) (hmLL hzc)
    have hcz : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • zz ∈ X.B.I.Lf := by
      rw [← hAq, ← mulVec_smul]; exact hAL _ hcq
    have hdw : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ ((By - 1) *ᵥ zz)) ∈ X.B.I.Lf := by
      rw [← mulVec_smul, ← mulVec_smul]; exact hWL _ hcz
    have hk := hclear hw hdw
    rw [Set.image_univ] at hk
    unfold InMod
    refine close X.B.I le_sup_right hv hsplit hc hc3 hk ?_
    rw [smul_neg, ← Tm_smul]; exact neg_mem (hTmL _ hzc)
  ·
    have hbL := (X.vectorsInLattice.2.2 i).1
    have hv := hTL _ hbL
    obtain ⟨t, ht⟩ : ∃ t, A *ᵥ X.bw i = t := ⟨_, rfl⟩
    have htL : t ∈ X.B.I.Lf := ht ▸ hAL _ hbL
    obtain ⟨t', ht'⟩ : ∃ t', t - ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • incl X.B.I (X.fR b) = t' := ⟨_, rfl⟩
    have horth : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) t' = 0 := by
      intro a
      rw [← ht', hA_sub_right, hA_sum_right]
      simp only [hA_smul_right, hpair, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, sub_self]
    have hsplit : Tm Ai By A (X.bw i) = Ai *ᵥ ((By - 1) *ᵥ t') +
        ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • (Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.fR b))) := by
      have h : t = t' + ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • incl X.B.I (X.fR b) := by
        rw [← ht', sub_add_cancel]
      simp only [Tm, ht]
      conv_lhs => rw [h]
      rw [mulVec_add, mulVec_add, mulVec_sum, mulVec_sum]
      simp only [mulVec_smul]
    have hw : Ai *ᵥ ((By - 1) *ᵥ t') ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
        ((fun b => incl X.B.I (X.eR b)) '' Set.univ) :=
      hspan _ _ (by rw [Set.image_univ]; exact hN3 _ horth)
    have hZ : ∀ b, ∃ τ ∈ IntAf X.B.I.F X.B.I.E,
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (incl X.B.I (X.eR b)) t =
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * τ := by
      intro b
      have h1 : hA X.B.I (incl X.B.I (X.eR b)) t = hA X.B.I (incl X.B.I (X.eR b)) (X.bw i) := by
        calc hA X.B.I (incl X.B.I (X.eR b)) t
            = hA X.B.I (A *ᵥ incl X.B.I (X.eR b)) (A *ᵥ X.bw i) := by rw [hAe, ht]
          _ = _ := hAform _ _
      have h2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (incl X.B.I (X.eR b)) (X.bw i) =
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (X.e0 b) (X.bw i) -
            hA X.B.I ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) (X.bw i) := by
        rw [hA_nat_left, hA_sub_left]; ring
      obtain ⟨t1, ht1, he1⟩ := ((X.weightVectorsIntegral i).2.2 b).1
      obtain ⟨t2, ht2, he2⟩ := hA_mL_left X.B.I X.B.g _ (hec b) _ hbL
      exact ⟨(c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t1 - t2, sub_mem (mul_mem hcI ht1) ht2,
        by rw [h1, h2, he1, he2]; ring⟩
    choose τ hτI hτ using hZ
    have hterm : ∀ b (V : VA X.B.I),
        ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (incl X.B.I (X.eR b)) t • V) =
          τ b • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • V)) := by
      intro b V
      simp only [smul_smul]
      congr 1
      push_cast
      linear_combination (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hτ b
    have hr : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
        ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • (Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.fR b))) ∈ mL X.B.I X.B.g := by
      rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [hterm]
      refine sm X.B.I (hτI b) (smul_mem_mL X.B.I X.B.g ?_)
      rw [← mulVec_smul, ← mulVec_smul]; exact hWL _ (hfL b)
    have hdw : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ ((By - 1) *ᵥ t')) ∈ X.B.I.Lf := by
      rw [← mulVec_smul, ← mulVec_smul]
      refine hWL _ ?_
      rw [← ht', smul_sub, Finset.smul_sum]
      refine sub_mem (sm X.B.I (natCast_int X.B.I _) htL) (Submodule.sum_mem _ fun b _ => ?_)
      rw [hterm]
      exact hmLL (sm X.B.I (hτI b) (smul_mem_mL X.B.I X.B.g (hfL b)))
    have hk := hclear hw hdw
    have hle : Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' Set.univ) ⊔ mL X.B.I X.B.g ≤
        Submodule.span (IntAf X.B.I.F X.B.I.E) (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ⊔ mL X.B.I X.B.g :=
      sup_le_sup_right (Submodule.span_mono (by rw [Set.image_univ]; exact Set.subset_union_left)) _
    have hcc : Nat.Coprime (c * c) X.B.g := Nat.Coprime.mul_left hc hc
    have hc4 : Nat.Coprime (c * (c * c) * c) X.B.g := Nat.Coprime.mul_left (Nat.Coprime.mul_left hc hcc) hc
    unfold InMod
    exact close X.B.I le_sup_right hv hsplit hcc hc4 (hle hk) hr

end MassDataMassesW.NLev
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsCompactStabGLHat
section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Char

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

def stabGLHat (Λ : Set (Fin n → E)) : Set (GL (Fin n) (Af F ⊗[F] E)) :=
  {g | (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ) ∧
    ((g⁻¹ : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ)}

theorem mem_Kloc_of (Λ : Set (Fin n → E)) {g : GL (Fin n) (Af F ⊗[F] E)} (hg : g ∈ stabGLHat Λ)
    (v : HeightOneSpectrum (𝓞 F)) : compV v g ∈ Kloc (E := E) v Λ := by
  intro y
  constructor
  · intro hy
    exact loc_of_matStab Λ hg.1 v hy
  · intro hy
    have hy' : ((g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map (tensMap (E := E) (evalV F v))) *ᵥ y ∈
        latLoc (E := E) v Λ := hy
    have h := loc_of_matStab Λ hg.2 v hy'
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h

theorem matStab_of_mem (Λ : Set (Fin n → E)) {g : GL (Fin n) (Af F ⊗[F] E)}
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), compV v g ∈ Kloc (E := E) v Λ) :
    (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ) := by
  intro x hx v
  rw [pv_mulVec]
  exact ((hg v) (pv v x)).1 (hx v)

theorem kf_iff (Λ : Set (Fin n → E)) (g : HA (Af F) σ J) :
    g ∈ Kf σ J Λ ↔ incAf σ J g ∈ stabGLHat Λ := by
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ Kf σ J Λ := (Kf σ J Λ).inv_mem hg
    refine ⟨matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg v), ?_⟩
    rw [← map_inv]
    exact matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg' v)
  · intro h
    rw [Kf, Subgroup.mem_iInf]
    intro v
    exact mem_Kloc_of Λ h v

end Char

def LatHatOpen : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → L.FG →
    IsOpen (latHat (F := F) (L : Set (Fin n → E)))

def LatHatCompact : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → L.FG →
    IsCompact (latHat (F := F) (L : Set (Fin n → E)))

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {n : ℕ}

theorem pv_intSmul_single (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (j : Fin n) :
    pv v ((N : F) • (Pi.single j 1 : Fin n → Af F ⊗[F] E)) = ratV (F := F) (Fv F v) (N • (Pi.single j (1 : E) : Fin n → E)) := by
  classical
  funext i
  by_cases h : i = j
  · subst h
    simp [pv, ratV, Algebra.smul_def, tensMap, inclR]
  · simp [pv, ratV, h, tensMap, inclR]

theorem hcol_hat (L : Submodule (𝓞 E) (Fin n → E)) {N : ℤ}
    (hN : ∀ j : Fin n, N • (Pi.single j (1 : E) : Fin n → E) ∈ L) (j : Fin n) :
    (N : F) • (Pi.single j 1 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) (L : Set (Fin n → E)) := by
  intro v
  rw [pv_intSmul_single]
  exact Submodule.subset_span ⟨_, hN j, rfl⟩

theorem isCompact_stabGLHat (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hc : IsCompact (latHat (F := F) (L : Set (Fin n → E)))) :
    IsCompact (stabGLHat (F := F) (L : Set (Fin n → E))) := by
  classical
  set M := latHat (F := F) (L : Set (Fin n → E))
  have hMcl : IsClosed M := hc.isClosed
  obtain ⟨N, hN0, hNmem⟩ := exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))
  have hN : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  have hSc := isCompact_matStab (K := F) hc hMcl (N : F) hN (hcol_hat L hNmem)
  have e : stabGLHat (F := F) (L : Set (Fin n → E)) =
      Units.embedProduct _ ⁻¹' (matStab M ×ˢ (MulOpposite.op '' matStab M)) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨_, h2, rfl⟩⟩
    · rintro ⟨h1, y, hy, hyg⟩
      refine ⟨h1, ?_⟩
      have hy' : y = (((g⁻¹ : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
        MulOpposite.op_injective hyg
      rwa [hy'] at hy
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod (hSc.image MulOpposite.continuous_op))

theorem isOpen_stabGLHat (L : Submodule (𝓞 E) (Fin n → E))
    (hc : IsCompact (latHat (F := F) (L : Set (Fin n → E))))
    (ho : IsOpen (latHat (F := F) (L : Set (Fin n → E)))) :
    IsOpen (stabGLHat (F := F) (L : Set (Fin n → E))) := by
  have hS := isOpen_matStab hc ho
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

end Glob

end MassDataMassesW.KCptW

namespace MassDataMassesW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub KCptW

end MassDataMassesW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassUnfoldGenHolds
section
noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem massUnfoldGen_holds : PIW.MassDataColumns.MassUnfoldGen := by
  intro D X u hM _ U _ hUo hfin 𝓕 h𝓕
  exact massUnfold_gen (hCM := isCMExt_of_cmData X.B.I.cm) (hJ := isHermND_of_setting X) (M := X.measW u)
    (hM := hM) (U := U) (hU := hUo.measurableSet) (hfin := hfin) (𝓕 := 𝓕) (h𝓕 := h𝓕)

end MassDataMassesW
end
end

