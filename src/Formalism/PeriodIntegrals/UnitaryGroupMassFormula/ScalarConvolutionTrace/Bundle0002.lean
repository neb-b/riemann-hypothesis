module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.AveragingOperatorIdempotent
section
open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem psiNat_mul_uni (ψ₀ : AddChar F ℂ) (z : GL (Fin k) F) {u : GL (Fin k) F} (hu : IsUni k u) :
    psiNat ψ₀ (z * u) = psiNat ψ₀ z * psiU ψ₀ u := by
  unfold psiNat
  by_cases hz : IsUni k z
  · rw [if_pos (isUni_mul hz hu), if_pos hz, psiU_mul ψ₀ hz hu]
  · have : ¬ IsUni k (z * u) := fun h => hz (by simpa using isUni_mul h (isUni_inv hu))
    rw [if_neg this, if_neg hz, zero_mul]

theorem sumPsi_mul_pi (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) {u : GL (Fin k) F}
    (hu : IsUni k u) :
    (∑ x : GL (Fin k) F, psiNat ψ₀ x • π x) * π u = (psiU ψ₀ u)⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x := by
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight u) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulRight]
  rw [smul_mul_assoc, ← map_mul, psiNat_mul_uni ψ₀ x hu, smul_smul]
  congr 1
  field_simp [psiU_ne_zero ψ₀ u]

theorem projQ_comp_pi (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) {u : GL (Fin k) F}
    (hu : IsUni k u) : projQ ψ₀ π ∘ₗ π u = (psiU ψ₀ u)⁻¹ • projQ ψ₀ π := by
  rw [← Module.End.mul_eq_comp]
  unfold projQ
  rw [smul_mul_assoc, sumPsi_mul_pi ψ₀ π hu, smul_comm]

theorem sum_boole_uni : (∑ x : GL (Fin k) F, if IsUni k x then (1 : ℂ) else 0) = (cardU F k : ℂ) := by
  rw [Finset.sum_boole]
  unfold cardU
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem averaging_operator_idempotent : QIdem := by
  intro F _ _ k ψ₀ V _ _ π
  have hterm : ∀ x : GL (Fin k) F, projQ ψ₀ π * (psiNat ψ₀ x • π x) =
      (if IsUni k x then (1 : ℂ) else 0) • projQ ψ₀ π := by
    intro x
    by_cases hx : IsUni k x
    · rw [mul_smul_comm, Module.End.mul_eq_comp, projQ_comp_pi ψ₀ π hx, smul_smul, if_pos hx]
      congr 1
      unfold psiNat; rw [if_pos hx]; field_simp [psiU_ne_zero ψ₀ x]
    · unfold psiNat; rw [if_neg hx, if_neg hx, zero_smul, zero_smul, mul_zero]
  rw [← Module.End.mul_eq_comp]
  conv_lhs => rw [show projQ ψ₀ π * projQ ψ₀ π =
    projQ ψ₀ π * (((cardU F k : ℂ))⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x) from rfl]
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [hterm]
  rw [← Finset.sum_smul, smul_smul, sum_boole_uni, inv_mul_cancel₀ (cardU_ne_zero F k), one_smul]

theorem idempotent_trace_formula : IdemTrace := by
  intro V _ _ _ e he
  have h : IsIdempotentElem e := he
  exact ((LinearMap.isProj_range_iff_isIdempotentElem e).2 h).trace

end PI.GGConvScalarW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.ConvScalarOfLitOf
section
open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

theorem convScalar_of (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff) (h5 : RankLeOne)
    (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) (hm : GelfandGraevMultOne) :
    ConvScalar := by
  intro F _ _ k ψ₀ hψ V _ _ _ π hπ
  have hu : IsUni k (1 : GL (Fin k) F) :=
    ⟨fun i => by simp, fun i j hij => by simp [Matrix.one_apply_ne (ne_of_gt hij)]⟩
  have hpsi1 : psiNat ψ₀ (1 : GL (Fin k) F) = 1 := by
    simp only [psiNat, if_pos hu, psiU]
    have hs : superdiag k ((1 : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = 0 := by
      unfold superdiag
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · have hij : i ≠ j := by
          intro e
          rw [e] at h
          omega
        simp [Matrix.one_apply_ne hij]
      · rfl
    rw [hs, AddChar.map_zero_eq_one]
  have hgam : gam ψ₀ (1 : GL (Fin k) F) =
      (cardU F k : ℂ)⁻¹ * (Fintype.card (GL (Fin k) F) : ℂ) := by
    unfold gam
    simp [hpsi1]
  have hG0 : (Fintype.card (GL (Fin k) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hU0 : (cardU F k : ℂ) ≠ 0 := by
    haveI : Nonempty {x : GL (Fin k) F // IsUni k x} := ⟨⟨1, hu⟩⟩
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hdim := h9 F k V π hπ
  have hd0 : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdim.ne'
  obtain ⟨c, hc⟩ := h6 F k V π hπ (repGam ψ₀ π) fun g => h2 F k ψ₀ V π g
  have htr := h7 F k ψ₀ V π
  rw [hc, h8 V (projQ ψ₀ π) (h3 F k ψ₀ V π), map_smul, LinearMap.trace_id, smul_eq_mul] at htr
  rw [hc, hgam]
  split_ifs with hgen
  · have hne := (h4 F k ψ₀ V π).mp hgen
    have hr1 : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) = 1 := by
      have hle := h5 hm F k ψ₀ hψ V π hπ
      have hpos : Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) ≠ 0 := fun h0 =>
        hne (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
      omega
    rw [hr1, Nat.cast_one, mul_one] at htr
    have hcv : c = (Fintype.card (GL (Fin k) F) : ℂ) / (Module.finrank ℂ V : ℂ) := by
      rw [eq_div_iff hd0]
      exact htr
    rw [smul_smul, hcv]
    congr 1
    field_simp
  · have hz : projQ ψ₀ π = 0 := by
      by_contra h
      exact hgen ((h4 F k ψ₀ V π).mpr h)
    rw [hz, LinearMap.range_zero, finrank_bot, Nat.cast_zero, mul_zero] at htr
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp htr with h | h
      · exact h
      · exact absurd h hd0
    rw [hc0, zero_smul, smul_zero]

theorem convScalarOfLit_of (h1 : RepGamConj) (h2 : RepGamComm) (h3 : QIdem) (h4 : GenericIff)
    (h5 : RankLeOne) (h6 : SchurC) (h7 : TraceRepGam) (h8 : IdemTrace) (h9 : DimPos) :
    ConvScalarOfLit := by
  exact fun hm => convScalar_of h1 h2 h3 h4 h5 h6 h7 h8 h9 hm

end PI.GGConvScalarW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.Reindex
section
noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic Finset

theorem gam_conj {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (g x : GL (Fin k) F) :
    gam ψ₀ (g * x * g⁻¹) = gam ψ₀ x := by
  unfold gam
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight g) (fun y => psiNat ψ₀ (y * x * y⁻¹))]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Equiv.coe_mulRight]
  congr 1
  group

theorem representation_commutes_gamma : RepGamComm := by
  intro F _ _ k ψ₀ V _ _ π g
  apply LinearMap.ext
  intro v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [repGam, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  have hm : ∀ a b : GL (Fin k) F, π a (π b v) = π (a * b) v := fun a b => by
    rw [map_mul, Module.End.mul_apply]
  simp only [hm]

  rw [← Equiv.sum_comp (MulAut.conj g).toEquiv (fun x => gam ψ₀ x • π (x * g) v)]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [gam_conj]
  congr 2
  group

theorem representation_conjugation_apply {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin k) F) V) (y x : GL (Fin k) F) (v : V) :
    π y⁻¹ (π (y * x * y⁻¹) (π y v)) = π x v := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem representation_conjugate_gamma : RepGamConj := by
  intro F _ _ k ψ₀ V _ _ π
  apply LinearMap.ext
  intro v
  have hR : ∀ y : GL (Fin k) F, ((π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y) v =
      ∑ z, ((cardU F k : ℂ)⁻¹ * psiNat ψ₀ (y * z * y⁻¹)) • π z v := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [projQ, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum]
    rw [← Equiv.sum_comp (MulAut.conj y).toEquiv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [representation_conjugation_apply, smul_smul]
  simp only [repGam, gam, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl fun y _ => hR y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]

theorem trace_representation_gamma : TraceRepGam := by
  intro F _ _ k ψ₀ V _ _ _ π
  set_option synthInstance.maxHeartbeats 100000 in
    rw [representation_conjugate_gamma F k ψ₀ V π, map_sum]

  have h : ∀ y : GL (Fin k) F,
      LinearMap.trace ℂ V ((π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y) = LinearMap.trace ℂ V (projQ ψ₀ π) := by
    intro y
    show LinearMap.trace ℂ V (π y⁻¹ * (projQ ψ₀ π * π y)) = _
    rw [LinearMap.trace_mul_comm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end PI.GGConvScalarW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.RepresentationDimensionPos
section
noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

theorem nontrivial_of_irreducible {G : Type} [Monoid G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : π.IsIrreducible) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  apply hab
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  congr 1
  exact Subsingleton.elim a b

theorem representation_dimension_pos : DimPos := by
  intro F _ _ k V _ _ _ π hπ
  haveI := nontrivial_of_irreducible π hπ
  exact Module.finrank_pos

theorem schur_lemma_complex : SchurC := by
  intro F _ _ k V _ _ _ π hπ f hf
  haveI := nontrivial_of_irreducible π hπ
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  refine ⟨c, ?_⟩
  have hinv : ∀ (g : GL (Fin k) F) ⦃v : V⦄, v ∈ LinearMap.ker (f - c • LinearMap.id) →
      π g v ∈ LinearMap.ker (f - c • LinearMap.id) := by
    intro g v hv
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
    have h1 := congrArg (fun φ : V →ₗ[ℂ] V => φ v) (hf g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, ← map_smul, ← map_sub, hv, map_zero]
  let W : Subrepresentation π := ⟨LinearMap.ker (f - c • LinearMap.id), hinv⟩
  have hs : IsSimpleOrder (Subrepresentation π) := hπ
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  rcases hs.eq_bot_or_eq_top W with hW | hW
  · exfalso
    apply hv.2
    have hvW : v ∈ LinearMap.ker (f - c • LinearMap.id) := by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hv.apply_eq_smul, sub_self]
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    rw [h2] at hvW
    have h3 : v ∈ (⊥ : Submodule ℂ V) := hvW
    simpa using h3
  · apply LinearMap.ext
    intro x
    have h2 := congrArg Subrepresentation.toSubmodule hW
    change LinearMap.ker (f - c • LinearMap.id) = _ at h2
    have hx : x ∈ LinearMap.ker (f - c • LinearMap.id) := by
      rw [h2]
      exact (show x ∈ (⊤ : Submodule ℂ V) from Submodule.mem_top)
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx
    simpa [sub_eq_zero] using hx

end PI.GGConvScalarW
end
end

