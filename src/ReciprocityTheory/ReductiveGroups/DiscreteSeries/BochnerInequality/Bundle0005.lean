module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchPhiOneApply
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Sch

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem phi_one_Wm (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) : phi E 1 x = 0 := by
  by_contra hne
  have := finiteDimensional_ncV (ε := ε) hV.1 1
  have hfdW : FiniteDimensional ℂ (Wm ε E V) := Submodule.finiteDimensional_of_le Wm_le_ncV
  have hWst : IsKStableSub ε (bAct E 1) (Wm ε E V) := Wm_kStable hE hU hV
  set T : Submodule ℂ M := (Wm ε E V).map (phi E 1) with hTdef
  have hfdT : FiniteDimensional ℂ T := inferInstance
  have hTst : IsKStableSub ε E T := by
    intro a b hab v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv
    rw [← phi_bAct hE 1 hab y]
    exact Submodule.mem_map_of_mem (hWst a b hab y hy)
  have hTne : T ≠ ⊥ := by
    intro hT
    have : phi E 1 x ∈ T := Submodule.mem_map_of_mem hx
    rw [hT, Submodule.mem_bot] at this
    exact hne this
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  obtain ⟨y, hyT, hy0, μ, hyμ⟩ := exists_khw hE hKU hfdT hTst hTne
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hyT
  obtain ⟨x1, hx1, -, hkhw, hfx⟩ := lift_khw (A := bAct E 1) (bAct_isKUnitary hU 1) (phi E 1)
    (fun a b hab z => phi_bAct hE 1 hab z) hfdW hWst hx₀ hyμ
  have hx10 : x1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact hy0 hfx.symm
  obtain ⟨a, b, hab, hε, hμ⟩ := Wm_khw hE hU hV hmono hh hbig hx1 hx10 hkhw
  have hlay : phi E 1 x₀ ∈ layer ε E V 1 := phi_mem_layer (Wm_le_ncV hx₀)
  have hcas : casimir E (phi E 1 x₀) = (casVal lam : ℂ) • phi E 1 x₀ :=
    casimir_genSub hE hc _ (layer_le_genSub (ε := ε) 1 hlay)
  rw [hμ] at hyμ
  exact hy0 (khw_lowK_sub_root_eq_zero ε hE hU lam hab hε
    (sch_gap ⟨hmono, h, hh, hbig⟩ hab hε) hyμ hcas)

theorem sch_coord_apply {k : ℕ} (κ : Fin k → Fin n × Fin n) (F : Big n k M) : coord k κ F = F κ := rfl

theorem sch_slice_apply {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (F : Big n k M)
    (ι : Fin 1 → Fin n × Fin n) : slice i κ F ι = F (Function.update κ i (ι 0)) := rfl

theorem sch_permute_apply {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M)
    (κ : Fin k → Fin n × Fin n) : permute σ F κ = F (κ ∘ σ) := rfl

theorem sch_word_snoc {k : ℕ} (init : Fin k → Fin n × Fin n) (p : Fin n × Fin n) :
    word E (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n) = word E init * E p.1 p.2 := by
  simp only [word, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]

theorem sch_word_one (ι : Fin 1 → Fin n × Fin n) : word E ι = E (ι 0).1 (ι 0).2 := by
  simp only [word, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]

theorem sch_phi_one_apply (G : Big n 1 M) :
    phi E 1 G = ∑ p : Fin n × Fin n, E p.1 p.2 (G (fun _ => p)) := by
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun κ => ?_)
  rw [Equiv.funUnique_apply, sch_word_one, sch_coord_apply]
  obtain ⟨p, rfl⟩ : ∃ p, κ = fun _ => p := ⟨κ 0, funext fun j => by rw [Fin.fin_one_eq_zero j]⟩
  rfl

theorem phi_Wm_last (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} {F : Big n (k + 1) M}
    (hF : ∀ κ, slice (Fin.last k) κ F ∈ Wm ε E V) : phi E (k + 1) F = 0 := by

  let e : (Fin k → Fin n × Fin n) × (Fin n × Fin n) ≃ (Fin (k + 1) → Fin n × Fin n) :=
    { toFun := fun q => Fin.snoc q.1 q.2
      invFun := fun κ => (Fin.init κ, κ (Fin.last k))
      left_inv := fun q => by simp
      right_inv := fun κ => Fin.snoc_init_self κ }
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply, sch_coord_apply]
  rw [Fintype.sum_equiv e.symm _
    (fun q => word E (Fin.snoc q.1 q.2 : Fin (k + 1) → Fin n × Fin n) (F (Fin.snoc q.1 q.2)))
    (fun κ => by simp only [e, Equiv.coe_fn_symm_mk, Fin.snoc_init_self])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun init _ => ?_
  simp only [sch_word_snoc, Module.End.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  rcases isEmpty_or_nonempty (Fin n × Fin n) with hX | ⟨⟨p0⟩⟩
  · simp
  · have h := phi_one_Wm hE hU hV hc hmono hh hbig (hF (Fin.snoc init p0))
    rw [sch_phi_one_apply] at h
    simp only [sch_slice_apply, Fin.update_snoc_last] at h
    rw [h, map_zero]

theorem phi_Wm_position (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {k : ℕ} (i : Fin (k + 1)) {F : Big n (k + 1) M} (hF0 : F ∈ ncV ε V (k + 1))
    (hF : ∀ κ, slice i κ F ∈ Wm ε E V) : phi E (k + 1) F ∈ layer ε E V k := by

  have hperm : ∀ κ, slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) ∈ Wm ε E V := by
    intro κ
    have heq : slice (Fin.last k) κ (permute (Equiv.swap i (Fin.last k)) F) =
        slice i (κ ∘ Equiv.swap i (Fin.last k)) F := by
      refine PiLp.ext fun ι => ?_
      rw [sch_slice_apply, sch_permute_apply, sch_slice_apply, Function.update_comp_equiv,
        Equiv.symm_swap, Equiv.swap_apply_right]
    rw [heq]
    exact hF _
  have h0 := phi_Wm_last hE hU hV hc hmono hh hbig hperm
  have hsub := phi_permute_sub_mem hE hV.2.1 (Equiv.swap i (Fin.last k)) hF0
  rw [h0, sub_zero] at hsub
  exact hsub

end Sch

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SltEqZeroOfCompact
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section PositionDegree

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

def slRest {k : ℕ} (i : Fin k) :
    (Fin k → Fin n × Fin n) ≃ (Fin n × Fin n) × ({j // j ≠ i} → Fin n × Fin n) :=
  Equiv.funSplitAt i _

def slt {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (A : Big n k M) : Big n 1 M :=
  WithLp.toLp 2 (fun ι : Fin 1 → Fin n × Fin n => A ((slRest i).symm (ι 0, r)))

theorem slRest_symm_self {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n) :
    (slRest i).symm (p, r) i = p := by
  simp [slRest, Equiv.funSplitAt_symm_apply]

theorem update_slRest_symm {k : ℕ} (i : Fin k) (p q : Fin n × Fin n)
    (r : {j // j ≠ i} → Fin n × Fin n) :
    Function.update ((slRest i).symm (p, r)) i q = (slRest i).symm (q, r) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [slRest, Equiv.funSplitAt_symm_apply]
  · simp [slRest, Equiv.funSplitAt_symm_apply, h]

theorem update_eq_slRest {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (q : Fin n × Fin n) :
    Function.update κ i q = (slRest i).symm (q, (slRest i κ).2) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [slRest, Equiv.funSplitAt_symm_apply]
  · simp [slRest, Equiv.funSplitAt_symm_apply, Equiv.funSplitAt_apply, h]

theorem slice_eq_slt {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (A : Big n k M) :
    slice i κ A = slt i (slRest i κ).2 A := by
  simp only [slice, slt, update_eq_slRest]

theorem slt_sum_fin_one_fun {β : Type*} [AddCommMonoid β] (f : (Fin n × Fin n) → β) :
    ∑ ι : Fin 1 → Fin n × Fin n, f (ι 0) = ∑ p, f p := by
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ (fun ι => by simp)

theorem slt_inner_eq_sum {k : ℕ} (i : Fin k) (A B : Big n k M) :
    inner ℂ A B = ∑ r, inner ℂ (slt i r A) (slt i r B) := by
  rw [PiLp.inner_apply, ← (slRest i).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [PiLp.inner_apply]
  exact (slt_sum_fin_one_fun
    (fun p => inner ℂ (A ((slRest i).symm (p, r))) (B ((slRest i).symm (p, r))))).symm

theorem slt_ofCoords_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    ofCoords k f x κ = f κ x := rfl

theorem slt_coord_apply (k : ℕ) (κ : Fin k → Fin n × Fin n) (F : Big n k M) :
    coord k κ F = F κ := rfl

theorem slt_mAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem slt_positionAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  rw [factorAd, slt_ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> simp [slt_coord_apply]

theorem slt_crossOp_apply (k : ℕ) (i : Fin k) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    crossOp ε E k i F κ = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if (κ i).1 = a then E b a (F (Function.update κ i (b, (κ i).2))) else 0) -
        (if (κ i).2 = b then E b a (F (Function.update κ i ((κ i).1, a))) else 0)) := by
  rw [← slt_coord_apply k κ (crossOp ε E k i F)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [crossOp, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [slt_coord_apply]
  change factorAd k i a b (mAct E k b a F) κ = _
  rw [slt_positionAd_apply, slt_mAct_apply, slt_mAct_apply]

private theorem slt_apply {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n)
    (A : Big n k M) (ι : Fin 1 → Fin n × Fin n) : slt i r A ι = A ((slRest i).symm (ι 0, r)) :=
  rfl

theorem slt_crossOp {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (A : Big n k M) :
    slt i r (crossOp ε E k i A) = crossOp ε E 1 0 (slt i r A) := by
  refine PiLp.ext fun ι => ?_
  rw [slt_apply, slt_crossOp_apply, slt_crossOp_apply, slRest_symm_self]
  simp only [update_slRest_symm, slt_apply, Function.update_self]

end PositionDegree

section PositionB

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem slt_mem_ncV_iff {k : ℕ} {F : Big n k M} :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap, slt_coord_apply]

theorem slRest_symm_ne {k : ℕ} (i : Fin k) (p : Fin n × Fin n) (r : {j // j ≠ i} → Fin n × Fin n)
    {j : Fin k} (h : j ≠ i) : (slRest i).symm (p, r) j = r ⟨j, h⟩ := by
  simp [slRest, Equiv.funSplitAt_symm_apply, h]

theorem slt_eq_slice {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) (p : Fin n × Fin n)
    (A : Big n k M) : slt i r A = slice i ((slRest i).symm (p, r)) A := by
  simp only [slice_eq_slt, Equiv.apply_symm_apply]

theorem slt_big_one_eq_zero (he : IsEmpty (Fin n × Fin n)) (x : Big n 1 M) : x = 0 := by
  exact PiLp.ext fun ι => (he.false (ι 0)).elim

theorem slt_slice_mem_ncV {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : slice i κ F ∈ ncV ε V 1 := by
  rw [slt_mem_ncV_iff] at hF ⊢
  intro ι
  have h := hF (Function.update κ i (ι 0))
  change F (Function.update κ i (ι 0)) ∈ _
  by_cases c : ∀ j : Fin 1, ε (ι j).1 ≠ ε (ι j).2
  · rw [if_pos c]
    split_ifs at h with c'
    · exact h
    · rw [Submodule.mem_bot] at h
      rw [h]
      exact V.zero_mem
  · rw [if_neg c]
    have c' : ¬ ∀ j, ε ((Function.update κ i (ι 0)) j).1 ≠ ε ((Function.update κ i (ι 0)) j).2 := by
      intro hall
      apply c
      intro j
      have hj := hall i
      rw [Function.update_self] at hj
      rwa [Subsingleton.elim j 0]
    rwa [if_neg c'] at h

theorem slt_mem_ncV {k : ℕ} (i : Fin k) (r : {j // j ≠ i} → Fin n × Fin n) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : slt i r F ∈ ncV ε V 1 := by
  by_cases he : IsEmpty (Fin n × Fin n)
  · rw [slt_big_one_eq_zero he (slt i r F)]
    exact Submodule.zero_mem _
  · rw [not_isEmpty_iff] at he
    obtain ⟨p⟩ := he
    rw [slt_eq_slice i r p]
    exact slt_slice_mem_ncV i _ hF

end PositionB

end ReciprocityTheory.ChartRestriction.DS
end
end

