module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrimeB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFPrime
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Tens

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem sgE_tensor (ε : Fin n → Bool) (a b : Fin n) :
    sgE ε (cpT (N := M) (n := n)) cmT a b = LinearMap.lTensor M (sgE ε cpFock cmFock a b) := by
  unfold sgE
  split_ifs
  · apply TensorProduct.ext'
    intro m f
    simp [cpT, cmT, LinearMap.sum_apply, TensorProduct.tmul_sum]
  · apply TensorProduct.ext'
    intro m f
    simp [cpT, cmT, LinearMap.sum_apply, TensorProduct.tmul_sum]
  · simp

theorem diagE_eT (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    diagE ε (eT (n := n) E) cpT cmT = fun a b => (TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b) : Module.End ℂ (TensorProduct ℂ M (Fock n))) := by
  funext a b
  rw [diagE, sgE_tensor]
  rfl

theorem casimir_eT (E : Fin n → Fin n → Module.End ℂ M) :
    casimir (eT (n := n) E) = TensorProduct.map (casimir E) LinearMap.id := by
  apply TensorProduct.ext'
  intro m f
  simp [casimir, eT, LinearMap.sum_apply, TensorProduct.sum_tmul]

theorem cfp_map_sub_smul_one (T : Module.End ℂ M) (c : ℂ) :
    TensorProduct.map (T - c • 1) (LinearMap.id : Fock n →ₗ[ℂ] Fock n) =
      TensorProduct.map T LinearMap.id - c • 1 := by
  apply TensorProduct.ext'
  intro m f
  simp [TensorProduct.sub_tmul, TensorProduct.smul_tmul']

theorem rng_lTensor {L : Submodule ℂ M} (g : Module.End ℂ (Fock n)) {y : TensorProduct ℂ M (Fock n)}
    (hy : y ∈ LinearMap.range (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n))) :
    TensorProduct.map LinearMap.id g y ∈
      LinearMap.range (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
  have h : (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)).comp
      (TensorProduct.map LinearMap.id g) =
      (TensorProduct.map LinearMap.id g).comp
        (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := by
    apply TensorProduct.ext'
    intro u f
    simp
  exact LinearMap.mem_range.mpr ⟨_, DFunLike.congr_fun h z⟩

theorem rng_map {L L' : Submodule ℂ M} (f : Module.End ℂ M) (hf : ∀ v ∈ L, f v ∈ L')
    {y : TensorProduct ℂ M (Fock n)}
    (hy : y ∈ LinearMap.range (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n))) :
    TensorProduct.map f LinearMap.id y ∈
      LinearMap.range (TensorProduct.map L'.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := by
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
  have h : (TensorProduct.map L'.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)).comp
      (TensorProduct.map (f.restrict hf) (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) =
      (TensorProduct.map f LinearMap.id).comp
        (TensorProduct.map L.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := by
    apply TensorProduct.ext'
    intro u f'
    simp
  exact LinearMap.mem_range.mpr ⟨_, DFunLike.congr_fun h z⟩

end Tens

theorem casimir_eq_casVal_of_no {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam)
    {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M}
    (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hNo : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0) :
    ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v := by
  obtain ⟨x, hx, -, hx0, hxK⟩ := lowFock_exists ε hE hmono hV
  have hxr : x ∈ LinearMap.range
      (TensorProduct.map V.subtype (LinearMap.id : Fock n →ₗ[ℂ] Fock n)) := hx
  have key : ∀ (a i : Fin n) (s : ℂ),
      ((if ε a = true then (1 : ℂ) else 0) - (if ε i = true then (1 : ℂ) else 0)) = s →
      ε a ≠ ε i → ∀ v ∈ V, E a i v ∈ layer ε E V 1 ⊓
        LinearMap.ker (zPlus ε E - ((∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) + s) • 1) := by
    intro a i s hs hne v hv
    refine Submodule.mem_inf.mpr ⟨mem_layer_one hv hne, ?_⟩
    rw [LinearMap.mem_ker]
    have h1 := LinearMap.congr_fun (zPlus_comm (ε := ε) hE a i) v
    rw [hs] at h1
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1
    rw [zPlus_V hE hV v hv, map_smul] at h1
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h1, add_smul]
    abel
  have hKHW : ∀ D : Module.End ℂ (TensorProduct ℂ M (Fock n)),
      (∀ a b, ε a = ε b → D * diagE ε (eT E) cpT cmT a b = diagE ε (eT E) cpT cmT a b * D) →
      IsKHWVec ε (fun a b => (TensorProduct.map (E a b) LinearMap.id +
        LinearMap.lTensor M (sgE ε cpFock cmFock a b) : Module.End ℂ (TensorProduct ℂ M (Fock n))))
        (lam - rhoC ε + rhoHol ε) (D x) := by
    intro D hD
    have h : IsKHWVec ε (diagE ε (eT E) cpT cmT) (lam - rhoC ε + rhoHol ε) (D x) := by
      refine ⟨fun a => ?_, fun a b hab he => ?_⟩
      · have e := LinearMap.congr_fun (hD a a rfl) x
        simp only [Module.End.mul_apply] at e
        rw [← e, hxK.1 a, map_smul]
      · have e := LinearMap.congr_fun (hD a b he) x
        simp only [Module.End.mul_apply] at e
        rw [← e, hxK.2 a b hab he, map_zero]
    have e := diagE_eT (M := M) (n := n) ε E
    rw [e] at h
    exact h
  have hp : dOp ε (eT E) cpT x = 0 := by
    apply tens_khw_vanish hmono hE hU hV hNo
      (t := (∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) + (-1))
    · intro h
      have : (-1 : ℂ) = 0 := by linear_combination h
      norm_num at this
    · simp only [dOp, LinearMap.sum_apply, Module.End.mul_apply]
      refine Submodule.sum_mem _ fun i hi => Submodule.sum_mem _ fun a ha => ?_
      have hi' : ε i = true := (Finset.mem_filter.mp hi).2
      have ha' : ε a = false := (Finset.mem_filter.mp ha).2
      exact rng_map (E a i) (key a i (-1) (by simp [hi', ha']) (by simp [hi', ha']))
        (rng_lTensor (cpFock i a) hxr)
    · exact hKHW _ fun a b hab =>
        dOp_comm_diagE (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b hab
  have hm : dOp' ε (eT E) cmT x = 0 := by
    apply tens_khw_vanish hmono hE hU hV hNo
      (t := (∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) + 1)
    · intro h
      have : (1 : ℂ) = 0 := by linear_combination h
      norm_num at this
    · simp only [dOp', LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.sum_mem _ fun a ha => ?_)
      have hi' : ε i = true := (Finset.mem_filter.mp hi).2
      have ha' : ε a = false := (Finset.mem_filter.mp ha).2
      exact rng_map (E i a) (key i a 1 (by simp [hi', ha']) (by simp [hi', ha']))
        (rng_lTensor (cmFock i a) hxr)
    · exact hKHW _ fun a b hab =>
        dOp'_comm_diagE (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b hab
  have hL : ((2 : ℂ) • ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) *
      (dOp ε (eT E) cpT + dOp' ε (eT E) cmT))) x = 0 := by
    simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.add_apply, hp, hm, add_zero,
      map_zero, smul_zero]
  rw [two_D_sq (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε] at hL
  have hK := casimirK_khwVec_compact ε (fun a b h =>
    diagE_compact (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b h) hxK
  have hS : (∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε (eT E) cpT cmT a a) x =
      ((dot (rhoHol ε) (lam - rhoC ε + rhoHol ε) : ℝ) : ℂ) • x := by
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, hxK.1, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp [dot]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
    LinearMap.smul_apply] at hL
  rw [hK, hS] at hL
  have hr : nsq (lam - rhoC ε + rhoHol ε + rhoC ε) - nsq (rhoC ε) -
      2 * dot (rhoHol ε) (lam - rhoC ε + rhoHol ε) = casVal lam := by
    have := khw_real_identity ε (lam - rhoC ε)
    rw [sub_add_cancel] at this
    rw [casVal]
    exact this
  have hC : casimir (eT E) x = ((casVal lam : ℝ) : ℂ) • x := by
    have h2 : casimir (eT E) x =
        ((nsq (lam - rhoC ε + rhoHol ε + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • x -
          (2 : ℂ) • (((dot (rhoHol ε) (lam - rhoC ε + rhoHol ε) : ℝ) : ℂ) • x) := by
      apply eq_of_sub_eq_zero
      rw [← neg_eq_zero, ← hL]
      abel
    rw [h2, ← hr]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_smul, mul_smul]
  rw [casimir_eT] at hC
  have hTw : ∀ w : M, (casimir E - ((casVal lam : ℝ) : ℂ) • 1) w =
      casimir E w - ((casVal lam : ℝ) : ℂ) • w := fun w => by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hTx : TensorProduct.map (casimir E - ((casVal lam : ℝ) : ℂ) • 1)
      (LinearMap.id : Fock n →ₗ[ℂ] Fock n) x = 0 := by
    rw [cfp_map_sub_smul_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hC,
      sub_self]
  obtain ⟨v₀, hv₀V, hv₀0, hTv₀⟩ := tens_ker_nontrivial _ hxr hx0 hTx
  have hstab : IsKStableSub ε E (V ⊓ LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • 1)) := by
    intro a b hab w hw
    obtain ⟨hwV, hwK⟩ := Submodule.mem_inf.mp hw
    rw [LinearMap.mem_ker, hTw, sub_eq_zero] at hwK
    refine Submodule.mem_inf.mpr ⟨hV.2.1 a b hab w hwV, ?_⟩
    rw [LinearMap.mem_ker, hTw]
    have hc := LinearMap.congr_fun (casimir_comm hE a b) w
    simp only [Module.End.mul_apply] at hc
    rw [hc, hwK, map_smul, sub_self]
  rcases hV.2.2.1 _ inf_le_left hstab with h | h
  · exfalso
    have hmem : v₀ ∈ V ⊓ LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • 1) :=
      Submodule.mem_inf.mpr ⟨hv₀V, hTv₀⟩
    rw [h] at hmem
    exact hv₀0 ((Submodule.mem_bot ℂ).mp hmem)
  · intro v hv
    have hmem : v ∈ V ⊓ LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • 1) := by
      rw [h]
      exact hv
    have hk := (Submodule.mem_inf.mp hmem).2
    rw [LinearMap.mem_ker, hTw] at hk
    exact sub_eq_zero.mp hk

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharpA
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

abbrev tco (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)) : M :=
  tcoef ((fockBasis n).coord s) y

def tform (y y' : TensorProduct ℂ M (Fock n)) : ℂ :=
  ∑ s, inner ℂ (tco s y) (tco s y')

theorem tform_conj (y y' : TensorProduct ℂ M (Fock n)) : star (tform y y') = tform y' y := by
  unfold tform
  rw [star_sum]
  exact sum_congr rfl fun s _ => inner_conj_symm _ _

theorem tform_sum_left {ι : Type*} (t : Finset ι) (f : ι → TensorProduct ℂ M (Fock n))
    (y' : TensorProduct ℂ M (Fock n)) : tform (∑ i ∈ t, f i) y' = ∑ i ∈ t, tform (f i) y' := by
  unfold tform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, sum_inner]
  exact sum_comm

theorem tform_sum_right {ι : Type*} (t : Finset ι) (f : ι → TensorProduct ℂ M (Fock n))
    (y : TensorProduct ℂ M (Fock n)) : tform y (∑ i ∈ t, f i) = ∑ i ∈ t, tform y (f i) := by
  unfold tform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, inner_sum]
  exact sum_comm

theorem tform_neg_left (y y' : TensorProduct ℂ M (Fock n)) : tform (-y) y' = -tform y y' := by
  unfold tform
  simp [inner_neg_left]

theorem tform_neg_right (y y' : TensorProduct ℂ M (Fock n)) : tform y (-y') = -tform y y' := by
  unfold tform
  simp [inner_neg_right]

theorem tform_add_left (y z y' : TensorProduct ℂ M (Fock n)) :
    tform (y + z) y' = tform y y' + tform z y' := by
  unfold tform
  simp [sum_add_distrib]

theorem tform_add_right (y y' z : TensorProduct ℂ M (Fock n)) :
    tform y (y' + z) = tform y y' + tform y z := by
  unfold tform
  simp [sum_add_distrib]

theorem tform_smul_right (c : ℂ) (y y' : TensorProduct ℂ M (Fock n)) :
    tform y (c • y') = c * tform y y' := by
  unfold tform
  simp [mul_sum]

theorem tform_self_re (y : TensorProduct ℂ M (Fock n)) : (tform y y).re = ∑ s, ‖tco s y‖ ^ 2 := by
  unfold tform
  rw [Complex.re_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem tform_self_re_nonneg (y : TensorProduct ℂ M (Fock n)) : 0 ≤ (tform y y).re := by
  rw [tform_self_re]
  exact sum_nonneg fun s _ => sq_nonneg _

theorem tform_self_re_pos {y : TensorProduct ℂ M (Fock n)} (hy : y ≠ 0) : 0 < (tform y y).re := by
  rcases (tform_self_re_nonneg y).lt_or_eq with h | h
  · exact h
  exfalso
  rw [tform_self_re] at h
  have h0 : ∀ s, tcoef ((fockBasis n).coord s) y = 0 := by
    intro s
    have hs := (sum_eq_zero_iff_of_nonneg (fun t _ => sq_nonneg ‖tco t y‖)).mp h.symm s (mem_univ s)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hs)
  apply hy
  rw [tcoef_expand y]
  exact sum_eq_zero fun s _ => by rw [h0 s, TensorProduct.zero_tmul]

theorem tco_map_left (T : Module.End ℂ M) (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)) :
    tco s (TensorProduct.map T LinearMap.id y) = T (tco s y) :=
  tcoef_map_left _ T y

theorem tco_lTensor (g : Module.End ℂ (Fock n)) (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)) :
    tco s (TensorProduct.map LinearMap.id g y) =
      ∑ t, (fockBasis n).repr (g (fockBasis n t)) s • tco t y := by
  conv_lhs => rw [tcoef_expand y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, tcoef_tmul, Module.Basis.coord_apply]

theorem tform_eT {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (a b : Fin n)
    (y y' : TensorProduct ℂ M (Fock n)) :
    tform (eT E a b y) y' = adjSign ε a b * tform y (eT E b a y') := by
  unfold tform eT
  simp only [tco_map_left, mul_sum]
  exact sum_congr rfl fun s _ => hU a b _ _

theorem tform_cpT (i a : Fin n) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (cpT i a y) y' = tform y (cmT i a y') := by
  unfold tform cpT cmT
  simp only [tco_lTensor, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun s _ => ?_
  congr 1
  have h1 := lf_repr_cp_star (i, a) t s
  have h2 := lf_repr_cm_eq (i, a) s t
  rw [h2, starRingEnd_apply]
  exact h1

theorem tform_cmT (i a : Fin n) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (cmT i a y) y' = tform y (cpT i a y') := by
  rw [← tform_conj y' (cmT i a y), ← tform_cpT, tform_conj]

theorem tform_dOp {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    (y y' : TensorProduct ℂ M (Fock n)) :
    tform (dOp ε (eT E) cpT y) y' = tform y (dOp' ε (eT E) cmT y') := by
  unfold dOp dOp'
  simp only [LinearMap.sum_apply, LinearMap.neg_apply, tform_sum_left, tform_neg_right, tform_sum_right,
    Module.End.mul_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun a ha => ?_
  simp only [plusIdx, minusIdx, mem_filter, mem_univ, true_and] at hi ha
  rw [tform_eT hU, tform_cpT]
  have hc : cmT i a (eT E i a y') = eT E i a (cmT i a y') := by
    have := LinearMap.congr_fun ((eT_commutesCAR (n := n) E) i a i a).2 y'
    simp only [Module.End.mul_apply] at this
    exact this.symm
  rw [hc]
  simp [adjSign, hi, ha]

theorem tform_D {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    (y y' : TensorProduct ℂ M (Fock n)) :
    tform ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y) y' =
      tform y ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) y') := by
  have h' : tform (dOp' ε (eT E) cmT y) y' = tform y (dOp ε (eT E) cpT y') := by
    rw [← tform_conj y' (dOp' ε (eT E) cmT y), ← tform_dOp hU, tform_conj]
  rw [LinearMap.add_apply, LinearMap.add_apply, tform_add_left, tform_add_right, tform_dOp hU, h', add_comm]

section Shift

theorem ssh_root_le (a b c : Fin n) : root a b c ≤ 1 := by
  unfold root
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

theorem ssh_root_ge (a b c : Fin n) : -1 ≤ root a b c := by
  unfold root
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> norm_num

theorem ssh_rhoN_consec (ε : Fin n → Bool) {x y : Fin n} (hxy : x < y) (he : ε x = ε y)
    (hc : ∀ c, x < c → c < y → False) : rhoN ε x = rhoN ε y := by
  have h := lfD_cnt (fun c => ε c ≠ ε x) hxy
  have h1 : (univ.filter fun c => c = x ∧ ε c ≠ ε x).card = 0 := by
    rw [lfD_single]; simp
  have h2 : (univ.filter fun c => c = y ∧ ε c ≠ ε x).card = 0 := by
    rw [lfD_single]; simp [he]
  have h3 : (univ.filter fun c => x < c ∧ c < y ∧ ε c ≠ ε x).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro c _ hc'
    exact hc c hc'.1 hc'.2.1
  simp only [rhoN, ← he]
  rw [h1, h2, h3] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  linarith

theorem ssh_strictAnti {ε : Fin n → Bool} {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) (h2 : 2 < h) {N : Type*} [AddCommGroup N] [Module ℂ N]
    {E : Fin n → Fin n → Module.End ℂ N} (hE : IsGlRep E) (a b : Fin n) {W : Submodule ℂ N}
    (hW : IsKIrrHW ε E (lowK ε (lam - root a b)) W) : StrictAnti (lam - root a b) := by
  have hF : Formalism.REAL.KRel ε E := fun a b c d _ _ => hE a b c d
  cases n with
  | zero => exact fun x => x.elim0
  | succ m =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have hxy : i.castSucc < i.succ := Fin.castSucc_lt_succ
    have hl := hmono hxy
    simp only [Pi.sub_apply]
    by_cases he : ε i.castSucc = ε i.succ
    · obtain ⟨N, hN⟩ := HW.kIrrHW_int ε hF hW _ _ hxy he
      have hbet : ∀ c, i.castSucc < c → c < i.succ → False := by
        intro c h1 h2
        rw [Fin.lt_def] at h1 h2
        simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
        omega
      have hC := HW.rhoC_consec ε hxy he (fun c h1 h2 => (hbet c h1 h2).elim)
      have hN' := ssh_rhoN_consec ε hxy he hbet
      simp only [lowK, Pi.add_apply, Pi.sub_apply] at hN
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    · have hg := hh _ _ he
      rw [abs_of_pos (sub_pos.mpr hl)] at hg
      have := ssh_root_le a b i.castSucc
      have := ssh_root_ge a b i.succ
      linarith

theorem ssh_casimir_eT {N : Type*} [AddCommGroup N] [Module ℂ N] (E : Fin n → Fin n → Module.End ℂ N) :
    casimir (eT (n := n) E) = TensorProduct.map (casimir E) LinearMap.id := by
  apply TensorProduct.ext'
  intro m f
  simp [casimir, eT, LinearMap.sum_apply, TensorProduct.sum_tmul]

theorem ssh_nsq_sub_root (lam : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    nsq (lam - root a b) = nsq lam - 2 * (lam a - lam b) + 2 := by
  have e : nsq (lam - root a b) = nsq lam - 2 * dot (root a b) lam + dot (root a b) (root a b) := by
    unfold nsq dot
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    simp only [Pi.sub_apply]
    ring
  rw [e, dot_root_left, dot_root_left]
  have ha : root a b a = 1 := by simp [root, hab]
  have hb : root a b b = -1 := by simp [root, Ne.symm hab]
  rw [ha, hb]
  ring

end Shift

end ReciprocityTheory.ChartRestriction.DS
end
end

