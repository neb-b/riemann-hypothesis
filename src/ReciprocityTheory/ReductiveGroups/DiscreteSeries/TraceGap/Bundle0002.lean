module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.IsPhysSet
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.BlockAnti

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdMatConjTranspose
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem kset_entry_zero {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {i j : Fin n}
    (h : ε i ≠ ε j) : k i j = 0 := by
  have h1 := congrFun (congrFun hk.2 i) j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : k i j * ((if ε j then (1 : ℂ) else -1) - (if ε i then 1 else -1)) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exfalso
    clear h1 h2 hk
    revert h h3
    cases ε i <;> cases ε j <;> norm_num

theorem adMat_mul {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (_hk' : k' ∈ Kset ε) :
    adMat ε (k * k') = adMat ε k * adMat ε k' := by
  ext x y
  rw [Matrix.mul_apply]
  by_cases hx : IsPhys ε x
  · by_cases hy : IsPhys ε y
    · simp only [adMat, hx, hy, if_true]
      rw [Fintype.sum_prod_type, Matrix.mul_apply, Matrix.mul_apply, star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      by_cases hz : IsPhys ε (u, v)
      · simp only [hz, if_true, star_mul']
        ring
      · simp only [hz, if_false, zero_mul]
        have hz' : ¬ (ε u = true ∧ ε v = false) := hz
        by_cases hu : ε u = true
        · have hv : ε v ≠ false := fun hv => hz' ⟨hu, hv⟩
          have : k x.2 v = 0 := kset_entry_zero hk (by rw [hx.2]; exact Ne.symm hv)
          simp [this]
        · have : k x.1 u = 0 := kset_entry_zero hk (by rw [hx.1]; exact Ne.symm hu)
          simp [this]
    · simp only [adMat, hx, hy, if_true, if_false]
      refine (Finset.sum_eq_zero fun z _ => ?_).symm
      split_ifs <;> simp
  · simp only [adMat, hx, if_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem adPhys_mul {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hk' : k' ∈ Kset ε) :
    adPhys ε (k * k') = adPhys ε k ∘ₗ adPhys ε k' := by
  rw [adPhys, adPhys, adPhys, adMat_mul hk hk', Matrix.mulVecLin_mul]

theorem ff_mul {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hk' : k' ∈ Kset ε) :
    ff ε (k * k') = (ff ε k).comp (ff ε k') := by
  rw [ff, ff, ff, adPhys_mul hk hk', ExteriorAlgebra.map_comp_map]

theorem adMat_one : adMat ε (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext x y
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  by_cases hx : IsPhys ε (x1, x2) <;> by_cases hy : IsPhys ε (y1, y2)
  · simp only [adMat, hx, hy, if_true, Matrix.one_apply, Prod.mk.injEq]
    by_cases h1 : x1 = y1 <;> by_cases h2 : x2 = y2 <;> simp [h1, h2]
  · have : (x1, x2) ≠ (y1, y2) := fun h => hy (h ▸ hx)
    simp only [adMat, hx, hy, if_true, if_false, Matrix.one_apply, this]
  · simp only [adMat, hx, if_false, Matrix.one_apply]
  · simp only [adMat, hx, if_false, Matrix.one_apply]

theorem ff_one : ff ε 1 = AlgHom.id ℂ (Fock n) := by
  rw [ff, adPhys, adMat_one, Matrix.mulVecLin_one, ExteriorAlgebra.map_id]

theorem ff_comp_involute (k : Matrix (Fin n) (Fin n) ℂ) :
    (ff ε k).comp CliffordAlgebra.involute = CliffordAlgebra.involute.comp (ff ε k) := by
  apply ExteriorAlgebra.hom_ext
  refine LinearMap.ext fun m => ?_
  simp [ff, ExteriorAlgebra.map_apply_ι]

theorem ff_involute (k : Matrix (Fin n) (Fin n) ℂ) (x : Fock n) :
    ff ε k (CliffordAlgebra.involute x) = CliffordAlgebra.involute (ff ε k x) :=
  AlgHom.congr_fun (ff_comp_involute k) x

theorem map_contractLeft {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (d : Module.Dual ℂ N) (x : ExteriorAlgebra ℂ M) :
    ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d ∘ₗ f) x) =
      CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | ι_mul x m hx =>
    rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul, hx, map_mul,
      ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul, LinearMap.comp_apply]

theorem cpFock_eq_cpV (i a : Fin n) : cpFock i a = cpV (Pi.single (i, a) (1 : ℂ)) := rfl

theorem dualV_single (x : Fin n × Fin n) :
    dualV (Pi.single x (1 : ℂ)) = LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) x := by
  refine LinearMap.ext fun w => ?_
  simp [dualV, Pi.single_apply]

theorem cmFock_eq_cmV (i a : Fin n) : cmFock i a = cmV (Pi.single (i, a) (1 : ℂ)) := by
  rw [cmV, dualV_single]
  rfl

theorem ff_cpV (k : Matrix (Fin n) (Fin n) ℂ) (v : Fin n × Fin n → ℂ) :
    (ff ε k).toLinearMap * cpV v = cpV (adPhys ε k v) * (ff ε k).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, cpV, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul, ff,
    ExteriorAlgebra.map_apply_ι]

theorem adMat_conjTranspose (k : Matrix (Fin n) (Fin n) ℂ) : (adMat ε k)ᴴ = adMat ε kᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, adMat]
  by_cases hx : IsPhys ε x <;> by_cases hy : IsPhys ε y
  · simp [hx, hy, star_mul', mul_comm]
  · have : y ≠ x := fun h => hy (h ▸ hx)
    simp [hx, hy, this]
  · have : x ≠ y := fun h => hx (h ▸ hy)
    simp [hx, hy, this, Ne.symm this]
  · simp only [hx, hy, if_false]
    by_cases h : y = x
    · subst h; simp
    · simp [h, Ne.symm h]

theorem kset_conjTranspose {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : kᴴ ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · have := hk.1
    rw [Matrix.mem_unitaryGroup_iff] at this ⊢
    rw [star_eq_conjTranspose, conjTranspose_conjTranspose]
    rw [star_eq_conjTranspose] at this
    exact mul_eq_one_comm.mp this
  · have hJ : (Jm ε)ᴴ = Jm ε := by
      simp only [Jm, Matrix.diagonal_conjTranspose]
      congr 1
      funext a
      by_cases h : ε a = true <;> simp [h]
    have := congrArg Matrix.conjTranspose hk.2
    rw [conjTranspose_mul, conjTranspose_mul, hJ] at this
    exact this.symm

theorem adMat_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : (adMat ε k)ᴴ * adMat ε k = 1 := by
  rw [adMat_conjTranspose, ← adMat_mul (kset_conjTranspose hk) hk]
  have : kᴴ * k = 1 := by
    have := hk.1
    rw [Matrix.mem_unitaryGroup_iff'] at this
    rwa [star_eq_conjTranspose] at this
  rw [this, adMat_one]

theorem dualV_eq_dot (w u : Fin n × Fin n → ℂ) : dualV w u = star w ⬝ᵥ u := by
  simp [dualV, dotProduct]

theorem dualV_adPhys {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : Fin n × Fin n → ℂ) :
    dualV v = dualV (adPhys ε k v) ∘ₗ adPhys ε k := by
  refine LinearMap.ext fun u => ?_
  rw [LinearMap.comp_apply, dualV_eq_dot, dualV_eq_dot]
  simp only [adPhys, Matrix.mulVecLin_apply]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, adMat_unitary hk, Matrix.vecMul_one]

theorem ff_cmV {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (v : Fin n × Fin n → ℂ) :
    (ff ε k).toLinearMap * cmV v = cmV (adPhys ε k v) * (ff ε k).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, cmV, AlgHom.toLinearMap_apply, ff]
  rw [dualV_adPhys hk v, map_contractLeft]

theorem ff_physFock (k : Matrix (Fin n) (Fin n) ℂ) {x : Fock n} (hx : x ∈ physFock ε) :
    ff ε k x ∈ physFock ε := by
  simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i a hia
  have hproj : (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) (i, a)) ∘ₗ adPhys ε k =
      LinearMap.proj (i, a) := by
    refine LinearMap.ext fun u => ?_
    have hp : ¬ IsPhys ε (i, a) := hia
    simp [adPhys, Matrix.mulVec, dotProduct, adMat, hp]
  have h := map_contractLeft (adPhys ε k) (LinearMap.proj (i, a)) x
  rw [hproj] at h
  simp only [cmFock, ff] at hx ⊢
  rw [← h, hx i a hia, map_zero]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.MemHighestWeightSubIff
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

theorem gc_coord_num (x : Fin n × Fin n) (s : Finset (Fin (n * n))) :
    (fockBasis n).coord s ∘ₗ (cpFock x.1 x.2 ∘ₗ cmFock x.1 x.2) =
      (if finProdFinEquiv x ∈ s then (1 : ℂ) else 0) • (fockBasis n).coord s := by
  refine (fockBasis n).ext fun t => ?_
  simp only [LinearMap.comp_apply, lf_num_basis, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  by_cases h : t = s
  · subst h
    split_ifs <;> simp
  · split_ifs <;> simp [Module.Basis.repr_self, h]

theorem gc_support_phys {ε : Fin n → Bool} {f : Fock n} (hf : f ∈ physFock ε) {s : Finset (Fin (n * n))}
    (hs : (fockBasis n).coord s f ≠ 0) : s ⊆ lfPhysModes ε := by
  intro m hm
  by_contra hnot
  obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
  have hx : ¬ (ε x.1 = true ∧ ε x.2 = false) := fun h => hnot ((lf_mem_phys ε x.1 x.2).2 h)
  have h0 : cmFock x.1 x.2 f = 0 := by
    simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hf
    exact hf x.1 x.2 hx
  have h := LinearMap.congr_fun (gc_coord_num x s) f
  simp only [LinearMap.comp_apply, h0, map_zero, if_pos hm, one_smul] at h
  exact hs h.symm

def gcPh (ε : Fin n → Bool) (s : Finset (Fin (n * n))) : Finset (Fin n × Fin n) :=
  (s \ (lowerWedgeAlt ε).1).image finProdFinEquiv.symm ∪
    ((lowerWedgeAlt ε).1 \ s).image fun k => ((finProdFinEquiv.symm k).2, (finProdFinEquiv.symm k).1)

theorem gc_disj (ε : Fin n → Bool) {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    Disjoint ((s \ (lowerWedgeAlt ε).1).image finProdFinEquiv.symm)
      (((lowerWedgeAlt ε).1 \ s).image fun k => ((finProdFinEquiv.symm k).2, (finProdFinEquiv.symm k).1)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx1
  obtain ⟨k', hk', he⟩ := Finset.mem_image.1 hx2
  have hp := hs (Finset.mem_sdiff.1 hk).1
  have hp' := (lowerWedgeAlt ε).2 (Finset.mem_sdiff.1 hk').1
  simp only [lfPhysModes, mem_filter, mem_univ, true_and] at hp hp'
  have e : (finProdFinEquiv.symm k').2 = (finProdFinEquiv.symm k).1 := congrArg Prod.fst he
  rw [e, hp.1] at hp'
  exact Bool.noConfusion hp'.2

theorem gc_isPosNC (ε : Fin n → Bool) {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    IsPosNC ε (gcPh ε s) := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨hks, hk0⟩ := Finset.mem_sdiff.1 hk
    have hp := hs hks
    obtain ⟨y, rfl⟩ := finProdFinEquiv.surjective k
    rw [mem_lowerWedge_iff] at hk0
    simp only [lfPhysModes, mem_filter, mem_univ, true_and, Equiv.symm_apply_apply] at hp ⊢
    have hne : y.1 ≠ y.2 := fun he => by
      have h1 := hp.1
      rw [he, hp.2] at h1
      exact Bool.noConfusion h1
    refine ⟨lt_of_le_of_ne (not_lt.1 fun h' => hk0 ⟨hp.1, hp.2, h'⟩) hne, ?_⟩
    rw [hp.1, hp.2]
    simp
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨y, rfl⟩ := finProdFinEquiv.surjective k
    have hk0 := (Finset.mem_sdiff.1 hk).1
    rw [mem_lowerWedge_iff] at hk0
    simp only [Equiv.symm_apply_apply]
    refine ⟨hk0.2.2, ?_⟩
    rw [hk0.1, hk0.2.1]
    simp

theorem gc_phSum (ε : Fin n → Bool) {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    phSum (gcPh ε s) = ∑ k ∈ s \ (lowerWedgeAlt ε).1, modeWt ε (finProdFinEquiv.symm k) -
      ∑ k ∈ (lowerWedgeAlt ε).1 \ s, modeWt ε (finProdFinEquiv.symm k) := by
  unfold phSum gcPh
  rw [Finset.sum_union (gc_disj ε hs), Finset.sum_image (fun a _ b _ h => finProdFinEquiv.symm.injective h),
    Finset.sum_image (fun a _ b _ h => finProdFinEquiv.symm.injective
      (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))),
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hp := hs (Finset.mem_sdiff.1 hk).1
    simp only [lfPhysModes, mem_filter, mem_univ, true_and] at hp
    simp only [modeWt, if_pos hp]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hp := (lowerWedgeAlt ε).2 (Finset.mem_sdiff.1 hk).1
    simp only [lfPhysModes, mem_filter, mem_univ, true_and] at hp
    simp only [modeWt, if_pos hp, root, neg_sub]

theorem fockWeight_wedge_lowerModes (ε : Fin n → Bool) : fockWt ε (lowerWedgeAlt ε).1 = rhoHol ε - rhoN ε :=
  (coord_wt_eq ε (lowerWedge_weight ε) (by simp)).symm

theorem gc_wt_eq (ε : Fin n → Bool) {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    fockWt ε s = rhoHol ε - rhoN ε + phSum (gcPh ε s) := by
  rw [gc_phSum ε hs, ← fockWeight_wedge_lowerModes]
  unfold fockWt
  have e1 := Finset.sum_sdiff (f := fun k => modeWt ε (finProdFinEquiv.symm k))
    (Finset.inter_subset_left : s ∩ (lowerWedgeAlt ε).1 ⊆ s)
  have e2 := Finset.sum_sdiff (f := fun k => modeWt ε (finProdFinEquiv.symm k))
    (Finset.inter_subset_right : s ∩ (lowerWedgeAlt ε).1 ⊆ (lowerWedgeAlt ε).1)
  have d1 : s \ (s ∩ (lowerWedgeAlt ε).1) = s \ (lowerWedgeAlt ε).1 := by
    ext; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have d2 : (lowerWedgeAlt ε).1 \ (s ∩ (lowerWedgeAlt ε).1) = (lowerWedgeAlt ε).1 \ s := by
    ext; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  rw [d1] at e1
  rw [d2] at e2
  rw [← e1, ← e2]
  abel

theorem gc_Ph_empty {ε : Fin n → Bool} {s : Finset (Fin (n * n))} (h : gcPh ε s = ∅) : s = (lowerWedgeAlt ε).1 := by
  unfold gcPh at h
  rw [Finset.union_eq_empty, Finset.image_eq_empty, Finset.image_eq_empty, Finset.sdiff_eq_empty_iff_subset,
    Finset.sdiff_eq_empty_iff_subset] at h
  exact Finset.Subset.antisymm h.1 h.2

theorem gc_plus_sum {ε : Fin n → Bool} {s : Finset (Fin (n * n))} (hs : s ⊆ lfPhysModes ε) :
    ∑ a ∈ plusIdx ε, fockWt ε s a = (s.card : ℝ) := by
  unfold fockWt
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hp := hs hk
  obtain ⟨y, rfl⟩ := finProdFinEquiv.surjective k
  have hp' := (lf_mem_phys ε y.1 y.2).1 hp
  simp only [Equiv.symm_apply_apply, modeWt, if_pos hp', root, Pi.sub_apply, Finset.sum_sub_distrib]
  simp [plusIdx, Pi.single_apply, hp'.1, hp'.2]

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

