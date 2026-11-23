module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionPointHeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionPointHeight

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_eval_mConeMap (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    aeval y f = eval (fun _ ↦ (1 : Ω)) (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [mConeMap]

theorem notMem_mCoordIdeal {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : aeval y f ≠ 0) :
    f ∉ mCoordIdeal y := by
  intro h
  rw [mCoordIdeal, RingHom.mem_ker] at h
  exact hf (by rw [aeval_eq_eval_mConeMap, h, map_zero])

theorem coord_ne_zero {y : (Σ k, ι k) → Ω} {p : Σ k, ι k} (hp : (X p : MRing ι) ∉ mCoordIdeal y) :
    y p ≠ 0 := by
  intro h0
  apply hp
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

theorem powLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m : ℕ) (z : (Σ k, ι k) → ℂ) :
    (IndefiniteRowSideFullHecke.HeightsSet.powLine A m).h z = A.h z ^ m := by
  induction m with
  | zero => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, IndefiniteRowSideFullHecke.HeightsSet.constLine]
  | succ m ih => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ih, pow_succ]

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (e : K → ℕ) :
    aeval y (IndefiniteRowSideFullHecke.HeightsSet.chartMon c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [IndefiniteRowSideFullHecke.HeightsSet.chartMon, map_prod, map_pow]

theorem vertR_le {W : Ideal (MRing ι)} {G H : MRing ι}
    (h : ∀ V ∈ divSupp W H, V ∈ divSupp W G ∧
      multAt (W ⊔ Ideal.span {H}) V ≤ multAt (W ⊔ Ideal.span {G}) V) :
    vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) H ≤ vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) G := by
  classical
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W H),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W G)]
  have hsub : (divSupp_finite W H).toFinset ⊆ (divSupp_finite W G).toFinset := fun V hV ↦ by
    rw [Set.Finite.mem_toFinset] at hV ⊢
    exact (h V hV).1
  have hc : ∀ V : Ideal (MRing ι), 0 ≤ (if IsHorizontal V then (0 : ℝ) else
      (geoNum 0 V (fun j ↦ ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).a) : ℝ) * Real.log (charOf V)) := by
    intro V
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by exact_mod_cast IndefiniteRowSideFullHecke.HeightsSet.geoNum_zero_nonneg V _)
        (Real.log_natCast_nonneg _)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun V _ _ ↦
    mul_nonneg (Nat.cast_nonneg _) (hc V))
  refine Finset.sum_le_sum fun V hV ↦ ?_
  rw [Set.Finite.mem_toFinset] at hV
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (h V hV).2) (hc V)

end SmallSectionPointHeight


open SmallSectionPointHeight in
theorem SmallSectionPointHeight.proof (hOrd : SectionOrderAtPoint.Statement) :
    SmallSectionPointHeight.Statement := by
  intro K _ ι _ Ω _ y D A τ s II hII hP hbir hA hτ hs hs0 hsmall
  classical

  choose c hc using hP.2.1.2.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦ coord_ne_zero (hc k)

  set ap : K → ℕ := fun k ↦ ((τ : ℤ) * A.a k).toNat with hap
  set an : K → ℕ := fun k ↦ (-((τ : ℤ) * A.a k)).toNat with han
  have hpn : ∀ k, (ap k : ℤ) = an k + τ * A.a k := fun k ↦ by
    have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
    simp only [hap, han]
    linarith
  obtain ⟨d, g0, h0, hg0, hh0, hh0y, hgh0⟩ := hbir (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k)))
  set G := g0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c ap with hGdef
  set H := h0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c an with hHdef
  have hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G (d + ap) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hg0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c ap)
  have hH : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog H (d + an) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hh0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c an)
  have hdeg : ∀ k, ((d + ap) k : ℤ) = (d + an) k + τ * A.a k := fun k ↦ by
    simp only [Pi.add_apply, Nat.cast_add, hpn k]
    ring
  have hGH : aeval y G = s * aeval y H := by
    have hprod : ∀ k, y ⟨k, c k⟩ ^ ap k = y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) * y ⟨k, c k⟩ ^ an k := fun k ↦ by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hpn k, add_comm]
    have h1 : (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun k _ ↦ by rw [← zpow_add₀ (hyc k), neg_add_cancel, zpow_zero]
    rw [hGdef, hHdef, map_mul, map_mul, aeval_chartMon, aeval_chartMon, hgh0,
      Finset.prod_congr rfl fun k _ ↦ hprod k, Finset.prod_mul_distrib]
    linear_combination (s * aeval y h0 * ∏ k, y ⟨k, c k⟩ ^ an k) * h1
  have hHy : aeval y H ≠ 0 := by
    rw [hHdef, map_mul, aeval_chartMon]
    exact mul_ne_zero hh0y (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc k))
  have hGy : aeval y G ≠ 0 := by
    rw [hGH]
    exact mul_ne_zero hs0 hHy
  refine ⟨G * H, ⟨_, IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hG hH⟩,
    notMem_mCoordIdeal (by rw [map_mul]; exact mul_ne_zero hGy hHy), ?_⟩
  intro W hW hPW hfW
  have hGW : G ∉ W := fun h ↦ hfW (W.mul_mem_right H h)
  have hHW : H ∉ W := fun h ↦ hfW (W.mul_mem_left G h)

  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set E := IndefiniteRowSideFullHecke.HeightsSet.powLine A τ with hEdef
  have hE : IsSmoothHerm E := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_powLine hA τ
  set B := HermLine.sqMetric (ι := ι) (d + an) with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric _
  have hEB : IsSmoothHerm (E.tensor B) := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hE hB
  have hEBa : ∀ k, (E.tensor B).a k = ((d + ap) k : ℕ) := fun k ↦ by
    show E.a k + B.a k = _
    rw [hEdef, IndefiniteRowSideFullHecke.HeightsSet.powLine_a, hdeg k]
    show _ + ((d + an) k : ℤ) = _
    ring
  have hsecG : IsSectionOn W (E.tensor B) G := ⟨_, hEBa, hG, hGW⟩
  have hsecH : IsSectionOn W B H := ⟨_, fun k ↦ rfl, hH, hHW⟩
  have hRG := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hEB hEBa hG hGW
  have hRH := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hB (fun k ↦ rfl) hH hHW
  have hadd := IndefiniteRowSideFullHecke.HeightsSet.inter_tensor (II K ι) hI hW hE hB
  have hpow := IndefiniteRowSideFullHecke.HeightsSet.inter_powLine (II K ι) hI hW hA τ
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecG] at hRG
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecH] at hRH

  have hvert := vertR_le (hOrd K ι Ω y A.a τ s W G H (d + ap) (d + an) hW hPW hs hG hH hdeg hGH hGW hHW)

  have harch : arInt W G (E.tensor B) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) ≤
      arInt W H B (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := by
    unfold arInt
    rw [Inter.ptsIntegral_add_of_dimOne fibreFinite hW _ (g₁ := logNorm B H)
      (g₂ := fun z ↦ logNorm (E.tensor B) G z - logNorm B H z) fun z _ ↦ by ring]
    refine add_le_of_nonpos_right (IndefiniteRowSideFullHecke.HeightsSet.ptsIntegral_nonpos W _ fun z hz ↦ ?_)
    show logNorm (E.tensor B) G z - logNorm B H z ≤ 0
    have hGz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecG hz)
    have hHz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecH hz)
    have hAz := A.pos z hz.1
    have hBz := B.pos z hz.1
    have hEz : E.h z = A.h z ^ τ := powLine_h A τ z
    have hEz0 : 0 < E.h z := hEz ▸ pow_pos hAz τ
    have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩
    have hsm := hsmall (d + ap) (d + an) G H z hG hH hdeg hGH hzP
    rw [← hEz] at hsm
    refine sub_nonpos.mpr (Real.log_le_log (div_pos hGz (mul_pos hEz0 hBz)) ?_)
    show _ / (E.h z * B.h z) ≤ _ / B.h z
    rw [div_le_div_iff₀ (mul_pos hEz0 hBz) hBz]
    nlinarith [mul_le_mul_of_nonneg_right hsm hBz.le]

  have hτI : 0 ≤ (τ : ℝ) * II K ι W 1 ![A] := by
    rw [← hpow]
    linarith
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hτI) hτ0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeExtension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

open Module

theorem SublatticeExtension.linearIndependent_real_of_discrete {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
    {ι : Type*} [Fintype ι] (v : ι → V) (hv : ∀ i, v i ∈ L) (hz : LinearIndependent ℤ v) :
    LinearIndependent ℝ v := by
  have hle : Submodule.span ℤ (Set.range v) ≤ L := Submodule.span_le.2 (Set.range_subset_iff.2 hv)
  have hdisc : DiscreteTopology (Submodule.span ℤ (Set.range v)) :=
    DiscreteTopology.of_continuous_injective (f := fun x => (⟨x.1, hle x.2⟩ : L))
      (continuous_subtype_val.subtype_mk _) (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
  rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hdisc]
  exact (finrank_span_eq_card hz).symm

theorem SublatticeExtension.proof : SublatticeExtension.Statement := by
  intro E E' _ _ R R' φ φ' _ _ _ ψ hφ hφ' hψ hnorm
  classical
  have mem : ∀ {G : Type} [AddCommGroup G] {n : ℕ} (χ : G →+ EuclideanSpace ℝ (Fin n)) (y),
      y ∈ imageLattice χ ↔ ∃ x, χ x = y := fun χ y => by
    rw [imageLattice, ← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe, AddMonoidHom.mem_range]
  let b := Free.chooseBasis ℤ (imageLattice φ')
  let bR := b.ofZLatticeBasis ℝ (imageLattice φ')
  let g : _ → E' := fun i => Classical.choose ((mem φ' _).1 (b i).2)
  have hg : ∀ i, φ' (g i) = b i := fun i => Classical.choose_spec ((mem φ' _).1 (b i).2)
  let Ψ := bR.constr ℝ (fun i => φ (ψ (g i)))
  have hΨb : ∀ i, Ψ (b i) = φ (ψ (g i)) := fun i => by
    rw [← b.ofZLatticeBasis_apply ℝ (imageLattice φ') i]; exact bR.constr_basis ℝ _ i

  have hext : ∀ x, Ψ (φ' x) = φ (ψ x) := by
    intro x
    obtain ⟨c, hc⟩ : ∃ c : _ → ℤ, x = ∑ i, c i • g i := by
      refine ⟨b.repr ⟨φ' x, (mem φ' _).2 ⟨x, rfl⟩⟩, hφ' ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simp only [map_zsmul, hg]
      have hs := congrArg Subtype.val (b.sum_repr ⟨φ' x, (mem φ' _).2 ⟨x, rfl⟩⟩)
      rw [Submodule.coe_sum] at hs; simp only [Submodule.coe_smul] at hs
      exact hs.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc]; simp only [map_sum, map_zsmul, hg, hΨb]

  have hlat : ∀ y ∈ imageLattice φ', ‖Ψ y‖ ≤ ‖y‖ := by
    intro y hy; obtain ⟨x, rfl⟩ := (mem φ' y).1 hy; rw [hext]; exact hnorm x
  let f : (_ → ℚ) → EuclideanSpace ℝ (Fin R') := fun q => bR.equivFun.symm (fun i => (q i : ℝ))
  have hf : DenseRange f :=
    (bR.equivFun.symm.surjective.denseRange).comp (DenseRange.piMap fun _ => Rat.denseRange_cast)
      (LinearMap.continuous_of_finiteDimensional bR.equivFun.symm.toLinearMap)
  have hrat : ∀ q, ‖Ψ (f q)‖ ≤ ‖f q‖ := by
    intro q
    have hNpos : (0 : ℝ) < (∏ i, (q i).den : ℕ) := by
      exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
    have hz : ∀ i, ∃ z : ℤ, ((∏ i, (q i).den : ℕ) : ℝ) * (q i : ℝ) = z := by
      intro i
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
      refine ⟨k * (q i).num, ?_⟩
      have : ((∏ i, (q i).den : ℕ) : ℚ) * q i = k * (q i).num := by
        rw [hk]; push_cast; rw [mul_comm ((q i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
      exact_mod_cast this
    choose z hz using hz
    have hmem : ((∏ i, (q i).den : ℕ) : ℝ) • f q ∈ imageLattice φ' := by
      have : ((∏ i, (q i).den : ℕ) : ℝ) • f q = ∑ i, z i • (b i : EuclideanSpace ℝ (Fin R')) := by
        simp only [f, Basis.equivFun_symm_apply, Finset.smul_sum, smul_smul, hz,
          ← Int.cast_smul_eq_zsmul ℝ, bR, Basis.ofZLatticeBasis_apply]
      rw [this]; exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
    have h := hlat _ hmem
    rw [map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hNpos.le] at h
    exact le_of_mul_le_mul_left h hNpos
  have hall : ∀ y, ‖Ψ y‖ ≤ ‖y‖ := by
    have hS : IsClosed {y | ‖Ψ y‖ ≤ ‖y‖} :=
      isClosed_le (continuous_norm.comp (LinearMap.continuous_of_finiteDimensional Ψ)) continuous_norm
    have hd : Dense {y | ‖Ψ y‖ ≤ ‖y‖} := Dense.mono (Set.range_subset_iff.2 fun q => hrat q) hf
    have h := hd.closure_eq
    rw [hS.closure_eq] at h
    exact Set.eq_univ_iff_forall.1 h

  have hvZ : LinearIndependent ℤ (fun i => φ (ψ (g i))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : ∑ i, c i • g i = 0 := by
      apply hψ; apply hφ; simpa [map_sum, map_zsmul] using hc
    have h1 : ∑ i, c i • b i = 0 := by
      apply Subtype.ext
      have := congrArg φ' h0
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_zsmul, hg] using this
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c h1
  have hvR := SublatticeExtension.linearIndependent_real_of_discrete (imageLattice φ) _
    (fun i => (mem φ _).2 ⟨ψ (g i), rfl⟩) hvZ
  refine ⟨Ψ, hext, hall, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have hc := Fintype.linearIndependent_iff.1 hvR (bR.equivFun y)
    (by rw [← bR.constr_apply_fintype ℝ]; exact hy)
  exact bR.equivFun.injective (by ext i; simp [hc i])

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopPullFS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace TopPullFS

variable {κ : Type} [Fintype κ] {D : ℕ}

theorem linApply_projMat (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) (k : Fin (D + 1)) :
    linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z ⟨(), k⟩ = z (e k) := by
  classical
  simp only [linApply, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem isSmoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  refine hm.mono fun z hz => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 => hi (congrFun h0 _)

theorem fs_linApply (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    (HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))).h
        (linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z) =
      Real.sqrt (∑ k, ‖z (e k)‖ ^ 2) := by
  simp only [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_sigma, Fintype.sum_unique]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [linApply_projMat]

end TopPullFS


open TopPullFS in
theorem TopPullFS.proof (hCM : ChangeOfModelStatement) (hBP : ProjFrameBasePtFree.Statement)
    (hIm : ProjFrameImage.Statement) (hDeg : ProjFrameGraphDeg.Statement) : TopPullFS.Statement := by
  intro D Ω _ _ κ _ I x m e hI hP hm hfr hFS
  obtain ⟨G, J, hJ, hJe⟩ := hDeg D Ω κ x e hP hfr
  have himg := hIm D Ω κ x e hfr
  have hSmoothFS : IsSmoothHerm (HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))) := by
    apply isSmoothHerm_ofCone
    intro z hz
    change ContDiffWithinAt ℝ _ (fun w : Ix (Fin (D + 1)) → ℂ => ‖WithLp.toLp 2 w‖) _ z
    have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (WithLp.toLp 2 : (Ix (Fin (D + 1)) → ℂ) → _) :=
      PiLp.contDiff_toLp
    have hz' : WithLp.toLp 2 z ≠ 0 := by simpa using hz
    exact (hL.contDiffAt.norm ℂ hz').contDiffWithinAt
  have key := hCM I hI Unit (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x) (D + 1) (projMat e) G J
    (fun _ => HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))) (fun _ => HermLine.ofCone m) hP
    (hBP D Ω κ x e hfr) (by rw [himg]; exact IndefiniteRowSideFullHecke.Inter.isArithVar_bot D) hJ
    (fun _ => hSmoothFS) (fun _ => isSmoothHerm_ofCone hm) (fun _ => rfl)
    (fun _ z hz => by
      rw [fs_linApply]
      exact hFS z ⟨fun h0 => by obtain ⟨i, hi⟩ := hz.1 (); exact hi (congrFun h0 _), hz.2⟩)
  rw [himg, hJe] at key
  simpa [top, hhOf] using key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionAnyDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace TwistIntersectionAnyDegree

theorem proof (hPc : EmbeddingPieces.Statement) (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    TwistIntersectionAnyDegree.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D A B II Λ _ hII hP hbir hA hBa hB hΛ hex hloc
  classical
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  have hC : IsSmoothHerm (A.tensor B) := hA.mul hB
  have hopen : IsOpen {u : (Σ k, ι k) → ℂ | ∀ k, ∃ i, u ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hCloc : ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((A.tensor B).h u) = Real.log (A.h u) + c := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    refine ⟨Real.log (Λ sg), ?_⟩
    filter_upwards [hloc z hz sg hsg, hopen.mem_nhds hz.1] with u hu hu'
    show Real.log (A.h u * B.h u) = _
    rw [hu, Real.log_mul (A.pos u hu').ne' (hΛ sg).ne']
  let L : Finset (Fin (D + 1)) → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun S i => if i ∈ S then A.tensor B else A
  have hLs : ∀ S i, IsSmoothHerm (L S i) := by
    intro S i
    dsimp only [L]
    split_ifs
    exacts [hC, hA]
  have hLpot : ∀ S i, ∀ z ∈ mcPts (mCoordIdeal y), ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, Real.log ((L S i).h u) = Real.log (A.h u) + c := by
    intro S i z hz
    dsimp only [L]
    split_ifs
    · exact hCloc z hz
    · exact ⟨0, Eventually.of_forall fun u => by rw [add_zero]⟩
  have step : ∀ (S : Finset (Fin (D + 1))) (j : Fin (D + 1)), j ∉ S →
      II K ι (mCoordIdeal y) (D + 1) (L (insert j S)) = II K ι (mCoordIdeal y) (D + 1) (L S) +
        -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S j hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := Fin.init (L S ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (insert j S) ∘ σ) = M := by
      funext i
      simp only [hMdef, Fin.init, Function.comp, L, Finset.mem_insert, hne i, false_or]
    have e0 : L S ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L S ∘ σ)
      have hl : (L S ∘ σ) (Fin.last D) = A := by simp [L, hσl, hj]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (insert j S) ∘ σ = Fin.snoc M (A.tensor B) := by
      have h0 := Fin.snoc_init_self (q := L (insert j S) ∘ σ)
      have hl : (L (insert j S) ∘ σ) (Fin.last D) = A.tensor B := by simp [L, hσl]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs S _
    have hint : ptsIntegral (mCoordIdeal y) (pot M) (logNorm B 1) =
        ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) :=
      TwistIntersection.ptsIntegral_add_locConst _ (fun i z hz => hLpot S (σ (Fin.castSucc i)) z hz) _
    rw [← hI.1 _ (D + 1) (L (insert j S)) σ hP (hLs _), ← hI.1 _ (D + 1) (L S) σ hP (hLs S), e0, e1,
      hI.2.1 _ D M A B hP hMs hA hB, TwistIntersection.I_snoc_degZero hI hP hMs hB hBa, hint]
  have hall : ∀ S : Finset (Fin (D + 1)), II K ι (mCoordIdeal y) (D + 1) (L S) =
      II K ι (mCoordIdeal y) (D + 1) (L ∅) +
        S.card * -ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (logNorm B 1) := by
    intro S
    refine Finset.induction_on S (by simp) ?_
    intro j S hj ih
    rw [step S j hj, ih, Finset.card_insert_of_notMem hj]
    push_cast
    ring
  have hL0 : L ∅ = fun _ => A := by
    funext i
    simp [L]
  have hLu : L Finset.univ = fun _ => A.tensor B := by
    funext i
    simp [L]
  have hw : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      logNorm B 1 =ᶠ[𝓝 z] fun _ => (fun sg => -Real.log (Λ sg)) sg := by
    intro z hz sg hsg
    filter_upwards [hloc z hz sg hsg] with u hu
    simp [logNorm, hu, Real.log_inv]
  have hpc := hPc K ι Ω F y D (fun _ => A) (fun sg => -Real.log (Λ sg)) (logNorm B 1) hP hbir
    (fun _ => hA) hex hw
  have hg : ptsIntegral (mCoordIdeal y) (pot fun _ : Fin D => A) (fun _ => 1) =
      (genDeg (mCoordIdeal y) D A.a : ℝ) := by
    rw [hDG K ι (mCoordIdeal y) D (fun _ => A) hP (fun _ => hA)]
    unfold genDeg
    congr
  have := hall Finset.univ
  rw [hL0, hLu, Finset.card_univ, Fintype.card_fin] at this
  rw [this, hpc, hg, Finset.sum_neg_distrib]
  push_cast
  ring

end TwistIntersectionAnyDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

