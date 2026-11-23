module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem cc_hL (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by
  have h0 : constantCoeff h = 0 := by
    have e := WickVanishing.coeff_ev_zero_left h 0
    rw [hc.ax0, Finsupp.embDomain_zero] at e
    rw [← coeff_zero_eq_constantCoeff_apply, ← e, map_zero]
  unfold FB.hL
  rw [WickVanishing.gt_const_ev_eq _ ?_ h, h0]
  intro j
  fin_cases j
  · exact WickVanishing.gp_pt 0
  · exact WickVanishing.gp_comp1 _ _ (fun i => by simp [FB.actK, B.A.const]) (WickVanishing.gp_pt 0)

theorem sc_of (hN1 : ConnectionIntegrality) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : SCSt := by
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hcg w0 hw0 m ι π _ _ _ c s ξh ψ hH hψ h11 h21 h12 P hPint e he f hf
  set x := (m : k) • B.hL k h w0 with hx
  have hx0 : constantCoeff x = 0 := by
    rw [hx, smul_eq_C_mul, map_mul, constantCoeff_C, cc_hL B h hcg w0, mul_zero]
  set E0 := liftX k (FB.expS k x) with hE0def
  set E1 := liftX k (FB.expS k (-x)) with hE1def
  have hE : E0 * E1 = 1 := by
    rw [hE0def, hE1def, ← liftX_mul, ← WickVanishing.gt_expS_add _ _ hx0 (by rw [map_neg, hx0, neg_zero]),
      add_neg_cancel, expS_zero', liftX_eq_rename, map_one]
  have hE0 : constantCoeff E0 = 1 := by rw [hE0def, cc_liftX, cc_expS _ hx0]
  have hgood : ∀ l X, GoodE R E0 X → GoodE R E0 (nabla k B h m (ξh l).1 (ξh l).2 X) := by
    rintro l X ⟨G, hG, rfl⟩
    refine ⟨E1 * nabla k B h m (ξh l).1 (ξh l).2 (E0 * G),
      hN1 R d O k hRQ B h hcg w0 hw0 m (ξh l) (hH l) G hG, ?_⟩
    rw [← mul_assoc, hE, one_mul]
  have hσ : GoodE R E0 (liftX k (FB.expS k x * f)) := ⟨liftX k f, intAA_liftX f hf, liftX_mul _ _⟩
  have haa : ∀ l l', s l = s l' → betaH k (ξh l) (ξh l') = 0 := fun l l' e' => h11 l l' fun hh => hh.2 e'
  have hab : ∀ l l', s l = s l' → betaH k (ξh l) (0, ψ l') = 0 := fun l l' e' => h12 l l' fun hh => hh.2 e'
  have hκ : ∀ l l', kapW m s ξh (fun l => (0, ψ l)) l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false := by
    intro l l' hne
    obtain ⟨hs, hs'⟩ := kapW_supp m s ξh _ l l' hne
    refine ⟨?_, hs, hs'⟩
    by_contra hc
    apply hne
    unfold kapW
    rw [if_pos ⟨hs, hs'⟩, h21 l l' (fun hh => hc hh.1), mul_zero]
  have hκJ : ∀ i j, kapE s (kapW m s ξh (fun l => (0, ψ l))) i j ∈ J := by
    intro i j
    unfold kapE kapW
    split_ifs
    · obtain ⟨u, φ, hu⟩ := hH ((sideE s).symm (Sum.inr j))
      rw [hu]
      unfold betaH
      simp only [Pi.zero_apply, mul_zero, zero_sub]
      rw [← nsmul_eq_mul]
      refine J.toAddSubmonoid.nsmul_mem (J.sum_mem fun t _ => J.neg_mem ?_) m
      rw [mul_comm, ← Algebra.smul_def]
      exact J.smul_mem _ (hψ _ t)
    · exact J.zero_mem
  obtain ⟨P0, hP0⟩ : P ∈ Set.range (MvPolynomial.map (algebraMap R k)) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun a ha => ?_
    obtain ⟨n', _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    exact RingHom.mem_range.mp (hPint n')
  have ordNabla_wick (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type}
      [Fintype ι] (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (hb0 : ∀ l, (ξb l).1 = 0)
      (haa : ∀ l l', s l = s l' → betaH k (ξa l) (ξa l') = 0)
      (hab : ∀ l l', s l = s l' → betaH k (ξa l) (ξb l') = 0) (P : MvPolynomial ι k) (f : PS k 1 d) :
      ordNabla k B h m s (fun l => ξa l + ξb l) P (liftX k f) =
        ∑ n ∈ Finset.range ((MvPolynomial.rename (sideE s) P).totalDegree + 1),
          PI.WickFormula.ordEval (opL B h m s ξa) (opR B h m s ξa)
            (((n.factorial : ℚ)⁻¹) • MvPolynomial.rename (sideE s) ((secondOrder k (kapW m s ξa ξb))^[n] P))
            (liftX k f) := by
    have hbb : ∀ l l', betaH k (ξb l) (ξb l') = 0 := fun l l' => by
      rw [show ξb l = (0, (ξb l).2) from Prod.ext (hb0 l) rfl, show ξb l' = (0, (ξb l').2) from Prod.ext (hb0 l') rfl]
      exact betaH_zero_zero _ _
    have hba : ∀ l l', s l = s l' → betaH k (ξb l) (ξa l') = 0 := fun l l' e => by
      rw [betaH_antisymm, hab l' l e.symm, neg_zero]
    have cA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (haa l l' e)
    have cAB : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (hab l l' e)
    have cBA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
      fun l l' e => nablaL_comm hN2 B h m _ _ (hba l l' e)
    have cB : ∀ l l', Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
      fun l l' => nablaL_comm hN2 B h m _ _ (hbb l l')
    have hsum : ∀ l, nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2 =
        nablaL B h m (ξa l).1 (ξa l).2 + nablaL B h m (ξb l).1 (ξb l).2 := fun l =>
      nablaL_add B h m _ _ _ _
    have cAll : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2)
        (nablaL B h m (ξa l' + ξb l').1 (ξa l' + ξb l').2) := fun l l' e => by
      rw [hsum, hsum]
      exact ((cA l l' e).add_right (cAB l l' e)).add_left ((cBA l l' e).add_right (cB l l'))
    rw [ordNabla_eq B h m s (fun l => ξa l + ξb l) cAll P (liftX k f)]
    have hL : opL B h m s (fun l => ξa l + ξb l) = opL B h m s ξa + opL B h m s ξb := funext fun i => hsum _
    have hR : opR B h m s (fun l => ξa l + ξb l) = opR B h m s ξa + opR B h m s ξb := funext fun j => hsum _
    have key := _root_.wick_formula k (Module.End k (AA k d)) (AA k d) _ _ (opL B h m s ξa) (opL B h m s ξb)
      (opR B h m s ξa) (opR B h m s ξb) (kapE s (kapW m s ξa ξb)) (liftX k f)
      (fun i i' => ⟨cA _ _ (by rw [side_inl s i, side_inl s i']), cAB _ _ (by rw [side_inl s i, side_inl s i']),
        cB _ _⟩)
      (fun j j' => ⟨cA _ _ (by rw [side_inr s j, side_inr s j']), cAB _ _ (by rw [side_inr s j, side_inr s j']),
        cB _ _⟩)
      (fun i j => cB _ _)
      (fun i j => by
        rw [nablaL_bracket hN2 B h m]
        unfold kapE kapW
        rw [if_pos ⟨side_inl s i, side_inr s j⟩])
      (fun i => by
        rw [Module.End.smul_def, opL, hb0]
        exact hN3 R d O k B h m _ f)
      (fun j => by
        rw [Module.End.smul_def, opR, hb0]
        exact hN3 R d O k B h m _ f)
      (MvPolynomial.rename (sideE s) P)
    rw [hL, hR, ← Module.End.smul_def, key]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.End.smul_def, delta_pow_rename s _ (kapW_supp m s ξa ξb)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ordNabla_wick hN2 hN3 B h m s ξh (fun l => (0, ψ l)) (fun _ => rfl) haa hab P (FB.expS k x * f), map_sum]
  refine Submodule.sum_mem _ fun n _ => ?_
  refine cc_ordEval_mem J e E0 hE0 (opL B h m s ξh) (opR B h m s ξh) (fun i => hgood _) (fun j => hgood _) _ hσ _
    fun mo => ?_
  by_cases hne : n ≤ e
  · refine pow_le_pow_right' (Submodule.one_le.mpr hJ1) hne ?_
    have key := (_root_.divided_power_integrality R k _ _ J _ hκJ (MvPolynomial.rename (sideE s) P0) n).1 mo
    rw [← delta_pow_rename s _ (kapW_supp m s ξh _) n P, ← hP0, ← MvPolynomial.map_rename]
    exact key
  · rw [secondOrder_iterate_eq_zero c s _ hκ P e he n (by omega), map_zero, smul_zero, MvPolynomial.coeff_zero]
    exact Submodule.zero_mem _

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
