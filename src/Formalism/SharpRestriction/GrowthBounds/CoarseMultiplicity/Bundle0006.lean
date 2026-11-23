module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.OtherStart

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FactAbs
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem fact_abs {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type)
    [Fintype σ] [DecidableEq σ] (odd : σ → Prop) [DecidablePred odd] (t ρ L : σ → ℕ)
    (hodd : ∀ v, odd v → L v = p ^ (t v + 1) ∧ ρ v < L v) (hend : ∀ v, ¬ odd v → L v = 1 ∧ ρ v = 0) (c : ℕ) :
    ∃ (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → ℚ),
      (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * c ∧ (∀ v ∈ ν.support, odd v) ∧ PadicGe p (q ν) 0) ∧
      ∀ μ : σ →₀ ℕ, ∃ h : ℚ, PadicGe p h c ∧
        (∏ v, ((ρ v + L v * μ v).factorial : ℚ)) *
            (∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ)) =
          (∏ v, ((ρ v).factorial : ℚ) * ((μ v).factorial : ℚ) * ((L v).factorial : ℚ) ^ (μ v)) * (1 + h) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := h52 p hp h5
  set t' : σ → ℕ := fun v => if odd v then t v else 0 with ht'
  set ρ' : σ → ℕ := fun v => if odd v then ρ v else 0 with hρ'
  have hlt : ∀ k, ρ' k < p ^ (t' k + 1) := by
    intro k
    by_cases hk : odd k
    · simp only [hρ', ht', if_pos hk]
      rw [← (hodd k hk).1]; exact (hodd k hk).2
    · simp only [hρ', ht', if_neg hk]
      exact pow_pos hp.pos _
  obtain ⟨hunit, -, hop⟩ := h2 σ t' ρ' hlt
  obtain ⟨T, q, hT, hq⟩ := hop true c
  let E : (σ → ℕ) → (σ →₀ ℕ) := fun j => Finsupp.equivFunOnFinite.symm j
  have hE : Function.Injective E := Finsupp.equivFunOnFinite.symm.injective
  have hEa : ∀ j v, E j v = j v := fun j v => rfl
  refine ⟨(T.filter fun j => ∀ v, ¬ odd v → j v = 0).image E, fun ν => q ν, ?_, ?_⟩
  · intro ν hν
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hν
    obtain ⟨hjT, hj0⟩ := Finset.mem_filter.1 hj
    refine ⟨?_, ?_, ?_⟩
    · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact (hT j hjT).1
    · intro v hv
      by_contra hno
      exact (Finsupp.mem_support_iff.1 hv) (hj0 v hno)
    · exact (hT j hjT).2
  · intro μ
    set e' : σ → ℕ := fun v => if odd v then μ v else 0 with he'
    set U : ℚ := ∏ k, cUnit (p ^ (t' k + 1)) (e' k) * dUnit (p ^ (t' k + 1)) (e' k) (ρ' k) with hU
    set A : ℚ := ∏ k, (((ρ' k + p ^ (t' k + 1) * e' k).factorial : ℕ) : ℚ) with hA
    set B : ℚ := ∏ k, ((ρ' k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (t' k + 1)).factorial : ℚ) ^ (e' k) with hB
    set g : ℚ := ∑ j ∈ T, q j * ∏ k, ((e' k).choose (j k) : ℚ) with hg
    have hU0 : U ≠ 0 := (hunit e').1
    have hUv : padicValRat p U = 0 := (hunit e').2
    have hAB : A = B * U := by
      rw [hA, hB, hU, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [h1 (t' k) (ρ' k) (e' k) (hlt k)]
      ring
    have hB0 : B ≠ 0 := by
      rw [hB]
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      have a1 : ((ρ' k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have a2 : ((e' k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have a3 : ((p ^ (t' k + 1)).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      exact mul_ne_zero (mul_ne_zero a1 a2) (pow_ne_zero _ a3)
    have hq' : PadicGe p (U⁻¹ - g) c := by
      have := hq e'
      simp only [if_true] at this
      have e : A / B = U := by rw [hAB]; field_simp
      rw [← hA, ← hB, e] at this
      exact this
    have hgs : (∑ ν ∈ (T.filter fun j => ∀ v, ¬ odd v → j v = 0).image E,
        q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : ℚ)) = g := by
      rw [Finset.sum_image fun a _ b _ h => hE h, hg, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ∀ v, ¬ odd v → j v = 0
      · rw [if_pos hj, Finsupp.prod_fintype _ _ (fun _ => Nat.choose_zero_right _)]
        push_cast
        congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases hk : odd k
        · simp only [he', if_pos hk, hEa]
        · simp only [he', if_neg hk, hEa, hj k hk, Nat.choose_zero_right]
      · rw [if_neg hj]
        push_neg at hj
        obtain ⟨v, hv, hjv⟩ := hj
        have : (∏ k, ((e' k).choose (j k) : ℚ)) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
          simp only [he', if_neg hv]
          rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hjv)]
          simp
        rw [this, mul_zero]
    refine ⟨(-U) * (U⁻¹ - g), ?_, ?_⟩
    · have hU' : PadicGe p (-U) 0 := padicGe_neg (Or.inr (by rw [hUv]; simp))
      have := padicGe_mul hU' hq'
      simpa using this
    · rw [hgs]
      set M : ℚ := ∏ v, (if odd v then (1 : ℚ) else ((μ v).factorial : ℚ)) with hM
      have l1 : (∏ v, ((ρ v + L v * μ v).factorial : ℚ)) = A * M := by
        rw [hA, hM, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : odd v
        · simp only [hρ', ht', he', if_pos hv, (hodd v hv).1, mul_one]
        · simp only [hρ', ht', he', if_neg hv, (hend v hv).1, (hend v hv).2]
          simp
      have l2 : (∏ v, ((ρ v).factorial : ℚ) * ((μ v).factorial : ℚ) * ((L v).factorial : ℚ) ^ (μ v)) = B * M := by
        rw [hB, hM, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        by_cases hv : odd v
        · simp only [hρ', ht', he', if_pos hv, (hodd v hv).1, mul_one]
        · simp only [hρ', ht', he', if_neg hv, (hend v hv).1, (hend v hv).2]
          simp
      rw [l1, l2, hAB]
      field_simp
      ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TestFlat
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq tens_Le edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF edgeBasis dual_edge latDual_colSpan)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jO : W →+* O} {w : O} {m : ℕ} {TT : Finset (Fin n')} {aT bT : Fin n' → ℕ}

variable (thK : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT))

theorem Xi_CC (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) (hhDegs TT aT bT)) (e : Edge W Qq (m + 1)) (he : IsEdge p n' 1 e)
    (t c : ℕ) (v : ↥(VHH (m := m) Kf TT aT bT)) (hv : v ∈ CCe p ι σ w TT aT bT t c e.dual) :
    XiH thK (zK Kf p κ TT aT bT) v ∈ CCe' p ι σ w TT aT bT t c e := by
  have hs1 : ∀ M : Submodule O (VHH (m := m) Kf TT aT bT), scale (1 : Kf) M = M := by
    intro M
    ext x
    simp [scale, Submodule.mem_map]
  have hs1' : ∀ M : Submodule O (Module.Dual Kf (VHH (m := m) Kf TT aT bT)), scale (1 : Kf) M = M := by
    intro M
    ext x
    simp [scale, Submodule.mem_map]
  simp only [CCe, CCe', Submodule.mem_inf, Submodule.mem_iInf] at hv ⊢
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  obtain ⟨g, hg⟩ := edgeBasis hS m 1 e he
  have hpQ : ((p : ℕ) : Qq) ≠ 0 := by
    haveI := hS.frac_alt
    intro h0
    apply hS.p_unif.ne_zero
    apply IsFractionRing.injective W Qq
    rw [map_natCast, h0, map_zero]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hℓu : IsUnit (g * Matrix.diagonal fun c : Fin (m + 1) =>
        if c.val < 1 then ((p : Qq))⁻¹ else 1).det := by
      rw [Matrix.det_mul, Matrix.det_diagonal]
      refine hg.1.mul (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun c _ => ?_))
      split_ifs
      · exact inv_ne_zero hpQ
      · exact one_ne_zero
    have htgt := hg.2.2
    have hsrc : e.dual.src = colSpan W ((g * Matrix.diagonal fun c : Fin (m + 1) =>
        if c.val < 1 then ((p : Qq))⁻¹ else 1)⁻¹).transpose := by
      show latDual e.tgt = _
      rw [htgt, latDual_colSpan _ hℓu]
    rw [hsrc] at hv1
    have h1 := FD_HL thK hS hm hthK κ hMD _ hℓu _ v hv1
    rwa [← htgt] at h1
  · have h1 := FD_edge thK hS hm hthK κ hMD 1 e g hg 1 v (by rw [hs1]; exact hv2)
    rwa [hs1'] at h1
  · intro e'' he''
    have hd := dual_edge hS m 1 e'' he''.1
    have hsrc : e''.dual.src = e.dual.src := by
      show latDual e''.tgt = latDual e.tgt
      rw [he''.2.1]
    have hne : e''.dual ≠ e.dual := fun heq =>
      he''.2.2 (by rw [← hd.2, heq, (dual_edge hS m 1 e he).2])
    have hv3' := hv3 e''.dual ⟨hd.1, hsrc, hne⟩
    obtain ⟨b, hb⟩ := edgeBasis hS m 1 e'' he''.1
    exact FD_edge thK hS hm hthK κ hMD 1 e'' b hb _ v hv3'

theorem kapR_zTen (hS : HidaSetting p n' W Qq O Kf ι σ jO w) :
    kapR hS (zTen (KK O) p m TT aT bT) = zK Kf p (kapZ p m TT aT bT) TT aT bT := by
  simp [zTen, zK, map_div₀, map_pow, map_natCast, map_prod, Nat.cast_prod]

theorem pairing (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsUnit b.det)
    (hb' : IsUnit ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq)).det)
    (Θ Θ' : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT))
    (hΘ : ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val b) F.1)
    (hΘ' : ∀ F, ((Θ' F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq))) F.1)
    (F F' : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (y : O) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    zTen (KK O) p m TT aT bT *
        fock (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
            (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)))
          (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
            (F' : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O))) = algebraMap O (KK O) y →
    beHH (m := m) p TT aT bT (Θ F) (XiH thK (zK Kf p (kapZ p m TT aT bT) TT aT bT) (Θ' F')) = algebraMap O Kf y := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  intro hy
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hF0 := (pol_iff hS _ _ _).1 F.2
  have hF0' := (pol_iff hS _ _ _).1 F'.2
  let P : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) :=
    ⟨Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val b)⁻¹) (map (kapR hS) F.1), Lin_Pol _ _ hF0⟩
  let Q : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) :=
    ⟨Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq)))⁻¹)
      (map (kapR hS) F'.1), Lin_Pol _ _ hF0'⟩
  have hP : Θ F = thK P := Subtype.ext (by rw [hΘ, hthK]; rfl)
  have hQ : Θ' F' = thK Q := Subtype.ext (by rw [hΘ', hthK]; rfl)
  have hk := congrArg (kapR hS) hy
  rw [map_mul, kapR_alg, kapR_zTen, fock_eq_fockR, ← fockR_map,
    lift_one hS φ hφ m TT aT bT b hb F.1 F.2, lift_one hS φ hφ m TT aT bT _ hb' F'.1 F'.2,
    tsact_smul_left, tsact_smul_right] at hk
  have hdual : ∀ x : TT × Bool,
      Aa x.2 (la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq)) * lb_D (m + 1) 1 c) *
        (Aa x.2 (la_tw ι σ x.1.val.val b * lb_D (m + 1) 1 c)).transpose = 1 := by
    intro x
    rw [hc, dualM hS x.1.val.val 1 b hb]
    exact Aa_dual' x.2 _ (by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb).mul (lb_D_det _ _ _ hw))
  rw [fockR_Lin_dual _ _ hdual] at hk
  unfold beHH
  rw [hP, hQ, map_smul, XiH_apply, smul_eq_mul, ← hk]
  have hpA : (p : Kf) ^ AHH TT aT bT = c ^ Avec (vecH TT) (hhDegs TT aT bT) * c ^ Avec (vecH TT) (hhDegs TT aT bT) := by
    rw [← Avec_eq (m := m), zpow_natCast, p_eq hS]
    ring
  rw [hpA]
  show _ = _ * (_ * (_ * fockR P.1 Q.1))
  ring

end

end Formalism.MainNotions.ColumnSystems.Pf.TF

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility TF
open Formalism.L2.G.Model (dE dual_edgeBasis pQ_ne edgeBasis dual_edge Th0)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem eig_one {R : Type} [CommSemiring R] {σ : Type} (ν μ : σ →₀ ℕ) (u : MvPolynomial σ R) :
    AddMonoidAlgebra.coeff (monomial ν (1 : R) * divDer ν u) μ = AddMonoidAlgebra.coeff u μ * ((ν.prod fun k i => (μ k).choose i : ℕ) : R) := by
  classical
  unfold divDer
  rw [Finset.mul_sum, coeff_sum]
  have key : ∀ m ∈ u.support, AddMonoidAlgebra.coeff (monomial ν (1 : R) * (if ν ≤ m then
      monomial (m - ν) (AddMonoidAlgebra.coeff u m * ((ν.prod fun k i => (m k).choose i : ℕ) : R)) else 0)) μ =
      if m = μ then AddMonoidAlgebra.coeff u μ * ((ν.prod fun k i => (μ k).choose i : ℕ) : R) else 0 := by
    intro m _
    by_cases h1 : ν ≤ m
    · rw [ite_eq_left h1, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le h1, coeff_monomial]
      by_cases h2 : m = μ
      · subst h2; simp
      · rw [ite_eq_right h2, ite_eq_right h2]
    · rw [ite_eq_right h1, mul_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      by_cases h2 : m = μ
      · subst h2
        rw [ite_eq_left rfl]
        obtain ⟨k, hk⟩ : ∃ k, ¬ ν k ≤ m k := by
          by_contra hcon
          push Not at hcon
          exact h1 hcon
        have hk' : m k < ν k := not_le.1 hk
        have h0 : (ν.prod fun k i => (m k).choose i) = 0 :=
          Finset.prod_eq_zero (i := k) (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hk')
        rw [h0]; simp
      · rw [ite_eq_right h2]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, zero_mul]

theorem eigAt : EigAt := by
  intro O _ _ σ T q u μ
  unfold gOp gEv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coeff_smul, eig_one, Algebra.smul_def, map_mul, map_natCast]
  ring

theorem fock_monoMap {K : Type} [Field K] {σ τ : Type} (f : MvPolynomial σ K →ₗ[K] MvPolynomial τ K)
    (ε : (σ →₀ ℕ) → (τ →₀ ℕ)) (hε : Function.Injective ε) (hf : ∀ μ c, f (monomial μ c) = monomial (ε μ) c)
    (u u' : MvPolynomial σ K) :
    fock (f u) (f u') = ∑ μ ∈ u.support, u.coeff μ * u'.coeff μ * (expFact (ε μ) : K) := by
  classical
  have hexp : ∀ v : MvPolynomial σ K, f v = ∑ μ ∈ v.support, monomial (ε μ) (v.coeff μ) := by
    intro v
    conv_lhs => rw [← v.support_sum_monomial_coeff]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => hf μ _
  have hco : ∀ (v : MvPolynomial σ K) (μ : σ →₀ ℕ), AddMonoidAlgebra.coeff (f v) (ε μ) = AddMonoidAlgebra.coeff v μ := by
    intro v μ
    rw [hexp, coeff_sum]
    have : ∀ μ' ∈ v.support, AddMonoidAlgebra.coeff (monomial (ε μ') (v.coeff μ')) (ε μ) = if μ' = μ then v.coeff μ else 0 := by
      intro μ' _
      rw [coeff_monomial]
      by_cases h : μ' = μ
      · subst h; simp
      · rw [ite_eq_right h, ite_eq_right fun h' => h (hε h')]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (notMem_support_iff.1 h).symm
  have hsupp : (f u).support ⊆ u.support.image ε := by
    rw [hexp]
    refine (support_sum).trans ?_
    intro m hm
    obtain ⟨μ, hμ, hm⟩ := Finset.mem_biUnion.1 hm
    have := support_monomial_subset hm
    rw [Finset.mem_singleton] at this
    exact Finset.mem_image.2 ⟨μ, hμ, this.symm⟩
  rw [Formalism.MainNotions.G.GLWeightTheory.fock_form_finset_sum _ _ _ hsupp, Finset.sum_image fun a _ b _ h => hε h]
  exact Finset.sum_congr rfl fun μ _ => by rw [hco, hco]

theorem topOdd_inj (X : Loc) (j : Fin (numSeg X.TT)) : Function.Injective (topOdd X j) := by
  intro i i' e
  have e' : segPos X.TT j i = segPos X.TT j i' := congrArg Subtype.val e
  have h1 := (pos_spec X.TT j i).2
  have h2 := (pos_spec X.TT j i').2
  rw [e'] at h1
  exact (dist_strictMono X.TT j).injective (h1.symm.trans h2)

theorem topOdd_ne_end (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : topOdd X j i ≠ topEnd X j := by
  intro e
  have e' : segPos X.TT j i = segNext X.TT j := congrArg Subtype.val e
  exact (pos_mem X.TT j i).2 (e' ▸ (next_mem X.TT j).2)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

