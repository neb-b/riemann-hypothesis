module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeightLatticeIndexIdentity

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogEigenModPrime
section
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

theorem coefLe_mv_of_ps {K : Type} [NormedField K] {r : ℝ} {A : K⟦X⟧} (h : ∀ n, ‖coeff n A‖ ≤ r) :
    ∀ m : Unit →₀ ℕ, ‖MvPowerSeries.coeff m A‖ ≤ r := by
  intro m
  have hm : m = Finsupp.single () (m ()) := by
    ext
    simp
  rw [hm]
  exact h (m ())

theorem norm_ringHom_pow_apply {K : Type} [NormedField K] (σ : K →+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) :
    ∀ (j : ℕ) (x : K), ‖(σ ^ j) x‖ = ‖x‖ := by
  intro j x
  induction j generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (ih (σ x)).trans (hσ x)

private theorem norm_coeff_pow_le_one {K : Type} [NormedField K] [IsUltrametricDist K] {s : Type}
    (M : MvPowerSeries s K) (hM : ∀ m, ‖MvPowerSeries.coeff m M‖ ≤ 1) :
    ∀ (N : ℕ) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (M ^ N)‖ ≤ 1 := by
  classical
  intro N
  induction N with
  | zero =>
    intro m
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ N ih =>
    intro m
    rw [pow_succ, MvPowerSeries.coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hM _)

theorem frobLog_eigen : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) →
    ∀ (i : ℕ), 0 < i → CoefLe ‖(l : K)‖ ((frobOp σ l i f).subst (Formalism.L2.Th1.C.mulBy f e w) -
      C ((σ ^ i) w) * frobOp σ l i f) := by
  intro K _ _ _ l σ hU f e hf w hw i hi
  have hU' := hU
  obtain ⟨hlp, -, hl1, -, hσn, -⟩ := hU
  obtain ⟨hlog, hd, hint⟩ := hf
  obtain ⟨h0, h1, h0', hfe, hef⟩ := hlog
  have hn : l ^ i ≠ 0 := pow_ne_zero _ hlp.ne_zero
  have hτ : ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := norm_ringHom_pow_apply σ hσn i
  set g := PowerSeries.map (σ ^ i) f with hg
  set e' := PowerSeries.map (σ ^ i) e with he'
  have hXm : MvPowerSeries.map (σ ^ i) (PowerSeries.X : K⟦X⟧) = PowerSeries.X := PowerSeries.map_X _
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have he0 : PowerSeries.constantCoeff e' = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he', PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0', map_zero]
  have hef' : PowerSeries.subst e' g = PowerSeries.X := by
    have := congrArg (MvPowerSeries.map (σ ^ i)) hef
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0'), hXm] at this
    exact this
  have hd' : CoefLe 1 (d⁄dX g) := by
    intro k
    rw [PowerSeries.coeff_derivative, hg, PowerSeries.coeff_map]
    have hk : (σ ^ i) ((PowerSeries.coeff (k + 1)) f) * ((k : K) + 1)
        = (σ ^ i) ((PowerSeries.coeff (k + 1)) f * ((k : K) + 1)) := by
      rw [map_mul, map_add (f := _), map_one, map_natCast]
    rw [hk, hτ, ← PowerSeries.coeff_derivative]
    exact hd k
  set M := Formalism.L2.Th1.C.mulBy f e w with hMdef
  have hCf0 : PowerSeries.constantCoeff (PowerSeries.C w * f) = 0 := by
    rw [map_mul, h0, mul_zero]
  have hM0 : MvPowerSeries.constantCoeff M = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hCf0 _ h0'
  have hMint : ∀ m, ‖MvPowerSeries.coeff m M‖ ≤ 1 := coefLe_mv_of_ps hw
  have hAB := _root_.GlobalTheory.Honda.pow_frob_sub_le K l σ hU' Unit M hMint i hn
  set A := M ^ l ^ i with hA
  set B := MvPowerSeries.expand (l ^ i) hn (MvPowerSeries.map (σ ^ i) M) with hB
  have hA0 : MvPowerSeries.constantCoeff A = 0 := by
    rw [hA, map_pow, hM0, zero_pow hn]
  have hB0 : MvPowerSeries.constantCoeff B = 0 := by
    simp [hB, hM0]
  have hA1 : ∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1 := fun m => norm_coeff_pow_le_one M hMint _ m
  have hB1 : ∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1 := by
    intro m
    have hb : MvPowerSeries.coeff m B
        = MvPowerSeries.coeff m A + -(MvPowerSeries.coeff m (A - B)) := by
      rw [map_sub]
      ring
    rw [hb]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
    exact max_le (hA1 m) ((hAB m).trans hl1.le)
  have key := GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative K l hlp hl1 g hd' Unit A B hA0 hB0 hA1 hB1 hAB
  have hsM : PowerSeries.subst M (frobOp σ l i f) = PowerSeries.subst A g := by
    have has := PowerSeries.HasSubst.of_constantCoeff_zero hM0
    unfold frobOp
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hn) has,
      PowerSeries.subst_pow has, PowerSeries.subst_X has]
  set c := (σ ^ i) w with hc
  have hq0 : PowerSeries.constantCoeff (PowerSeries.C c * g) = 0 := by
    rw [map_mul, hg0, mul_zero]
  have hmapM : MvPowerSeries.map (σ ^ i) M = PowerSeries.subst (PowerSeries.C c * g) e' := by
    have hm : MvPowerSeries.map (σ ^ i) (PowerSeries.C w * f) = PowerSeries.C c * g := by
      change PowerSeries.map (σ ^ i) (PowerSeries.C w * f) = _
      rw [map_mul, PowerSeries.map_C]
    rw [hMdef]
    unfold Formalism.L2.Th1.C.mulBy
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hCf0), hm]
  have hexp : MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g)
      = PowerSeries.C c * PowerSeries.subst (PowerSeries.X ^ l ^ i) g := by
    change PowerSeries.expand (l ^ i) hn (PowerSeries.C c * g) = _
    rw [PowerSeries.expand_apply, PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow hn),
      PowerSeries.subst_C]
    rfl
  have hexp0 : MvPowerSeries.constantCoeff (MvPowerSeries.expand (l ^ i) hn (PowerSeries.C c * g)) = 0 := by
    rw [MvPowerSeries.constantCoeff_expand]
    exact hq0
  have hBg : PowerSeries.subst B g = PowerSeries.C c * frobOp σ l i f := by
    rw [hB, hmapM, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.of_constantCoeff_zero hq0),
      ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' he0)
        (PowerSeries.HasSubst.of_constantCoeff_zero hexp0),
      hef', PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hexp0), hexp]
    rfl
  intro k
  rw [hsM, ← hBg]
  exact key (Finsupp.single () k)

end GlobalTheory.Honda
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeSumTermAtCoset
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTarget

open GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem inSupp_mul_left {y : Matrix (A ⊕ D') (A ⊕ D) k} (hy : InSupp y) {u : GL (A ⊕ D') k}
    (hu : u ∈ parahoric k A D') : InSupp (u.val * y) ∧
      valuation k ((u.val * y).toBlocks₁₁.det - u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) < 1 := by
  have hJ := GlobalTheory.DatumEigen.int_of_mem hu
  have hl := (mem_parahoric.1 hu).2
  obtain ⟨hyi, hyd, hyl⟩ := hy
  have hprod : ∀ i l, (u.val * y) i l ∈ 𝒪[k] := fun i l => by
    rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hJ i m) (hyi m l)
  have hcong : valuation k ((u.val * y).toBlocks₁₁.det - u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine GlobalTheory.DatumEigen.val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [Matrix.mul_apply]; exact sum_mem fun m _ => mul_mem (hJ _ _) (hyi _ _)
    · simp only [toBlocks₁₁, of_apply, Matrix.mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)
  have hd1 : valuation k (u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hyd, mul_one, (GlobalTheory.DatumEigen.val_det_blocks hu).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact GlobalTheory.DatumEigen.val_mul_lt (hyi _ _) (hl _ _)
    · exact GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem torusElt_indic_int {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D') :
    IsIntM (torusElt k D' ϖ (indic s)).val := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  rw [val_torusElt]
  intro i j
  rw [diagonal_apply]; split_ifs
  · show valuation k _ ≤ 1
    rw [map_zpow₀]
    exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)
  · exact zero_mem _

theorem inSupp_diag_mul {y : Matrix (A ⊕ D') (A ⊕ D) k} (hy : InSupp y) {t : Matrix D' D' k} (ht : IsIntM t) :
    InSupp ((fromBlocks (1 : Matrix A A k) 0 0 t : Matrix (A ⊕ D') (A ⊕ D') k) * y) ∧
      ((fromBlocks (1 : Matrix A A k) 0 0 t : Matrix (A ⊕ D') (A ⊕ D') k) * y).toBlocks₁₁ = y.toBlocks₁₁ := by
  obtain ⟨h1, h2, h3⟩ := hy
  obtain ⟨a, b, c, e⟩ := isIntM_toBlocks (show IsIntM y from h1)
  rw [fromBlocks_diag_mul]
  refine ⟨⟨isIntM_fromBlocks_iff.2 ⟨a, b, isIntM_mul ht c, isIntM_mul ht e⟩, by simpa using h2, fun i j => ?_⟩,
    toBlocks_fromBlocks₁₁ _ _ _ _⟩
  rw [fromBlocks_apply₂₁]
  exact val_lt_mul ht (fun a b => h3 a b) i j


open Classical in
theorem coset_term : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, (InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → ((ξ d * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = datum ξ x) ∧ (¬ InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = 0) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s j hj d hd x
  set y := ((j * mtor ϖ (indic s))⁻¹).1 * x with hydef
  refine ⟨fun hW => ?_, fun hW => by simp only [datum, dif_neg hW]⟩
  set T := torusElt k D' ϖ (indic s) with hT
  have hg0 : (mtor (A := A) ϖ (indic s)).val = fromBlocks (1 : Matrix A A k) 0 0 T.val := by
    rw [mtor_eq_dg, val_dg]
  have hx : x = j.val * ((mtor (A := A) ϖ (indic s)).val * y) := by
    rw [hydef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  obtain ⟨hg, hg11⟩ := inSupp_diag_mul hW (torusElt_indic_int hϖ s)
  rw [← hg0] at hg hg11
  obtain ⟨hs, hc⟩ := inSupp_mul_left hg hj
  rw [← hx, hg11] at hc
  rw [← hx] at hs
  obtain ⟨h11, h22⟩ := GlobalTheory.DatumEigen.val_det_blocks hj
  have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
  set u₁ : kˣ := Units.mk0 _ n11 with hu₁
  have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
  have t1 : ξ (GeneralLinearGroup.det j) = ξ (u₁ * d) := by
    refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
    rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.DatumEigen.det_cong hj
  have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hW.det_ne * u₁) := by
    refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hW.2.1, one_mul]; exact h11) ?_
    show valuation k (x.toBlocks₁₁.det - y.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1
    rw [mul_comm (y.toBlocks₁₁.det)]
    exact hc
  simp only [datum, dif_pos hs, dif_pos hW]
  rw [t1, t2, ← Units.val_mul]
  congr 1
  simp only [map_mul]
  group

end GlobalTheory.ParHeckeTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeightLatticeIndexIdentityStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open GlobalTheory.HeckeLatIndex in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedHeight_lattice_index_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ H : GL D k → ℝ, IsHgt ϖ H → ∀ (m g : GL D k) (s : Finset D), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∀ (L Lm large₂ : AddSubgroup (D → k)), (∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1) → (∀ v, v ∈ Lm ↔ m.1.mulVec v ∈ L) → (∀ v, v ∈ large₂ ↔ (g⁻¹).1.mulVec v ∈ L) → (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g) = (resCard k : ℝ) ^ s.card * H m := by
  intro k _ _ _ _ D _ _ ϖ hϖ H hH m g s hg L Lm large₂ hL hLm hLg
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (show 0 < resCard k by unfold resCard; exact Nat.card_pos)
  have hgt_mul_index (h : GL D k) (L P : AddSubgroup (D → k))
      (hL : ∀ v, v ∈ L ↔ ∀ i, valuation k (v i) < 1)
      (hP : ∀ v, v ∈ P ↔ h.1.mulVec v ∈ L) :
      H h * (((P ⊓ L).relIndex P : ℕ) : ℝ) * (((P ⊓ L).relIndex L : ℕ) : ℝ) = 1 := by
    have decompose (g : GL D k) :
        ∃ x ∈ KO k D, ∃ y ∈ KO k D, ∃ e : D → ℤ, g = x * torusElt k D ϖ e * y := by
      obtain ⟨x, hx, y, hy, a, rfl⟩ := GlobalTheory.LocalCartan.exists_diagT g
      let ordHom : kˣ →* Multiplicative ℤ :=
        MonoidHom.mk' (fun z => Multiplicative.ofAdd (ord k z))
          (fun z w => by rw [ord_mul, ofAdd_add])
      let e : D → ℤ := fun i => ord k (a i)
      let u : D → kˣ := fun i => a i / ϖ ^ e i
      have hu (i : D) : valuation k (u i : k) = 1 := by
        apply ord_eq_zero_iff.mp
        have he := congrArg Multiplicative.toAdd (map_zpow ordHom ϖ (e i))
        have hp : ord k (ϖ ^ e i) = e i := by
          simpa [ordHom, toAdd_zpow, ord_eq_one hϖ] using he
        have hz := ord_mul k (u i) (ϖ ^ e i)
        rw [show u i * ϖ ^ e i = a i by simp [u], hp] at hz
        change e i = _ at hz
        omega
      refine ⟨x * diagT k D u, mul_mem hx (GlobalTheory.LocalCartan.diagT_mem_KO hu),
        y, hy, e, ?_⟩
      have ha : a = u * fun i => ϖ ^ e i := funext fun i => by simp [u]
      unfold torusElt
      rw [ha, map_mul]
      simp only [mul_assoc]
    obtain ⟨x, hx, y, hy, e, rfl⟩ := decompose h
    let t : GL D k := torusElt k D ϖ e
    let Pt : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin t.1).toAddMonoidHom
    have hPt : ∀ v, v ∈ Pt ↔ t.1.mulVec v ∈ L := fun v => Iff.rfl
    obtain ⟨e1, e2⟩ := ko_index k D t x y hx hy L Pt P hL hPt hP
    have hd := diag_index k D ϖ hϖ e L Pt hL (fun v => by
      rw [hPt, hL]
      simp [t, torusElt, val_diagT, Matrix.mulVec_diagonal])
    have hH1 : H (x * t * y) = H t := by rw [(hH.1 y hy _).2, (hH.1 x hx _).1]
    rw [e1, e2, mul_assoc, hd]
    change H (x * t * y) * _ = 1
    rw [hH1, hH.2 e, ← zpow_add₀ hq.ne']
    simp
  obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hg

  have hgL : ∀ v, v ∈ L → g.1.mulVec v ∈ L := by
    intro v hv
    rw [hgeq, hL]
    have h1 := ko_pres k D κ' hκ' v ((hL v).1 hv)
    have h2 : ∀ i, valuation k ((torusElt k D ϖ (indic s)).1.mulVec (κ'.1.mulVec v) i) < 1 := by
      intro i
      simp only [torusElt, val_diagT, Matrix.mulVec_diagonal, map_mul]
      have hle : valuation k ((ϖ ^ indic s i : kˣ) : k) ≤ 1 := by
        unfold indic
        split_ifs
        · simp only [zpow_one]
          rw [hϖ]
          exact uniformizer_lt_one.le
        · simp
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hle) (h1 i)
    have h3 := ko_pres k D κ hκ _ h2
    simpa [Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc] using h3
  have hLgL : large₂ ≤ L := by
    intro v hv
    have : g.1.mulVec ((g⁻¹).1.mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this]
    exact hgL _ ((hLg v).1 hv)
  set φ := (Matrix.mulVecLin g.1).toAddMonoidHom with hφ
  have hinj : Function.Injective φ := mulVec_injective g

  let P₁ : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin (m * g).1).toAddMonoidHom
  let P₂ : AddSubgroup (D → k) := L.comap (Matrix.mulVecLin g.1).toAddMonoidHom
  have hP₁ : ∀ v, v ∈ P₁ ↔ (m * g).1.mulVec v ∈ L := fun v => Iff.rfl
  have hP₂ : ∀ v, v ∈ P₂ ↔ g.1.mulVec v ∈ L := fun v => Iff.rfl
  have mP₁ : P₁.map φ = Lm := map_eq_of_preimage g P₁ Lm fun w => by
    rw [hP₁, hLm, Units.val_mul, Matrix.mulVec_mulVec]
  have mL : L.map φ = large₂ := by
    refine map_eq_of_preimage g L large₂ fun w => ?_
    rw [hLg, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have mP₂ : P₂.map φ = L := map_eq_of_preimage g P₂ L hP₂
  have k₁ := hgt_mul_index m L Lm hL hLm
  have k₂ := hgt_mul_index (m * g) L P₁ hL hP₁
  have k₃ := hgt_mul_index g L P₂ hL hP₂
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj,
    ← AddSubgroup.relIndex_map_map_of_injective (f := φ) (P₁ ⊓ L) L hinj,
    AddSubgroup.map_inf_eq _ _ _ hinj, mP₁, mL] at k₂
  have hLP₂ : L ≤ P₂ := fun v hv => hgL v hv
  rw [inf_eq_right.2 hLP₂, AddSubgroup.relIndex_self, ← AddSubgroup.relIndex_map_map_of_injective (f := φ) _ _ hinj,
    mL, mP₂] at k₃
  have hHg : H g = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [hgeq, (hH.1 κ' hκ' _).2, (hH.1 κ hκ _).1, hH.2]
    congr 2
    unfold sumAbs indic
    rw [Finset.sum_congr rfl (fun i _ => show |(if i ∈ s then (1:ℤ) else 0)| = if i ∈ s then 1 else 0 by split_ifs <;> simp)]
    simp
  rw [hHg] at k₃

  have t₁ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) Lm (inf_le_inf_left _ hLgL) inf_le_left
  have t₂ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) large₂ L inf_le_right hLgL
  have t₃ := AddSubgroup.relIndex_mul_relIndex (Lm ⊓ large₂) (Lm ⊓ L) L (inf_le_inf_left _ hLgL) inf_le_right
  have hQ : (large₂.relIndex L : ℝ) = (resCard k : ℝ) ^ s.card := by
    have hne' : (resCard k : ℝ) ^ s.card ≠ 0 := by positivity
    rw [_root_.zpow_neg, zpow_natCast, Nat.cast_one, mul_one, inv_mul_eq_one₀ hne'] at k₃
    exact k₃.symm
  have e1 : (((Lm ⊓ large₂).relIndex Lm : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex Lm : ℕ) := by
    rw [← t₁]; push_cast; ring
  have e2 : (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ) = ((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) * ((Lm ⊓ L).relIndex L : ℕ) := by
    rw [← hQ]
    have := congrArg (fun n : ℕ => (n : ℝ)) (t₂.trans t₃.symm)
    push_cast at this
    linarith
  linear_combination (-(((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) ^ 2 * H (m * g)) * k₁ + ((resCard k : ℝ) ^ s.card * H m) * k₂
    + (-(H m * H (m * g) * (resCard k : ℝ) ^ s.card * (((Lm ⊓ large₂).relIndex large₂ : ℕ) : ℝ))) * e1
    + (-(H m * H (m * g) * (((Lm ⊓ large₂).relIndex (Lm ⊓ L) : ℕ) : ℝ) * (((Lm ⊓ L).relIndex Lm : ℕ) : ℝ))) * e2
end

