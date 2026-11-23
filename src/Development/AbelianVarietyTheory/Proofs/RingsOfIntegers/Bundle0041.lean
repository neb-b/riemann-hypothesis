module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpec
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GaugeThirdDifferenceSymmetryIntegralExponentials
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLaws
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantSectionEqLimitChartPoint
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit

theorem ptOf_const_left : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (G : Over (Sp V)) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (X : limO V d 1 ⟶ G), IsLimit x X → ∀ (α : Fin d → V) (hα : Small α) (aV : Sp V ⟶ G.left), (∀ m : ℕ, ∃ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1), (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p.2)) ∧ spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ aV = spMap (ψ : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (x m).left) → ∀ n : ℕ, (ptOf X (Sm.const B α hα : Sm B n)).left = spMap (algebraMap V (PS V n d)) ≫ aV := by
  intro V _ _ _ _ _ d O _ _ B G x X hX α hα aV ha n
  let χ : PS V 1 d →ₐ[V] V :=
    GlobalTheory.mvEvalAdic V (maximalIdeal V) (fun p : Fin 1 × Fin d => α p.2) (fun p => hα p.2)
  have hχ : ∀ p, χ (MvPowerSeries.X p) = α p.2 := fun p => GlobalTheory.mvEvalAdic_X _ _ _ p
  have h1 : evA ![(Sm.const B α hα : Sm B n)] = (Algebra.ofId V (PS V n d)).comp χ := by
    refine AlgHom.ext fun f => (evA_apply _ f).trans ?_
    refine evC_eq_algHom _ (fun p : Fin 1 × Fin d => ((![(Sm.const B α hα : Sm B n)] : Fin 1 → Sm B n) p.1).2 p.2)
      _ (fun p => ?_) f
    obtain ⟨i, j⟩ := p
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, hχ]
    rfl
  have h2 : spMap (χ : PS V 1 d →+* V) ≫ X.left = aV := by
    refine GlobalTheory.hom_ext_of_isHausdorff (maximalIdeal V) fun m => ?_
    obtain ⟨ψ, hψ, e⟩ := ha m
    have hj : ∀ p : Fin 1 × Fin d, jetA (V := V) (Fin 1 × Fin d) m (MvPowerSeries.X p) =
        Ideal.Quotient.mk _ (MvPolynomial.X p) := fun p => by
      first
      | exact (mk_psTrunc m _ (MvPowerSeries.constantCoeff_X p)).trans (Chart.pj_X m p)
      | exact FBIdSy.mk_psTrunc_X m p
      | exact (mk_psTrunc m _ (MvPowerSeries.constantCoeff_X p)).symm.trans (Chart.pj_X m p)
    have k : ψ.comp (jetA (Fin 1 × Fin d) m) = (Ideal.Quotient.mkₐ V (maximalIdeal V ^ (m + 1))).comp χ := by
      have hv : ∀ p, (ψ.comp (jetA (Fin 1 × Fin d) m)) (MvPowerSeries.X p) = Ideal.Quotient.mk _ (α p.2) :=
        fun p => by rw [AlgHom.comp_apply, hj, hψ]
      have hv' : ∀ p, ((Ideal.Quotient.mkₐ V (maximalIdeal V ^ (m + 1))).comp χ) (MvPowerSeries.X p) =
          Ideal.Quotient.mk _ (α p.2) := fun p => by rw [AlgHom.comp_apply, hχ]; rfl
      refine AlgHom.ext fun f => ?_
      have := GlobalTheory.algHom_sub_mem_pow _ _
        (J := (maximalIdeal V).map (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))))
        (fun p => hv p ▸ Ideal.mem_map_of_mem _ (hα p.2)) (fun p => hv' p ▸ Ideal.mem_map_of_mem _ (hα p.2))
        (n := m + 1) (fun p => by rw [hv, hv', sub_self]; exact zero_mem _) f
      rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot, sub_eq_zero] at this
      exact this
    have k2 := GlobalTheory.PlaceFormPt.spMap_homAt (jetA (Fin 1 × Fin d) m) ψ X.left
    rw [k] at k2
    have k3 : (x m).left = (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetA (Fin 1 × Fin d) m)).left ≫ X.left :=
      (congrArg (fun q => q.left) (hX m)).symm
    refine Eq.trans ?_ (k2.symm.trans ((congrArg (_ ≫ ·) k3.symm).trans e.symm))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.left) (Spec.map_comp _ _).symm)
  rw [← h2, ptOf, h1]
  exact (congrArg (· ≫ X.left) (Spec.map_comp (CommRingCat.ofHom (χ : PS V 1 d →+* V))
    (CommRingCat.ofHom (algebraMap V (PS V n d))))).trans (Category.assoc _ _ _)

end GlobalTheory.TransUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvalIotaSeriesEqQuadraticInversionPartials
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PlaceInt.ThetaInt

namespace GlobalTheory.TransUnit.IotaLaw

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B : FB V d O} {n : ℕ}

theorem evA_three (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) (f : PS V 3 d) :
    evA ![x, y, z] f = ev ![x.1, y.1, z.1] f := by
  rw [evA_eq_ev]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j i
    fin_cases j
    exacts [hx i, hy i, hz i]

theorem mul_val_of (x y : Sm B n) (hx : GP x.1) (hy : GP y.1) : (x * y).1 = addOf B.G.F x.1 y.1 := by
  rw [Sm.mul_val]
  funext i
  show evV ![x.1, y.1] (B.G.F i) = ev ![x.1, y.1] (B.G.F i)
  rw [← smallPointsSubstitutionAlgHom_two_points, evA_eq_ev]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j k
    fin_cases j
    exacts [hx k, hy k]

theorem compV_of (φ : Pt V 1 d) (x : Sm B n) (hx : GP x.1) : compV φ x.1 = comp1 φ x.1 := by
  funext i
  show evV ![x.1] (φ i) = ev ![x.1] (φ i)
  rw [← smallPointsSubstitutionAlgHom_single_point, evA_eq_ev]
  · congr 1
    funext j
    fin_cases j
    rfl
  · intro j k
    fin_cases j
    exact hx k

theorem constantCoeff_act_eq_zero (o : O) (x : Sm B n) (hx : GP x.1) : GP (Sm.act B o x).1 := by
  rw [Sm.act_val, compV_of _ x hx]
  exact gp_comp1 _ _ (fun i => B.A.const o i) hx

theorem constantCoeff_inv_eq_zero (x : Sm B n) (hx : GP x.1) : GP (x⁻¹).1 := by
  rw [Sm.inv_val, ← Sm.act_val]
  exact constantCoeff_act_eq_zero (-1) x hx

variable (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] {h : PS K 2 d}

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] [Algebra ℚ K] in
theorem mp_zero : mp K (0 : Pt V n d) = 0 := by
  funext i
  simp [mp]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one (hh : B.IsCanonGauge K h) (a : Pt K n d) (ha : GP a) : ev ![0, a] h = 0 := by
  obtain ⟨h1, h2, -, -, -, -⟩ := hh
  have hv : ∀ j, GP (![a] j) := single_point_zero_constant ha
  have hw : ∀ j, GP (![(0 : Pt K 1 d), pt K (n := 1) d 0] j) := pair_points_zero_constant gp_zero₂ (gp_pt 0)
  have e := gt_ev_ev' ![a] _ hv hw h
  rw [h1, eval_pair_points, evP_zero _ hv, evP_pt _ hv] at e
  simp only [Matrix.cons_val_zero] at e
  rw [← e, gt_ev_zero _ hv]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem canonicalGauge_eval_zero_right (hh : B.IsCanonGauge K h) (a : Pt K n d) (ha : GP a) : ev ![a, 0] h = 0 := by
  obtain ⟨h1, h2, -, -, -, -⟩ := hh
  have hv : ∀ j, GP (![a] j) := single_point_zero_constant ha
  have hw : ∀ j, GP (![pt K (n := 1) d 0, (0 : Pt K 1 d)] j) := pair_points_zero_constant (gp_pt 0) gp_zero₂
  have e := gt_ev_ev' ![a] _ hv hw h
  rw [h2, eval_pair_points, evP_zero _ hv, evP_pt _ hv] at e
  simp only [Matrix.cons_val_zero] at e
  rw [← e, gt_ev_zero _ hv]

theorem canonicalGauge_first_partial_law_in_field (hh : B.IsCanonGauge K h) (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) :
    FB.toK K (evA ![x, y, z] B.ph1) = FB.expS K (ev ![mp K x.1, mp K z.1] h + ev ![mp K y.1, mp K z.1] h
      - ev ![mp K (x * y).1, mp K z.1] h) := by
  have hc : MvPowerSeries.constantCoeff h = 0 := cc_gauge (K := K) (B := B) hh
  obtain ⟨-, -, h3, h4, -, -⟩ := hh
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK K i) = 0 := cc_FK (K := K) (B := B)
  have p0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have pa : GP (addOf (B.FK K) (pt K (n := 3) d 0) (pt K d 1)) := gp_addOf _ hF _ _ p0 p1
  have hX : ∀ j, GP (![mp K x.1, mp K y.1, mp K z.1] j) := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K hx) (constantCoeff_baseChange_eq_zero K hy) (constantCoeff_baseChange_eq_zero K hz)
  have hv : (fun j => mp K (![x.1, y.1, z.1] j)) = ![mp K x.1, mp K y.1, mp K z.1] := by
    funext j
    fin_cases j <;> rfl
  rw [evA_three x y z hx hy hz, toK_ev K _ (triple_points_zero_constant hx hy hz), h3, hv]
  rw [gt_ev_expS _ hX]
  · congr 1
    rw [gt_ev_sub _ hX, gt_ev_add _ hX, gt_ev_ev' _ _ hX (pair_points_zero_constant p0 p2), gt_ev_ev' _ _ hX (pair_points_zero_constant p1 p2),
      gt_ev_ev' _ _ hX (pair_points_zero_constant pa p2), eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hX _ _ _ p0 p1,
      evP_pt _ hX, evP_pt _ hX, evP_pt _ hX, mul_val_of x y hx hy, mp_addOf K B.G _ _ hx hy]
    rfl
  · rw [map_sub, map_add (f := _), gt_const_ev_eq _ (pair_points_zero_constant p0 p2), gt_const_ev_eq _ (pair_points_zero_constant p1 p2),
      gt_const_ev_eq _ (pair_points_zero_constant pa p2), hc]
    simp

theorem canonicalGauge_second_partial_law_in_field (hh : B.IsCanonGauge K h) (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) :
    FB.toK K (evA ![x, y, z] B.ph2) = FB.expS K (ev ![mp K x.1, mp K y.1] h + ev ![mp K x.1, mp K z.1] h
      - ev ![mp K x.1, mp K (y * z).1] h) := by
  have hc : MvPowerSeries.constantCoeff h = 0 := cc_gauge (K := K) (B := B) hh
  obtain ⟨-, -, h3, h4, -, -⟩ := hh
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK K i) = 0 := cc_FK (K := K) (B := B)
  have p0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have pa : GP (addOf (B.FK K) (pt K (n := 3) d 1) (pt K d 2)) := gp_addOf _ hF _ _ p1 p2
  have hX : ∀ j, GP (![mp K x.1, mp K y.1, mp K z.1] j) := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K hx) (constantCoeff_baseChange_eq_zero K hy) (constantCoeff_baseChange_eq_zero K hz)
  have hv : (fun j => mp K (![x.1, y.1, z.1] j)) = ![mp K x.1, mp K y.1, mp K z.1] := by
    funext j
    fin_cases j <;> rfl
  rw [evA_three x y z hx hy hz, toK_ev K _ (triple_points_zero_constant hx hy hz), h4, hv]
  rw [gt_ev_expS _ hX]
  · congr 1
    rw [gt_ev_sub _ hX, gt_ev_add _ hX, gt_ev_ev' _ _ hX (pair_points_zero_constant p0 p1), gt_ev_ev' _ _ hX (pair_points_zero_constant p0 p2),
      gt_ev_ev' _ _ hX (pair_points_zero_constant p0 pa), eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hX _ _ _ p1 p2,
      evP_pt _ hX, evP_pt _ hX, evP_pt _ hX, mul_val_of y z hy hz, mp_addOf K B.G _ _ hy hz]
    rfl
  · rw [map_sub, map_add (f := _), gt_const_ev_eq _ (pair_points_zero_constant p0 p1), gt_const_ev_eq _ (pair_points_zero_constant p0 p2),
      gt_const_ev_eq _ (pair_points_zero_constant p0 pa), hc]
    simp

private theorem eq_of_toK_eq_of_injective (hi : Function.Injective (algebraMap V K)) {m : ℕ} (a b : PS V m d)
    (hab : FB.toK K a = FB.toK K b) : a = b := by
  unfold FB.toK at hab
  refine MvPowerSeries.ext fun k => ?_
  have e := congrArg (MvPowerSeries.coeff k) hab
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at e
  exact hi e

theorem iota_gen (hi : Function.Injective (algebraMap V K)) (hh : B.IsCanonGauge K h) (w0 : O)
    (p₁ p₂ : (PS V 3 d)ˣ) (e₁ : p₁.val = B.ph1) (e₂ : p₂.val = B.ph2) (jo : PS V 1 d) (hj : IsIota B K h w0 jo) :
    jo = (quadN (u3 p₁) (u3 p₂) (Sm.act B w0) (Sm.gen B (0 : Fin 1))).val := by
  unfold IsIota at hj
  set g : Sm B 1 := Sm.gen B 0 with hgdef
  have hg : GP g.1 := gp_pt 0
  have hgi : GP (g⁻¹).1 := constantCoeff_inv_eq_zero g hg
  have hwg : GP (Sm.act B w0 g).1 := constantCoeff_act_eq_zero w0 g hg
  have hwgi : GP ((Sm.act B w0 g)⁻¹).1 := constantCoeff_inv_eq_zero _ hwg
  have hc : MvPowerSeries.constantCoeff h = 0 := cc_gauge (K := K) (B := B) hh
  have c2 : ∀ a b : Pt K 1 d, GP a → GP b → MvPowerSeries.constantCoeff (ev ![a, b] h) = 0 := fun a b ha hb => by
    rw [gt_const_ev_eq _ (pair_points_zero_constant ha hb), hc]
  have hL1 : B.hL K h w0 = ev ![mp K g.1, mp K (Sm.act B w0 g).1] h := by
    have e := ev_hL K B h w0 g.1 hg
    rw [Sm.act_val, compV_of _ g hg, ← e, show mp K g.1 = pt K (n := 1) d 0 from mp_pt K 0, gt_ev_pt_self]
  have ha : mp K (g⁻¹).1 = B.actK K (-1) := by
    rw [Sm.inv_val, compV_of _ g hg]
    show mp K (comp1 (B.A.act (-1)) (pt V (n := 1) d 0)) = _
    rw [gt_comp1_pt_right]
    rfl
  have hL2 : ev ![B.actK K (-1)] (B.hL K h w0) = ev ![mp K (g⁻¹).1, mp K ((Sm.act B w0 g)⁻¹).1] h := by
    rw [← ha, ev_hL K B h w0 (g⁻¹).1 hgi, ← map_inv (Sm.act B w0) g, Sm.act_val, compV_of _ _ hgi]
  have key : jo * (u3 p₁ g g⁻¹ (Sm.act B w0 g)).val = (u3 p₂ g⁻¹ (Sm.act B w0 g) (Sm.act B w0 g)⁻¹).val := by
    apply eq_of_toK_eq_of_injective K hi
    have hm : ∀ a b : PS V 1 d, FB.toK K (a * b) = FB.toK K a * FB.toK K b := fun a b => by
      unfold FB.toK
      exact map_mul _ _ _
    rw [hm, hj]
    unfold u3
    rw [evU_val, evU_val, e₁, e₂, canonicalGauge_first_partial_law_in_field K hh g g⁻¹ _ hg hgi hwg, canonicalGauge_second_partial_law_in_field K hh g⁻¹ _ _ hgi hwg hwgi,
      mul_inv_cancel, mul_inv_cancel, Sm.one_val, mp_zero K, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one K hh _ (constantCoeff_baseChange_eq_zero K hwg),
      canonicalGauge_eval_zero_right K hh _ (constantCoeff_baseChange_eq_zero K hgi), hL2, hL1]
    have cA := c2 _ _ (constantCoeff_baseChange_eq_zero K hgi) (constantCoeff_baseChange_eq_zero K hwgi)
    have cB := c2 _ _ (constantCoeff_baseChange_eq_zero K hg) (constantCoeff_baseChange_eq_zero K hwg)
    have cQ := c2 _ _ (constantCoeff_baseChange_eq_zero K hgi) (constantCoeff_baseChange_eq_zero K hwg)
    rw [← gt_expS_add]
    · congr 1
      ring
    · simp [cA, cB]
    · simp [cB, cQ]
  unfold quadN
  rw [div_eq_mul_inv, Units.val_mul, ← key, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

end GlobalTheory.TransUnit.IotaLaw

namespace GlobalTheory.TransUnit

theorem evA_iota_eq_quadN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (p₁ p₂ : (PS V 3 d)ˣ), p₁.val = B.ph1 → p₂.val = B.ph2 → ∀ jo : PS V 1 d, IsIota B K h w0 jo → ∀ (n : ℕ) (x : Sm B n), evA ![x] jo = (quadN (u3 p₁) (u3 p₂) (Sm.act B w0) x).val := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ _ h w0 hh p₁ p₂ e₁ e₂ jo hj n x
  rw [IotaLaw.iota_gen K (IsFractionRing.injective V K) hh w0 p₁ p₂ e₁ e₂ jo hj, ← evU_val,
    ← quadN_map (Sm.sub ![x]) (evU ![x]) (fun y => (Sm.sub_act ![x] w0 y).symm) (fun a b c => unitSeriesValueThreePoints_substitution ![x] p₁ a b c)
      (fun a b c => unitSeriesValueThreePoints_substitution ![x] p₂ a b c) (Sm.gen B 0), Sm.sub_gen]
  rfl

end GlobalTheory.TransUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowerSeriesLimitOfCompatibleJetPoints
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit.LimEx

variable {V : Type} [CommRing V] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem isLocalRing_jet [IsLocalRing V] (m : ℕ) : IsLocalRing (Jet V κ m) :=
  haveI : Nontrivial (Jet V κ m) := (jetAug : Jet V κ m →ₐ[V] V).toRingHom.domain_nontrivial
  IsLocalRing.of_surjective' (jetA κ m : MvPowerSeries κ V →ₐ[V] Jet V κ m).toRingHom
    (fun a => GlobalTheory.ChartCmp.FrameRatio.psJet_surj m a)

theorem exists_ringHom_of_jets {A : Type} [CommRing A] (φ : ∀ m, A →+* Jet V κ m)
    (h : ∀ m a, (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) (φ (m + 1) a) = φ m a) :
    ∃ ψ : A →+* MvPowerSeries κ V, ∀ m a, jetA κ m (ψ a) = φ m a := by
  choose f hf using fun a => GermD.exists_ps_of_jets (fun m => φ m a) (fun m => h m a)
  have hf' : ∀ a m, jetA κ m (f a) = φ m a := hf
  have ext : ∀ {p q : MvPowerSeries κ V}, (∀ m, jetA κ m p = jetA κ m q) → p = q :=
    fun hpq => FrameBiextId.ps_ext hpq
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun m a => hf' a m⟩
  · exact ext fun m => by rw [hf', map_one, map_one]
  · exact fun a b => ext fun m => by rw [map_mul, hf', hf', hf', map_mul]
  · exact ext fun m => by rw [hf', map_zero, map_zero]
  · exact fun a b => ext fun m => by rw [map_add (f := _), hf', hf', hf', map_add (f := _)]

theorem exists_limit_hom [IsLocalRing V] {Y : Scheme.{0}} (p : Y ⟶ Spec (.of V))
    (x : ∀ m, Spec (.of (Jet V κ m)) ⟶ Y)
    (hx : ∀ m, Spec.map (CommRingCat.ofHom
      ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)) ≫ x (m + 1) = x m)
    (hp : ∀ m, x m ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (Jet V κ m)))) :
    ∃ g : Spec (.of (MvPowerSeries κ V)) ⟶ Y,
      g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (MvPowerSeries κ V))) ∧
      ∀ m, Spec.map (CommRingCat.ofHom ((jetA κ m : MvPowerSeries κ V →ₐ[V] Jet V κ m) :
        MvPowerSeries κ V →+* Jet V κ m)) ≫ g = x m := by
  have hloc := fun m => isLocalRing_jet (V := V) (κ := κ) m
  let y : Y := x 0 (closedPoint (Jet V κ 0))
  have hy : ∀ m, x m (closedPoint (Jet V κ m)) = y := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← ih, ← hx m]
      refine Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _).symm
      have : IsLocalHom (CommRingCat.ofHom
          ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)).hom :=
        IsLocalHom.of_surjective _ (fun a => by
          obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
          exact ⟨Ideal.Quotient.mk _ q, rfl⟩)
      have h1 := Spec_closedPoint (f := CommRingCat.ofHom
          ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m))
      exact congrArg (x (m + 1)) h1.symm
  choose φ hφ using fun m => (GlobalTheory.existsUnique_factor_stalk (x m) (hy m)).exists
  have hc : ∀ m a, (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) ((φ (m + 1)).hom a) = (φ m).hom a := by
    intro m a
    have h1 : Spec.map (CommRingCat.ofHom
        ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)) ≫
        Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono (Y.fromSpecStalk y), Category.assoc, hφ, hφ, hx m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom a)
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_jets (fun m => (φ m).hom) hc
  obtain ⟨s, hs⟩ := Spec.map_surjective (Y.fromSpecStalk y ≫ p)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y, ?_, fun m => ?_⟩
  · rw [Category.assoc, ← hs, ← Spec.map_comp]
    congr 1
    ext1
    refine RingHom.ext fun c => FrameBiextId.ps_ext fun m => ?_
    have h1 : Spec.map (φ m) ≫ Spec.map s = Spec.map (CommRingCat.ofHom (algebraMap V (Jet V κ m))) := by
      rw [hs, ← Category.assoc, hφ, hp]
    rw [← Spec.map_comp] at h1
    have h2 : (φ m).hom (s.hom c) = algebraMap V (Jet V κ m) c := congr($(Spec.map_injective h1).hom c)
    exact ((hψ m (s.hom c)).trans h2).trans ((jetA κ m).commutes c).symm
  · rw [← hφ m, ← Spec.map_comp_assoc]
    congr 2
    ext1
    exact RingHom.ext fun a => hψ m a

theorem exists_isLimit : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) (d : ℕ)
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G),
    (∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m) →
    ∃ X : limO V d 1 ⟶ G, IsLimit x X := by
  intro V _ _ G d x hx
  obtain ⟨g, hg, hg'⟩ := exists_limit_hom (V := V) (κ := Fin 1 × Fin d) G.hom (fun m => (x m).left)
    (fun m => congrArg CommaMorphism.left (hx m))
    (fun m => (Over.w (x m)).trans (Category.comp_id _))
  exact ⟨Over.homMk g (hg.trans (Category.comp_id _).symm), fun m => Over.OverMorphism.ext (hg' m)⟩

end GlobalTheory.TransUnit.LimEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLawsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n m : ℕ) (p q : Matrix (Fin n) (Fin n) O) (x y : Fin n → Pt V m d), (∀ b i, MvPowerSeries.constantCoeff (x b i) ∈ maximalIdeal V) → (∀ b i, MvPowerSeries.constantCoeff (y b i) ∈ maximalIdeal V) → (∀ b i, MvPowerSeries.constantCoeff (matV B p x b i) ∈ maximalIdeal V) ∧ matV B (p * q) x = matV B p (matV B q x) ∧ (matV B p (fun b => addV B.G.F (x b) (y b)) = fun b => addV B.G.F (matV B p x b) (matV B p y b)) ∧ (∀ a : O, matV B (a • (1 : Matrix (Fin n) (Fin n) O)) x = fun b => compV (B.A.act a) (x b)) ∧ (∀ b i, evV x (matV B p (fun j => pt V (n := n) d j) b i) = matV B p x b i) ∧ (∀ b i, MvPowerSeries.constantCoeff (matV B p (fun j => pt V (n := n) d j) b i) = 0) ∧ ∀ f : PS V n d, pullM B (p * q) f = pullM B q (pullM B p f) := by
  first | exact @GlobalTheory.PlaceInt.MatAct.matV_laws | exact GlobalTheory.PlaceInt.MatAct.matV_laws | (intros; apply GlobalTheory.PlaceInt.MatAct.matV_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundIntegralChartRamified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

namespace GlobalTheory.PlaceInt.ChartRam

theorem isRQ_of_not_isUnit (T : CDVR) (N : ℕ) (hN0 : N ≠ 0) (hNu : ¬ IsUnit (N : T.V)) :
    TB.IsRQ (R := T.V) T.Fr := by
  refine ⟨IsFractionRing.injective T.V T.Fr, fun y => ?_⟩
  have hNV0 : (N : T.V) ≠ 0 := by exact_mod_cast hN0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hNV0 hϖ
  have hϖN : ϖ ∣ (N : T.V) := by
    rcases m with _ | m
    · exact absurd (hm.isUnit_iff.2 (by simp)) hNu
    · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T.V) y
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ
  have hsd : s ∣ (N : T.V) ^ n := hn.dvd.trans (pow_dvd_pow_of_dvd hϖN n)
  obtain ⟨c, hc⟩ := hsd
  refine ⟨c * a, N ^ n, pow_pos (Nat.pos_of_ne_zero hN0) n, ?_⟩
  have hsK : algebraMap T.V T.Fr s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]; exact hs0
  have hcast : ((N ^ n : ℕ) : T.Fr) = algebraMap T.V T.Fr ((N : T.V) ^ n) := by
    rw [map_pow, map_natCast]; push_cast; rfl
  rw [hcast, hc, map_mul, map_mul]
  field_simp

theorem vV_natCast_nonneg (T : CDVR) (N : ℕ) (hN0 : N ≠ 0) : 0 ≤ vV T.V (N : T.Fr) := by
  have hr : algebraMap T.V T.Fr (N : T.V) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]
    exact_mod_cast hN0
  have h1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) (N : T.V)
  have h2 : valV T.V (algebraMap T.V T.Fr (N : T.V)) ≠ 0 := valV_ne_zero hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one, map_natCast] at h3
  unfold vV
  omega


set_option maxHeartbeats 1000000 in
theorem chBound_ramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) * (Formalism.L2.Pj.DF Dw w : ℝ) / 2) w n := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hG p a m hp hpu hpm hd hmv e he w n
  refine GlobalTheory.T.harmonicValue_bound_of_column_products E H Dw l Xo c hstar T io y C e _ w n ?_
  intro k P hP f hf
  let _ := io.toAlgebra
  obtain ⟨π, _, _, cc, s, hcs, φ, ψ, hψ, heig, h21a, h21b, h21c⟩ :=
    GlobalTheory.T.exists_ramified_eigen_lifts_of_chart_directions E H Dw l Xo c hstar T io y C hG p a m hp hpu hpm hd hmv e he
  obtain ⟨hF, hA, h1, h2, hs, had, hu⟩ := C.gen.1
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  let t : CVA.IntTie (algebraMap T.V T.Fr) C.ch.B :=
    ⟨C.FT, C.actT, C.ph1T, C.ph2T, C.syT, C.adT, funext fun i => (hF i).symm, fun a => funext fun i => (hA a i).symm,
      h1.symm, h2.symm, hs.symm, fun a => (had a).symm⟩
  have huv : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i) := funext fun ℓ => funext fun i => hu ℓ i
  simp only [huv] at heig h21a h21b h21c
  set cJ : ℝ := (vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E) with hcJ
  have hv : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast vV_natCast_nonneg T p hp.ne_zero
  have hcJ0 : 0 ≤ cJ := by rw [hcJ]; positivity
  have hw0 : H.w0 + star H.w0 = 1 := by rw [hstar]; exact CVA.cmHostUnit_add_conj_eq_one H
  have hpmin : ∀ mo ∈ P.support, ∑ b, TB.pairMin (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1)
      (colL Dw.mult n mo b) ≤ Formalism.L2.Pj.DF Dw w / 2 := fun mo hmo =>
    sum_pairMin_le Dw.mult n cc s (fun τ i => w (τ, i)) mo (hP.1.2.2 mo hmo)
  have hmem := chartValJ (isRQ_of_not_isUnit T p hp.ne_zero hpu) (Jv T e cJ) (one_mem_Jv T e hcJ0)
    (CVA.fbOf t hinj) C.ch.h (CVA.fbOf_canon t hinj C.ch.h C.ch.gauge) H.w0 hw0 k
    Dw.mult ComplexEmbedding.conjugate (fun τ => by ext x; simp) (InPsi H)
    (CVA.inPsi_or H) cc s hcs C.uvecT φ ψ hψ heig h21a h21b h21c n (fun τ i => w (τ, i)) P hP
    (Formalism.L2.Pj.DF Dw w / 2) hpmin f hf
  have hval := mem_Jv_pow T e hcJ0 _ _ hmem
  simp only [CVA.fbOf_nabVal] at hval
  rw [huv]
  refine le_trans ?_ hval
  apply EReal.coe_le_coe_iff.2
  have hdiv : ((Formalism.L2.Pj.DF Dw w / 2 : ℕ) : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self _ 2
  nlinarith

end GlobalTheory.PlaceInt.ChartRam
end

