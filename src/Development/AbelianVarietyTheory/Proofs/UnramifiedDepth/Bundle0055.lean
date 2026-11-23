module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralSeriesFrameEqProdRows
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal.PlaneRead

open MvPowerSeries EndCalc

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}

def expAt (X : RawChart C d I κ) {ω : Type} [Fintype ω] (v : ω → κ → C) : κ → MvPowerSeries ω C :=
  fun x => subst (fun i : κ => ∑ w, v w i • (MvPowerSeries.X w : MvPowerSeries ω C)) (X.ex x)

theorem comb_cc {ι ω : Type} [Fintype ι] (c : ι → C) (φ : ι → ω) :
    constantCoeff (∑ w, c w • (MvPowerSeries.X (φ w) : MvPowerSeries ω C)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [constantCoeff_smul, constantCoeff_X, smul_zero]

theorem expAt_cc (H : RLaw X V) {ω : Type} [Fintype ω] (v : ω → κ → C) (x : κ) :
    constantCoeff (expAt X v x) = 0 := by
  unfold expAt
  rw [cc_subst (fun i => comb_cc (fun w => v w i) (fun w => w)), H.exc]

theorem subst_endomorphismSeries_expAt (H : RLaw X V) {ω : Type} [Fintype ω] (v : ω → κ → C) (A : Matrix κ κ C) (i : κ) :
    subst (expAt X v) (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i) =
      expAt X (fun w => A.mulVec (v w)) i := by
  rw [subst_endP H (fun s => constantCoeff_X s) (expAt_cc H v)]
  simp only [subst_X (hasSubst_of_constantCoeff_zero (expAt_cc H v))]
  have hl : ∀ y, subst (expAt X v) (X.lg y) = ∑ w, v w y • (MvPowerSeries.X w : MvPowerSeries ω C) :=
    fun y => lg_ex H (fun i => comb_cc (fun w => v w i) (fun w => w)) y
  unfold endP
  simp only [hl]
  unfold expAt
  congr 1
  funext x
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem subst_hEnd_expAt (H : RLaw X V) {ω : Type} [Fintype ω] (v : ω → κ → C) (A B : Matrix κ κ C) :
    subst (expAt X v) (hEnd X A B) =
      hAt X (expAt X (fun w => A.mulVec (v w))) (expAt X (fun w => B.mulVec (v w))) := by
  unfold hEnd
  rw [subst_hAt (constantCoeff_expMulLog H (fun s => constantCoeff_X s) A) (constantCoeff_expMulLog H (fun s => constantCoeff_X s) B) (expAt_cc H v)]
  simp only [subst_endomorphismSeries_expAt H]

theorem hEnd_cc (H : RLaw X V) (A B : Matrix κ κ C) : constantCoeff (hEnd X A B) = 0 :=
  hAt_cc H (constantCoeff_expMulLog H (fun s => constantCoeff_X s) A) (constantCoeff_expMulLog H (fun s => constantCoeff_X s) B)

end GlobalTheory.RowVal.PlaneRead

namespace GlobalTheory.RowVal

open PlaneRead EndCalc

theorem exists_intS_frame_eq_prod : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (Orb : Type) [Fintype Orb] (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : ∀ o, RawChart C d (I o) κ) (d₀ : ℕ) (I₀ : Fin 2 → Type) [∀ g, Fintype (I₀ g)] (X₀ : RawChart C d₀ I₀ κ), RLaw X₀ V → (∀ o, (X o).ex = X₀.ex ∧ (X o).h = X₀.h ∧ (X o).k = X₀.k) → ∀ (π : Orb → Fin 2 → Matrix κ κ C) (W : Matrix κ κ C), (∀ o g, IntEnd X₀ V (π o g)) → (∀ o g c, (π o g).mulVec ((X o).u g c) = (X o).u g c) → (∀ o g o' g' c, (o, g) ≠ (o', g') → (π o g).mulVec ((X o').u g' c) = 0) → (∑ o, hEnd X₀ (π o 0) (π o 1)) - hEnd X₀ (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ → ∀ gr : ∀ o, MvPowerSeries (WV (I o)) C, (∀ o, gr o ∈ ExpInt (X o) V) → ∃ F : MvPowerSeries κ C, IntS V F ∧ MvPowerSeries.subst (fun x : κ => MvPowerSeries.subst (fun i : κ => ∑ w : WVO I, (X w.1).u w.2.1 w.2.2 i • (MvPowerSeries.X w : MvPowerSeries (WVO I) C)) (X₀.ex x)) (F * mvExp ((X₀.k : C) • hEnd X₀ 1 W)) = ∏ o, MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) (gr o * mvExp (X o).hRow) := by
  intro C _ _ V d Orb _ I _ κ _ _ X d₀ I₀ _ X₀ H hX π W hπ hfix hkill hD gr hgr
  classical
  choose f hf hgf using hgr
  let u : WVO I → κ → C := fun w => (X w.1).u w.2.1 w.2.2
  set P : Matrix κ κ C := ∑ o, ∑ g, π o g with hP
  set D := (∑ o, hEnd X₀ (π o 0) (π o 1)) - hEnd X₀ P (W * P) with hDdef
  have cX : ∀ s : κ, MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries κ C) = 0 :=
    fun s => MvPowerSeries.constantCoeff_X s
  have cπ : ∀ o (p : Fin 2 × κ), MvPowerSeries.constantCoeff
      (endP X₀ (π o p.1) (MvPowerSeries.X : κ → MvPowerSeries κ C) p.2) = 0 := fun o p => constantCoeff_expMulLog H cX _ _
  have hkD : (X₀.k : C) • D ∈ logInt V κ := by
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hD _
  let r : ∀ o, WV (I o) → MvPowerSeries (WVO I) C := fun o w => MvPowerSeries.X (⟨o, w⟩ : WVO I)
  have cr : ∀ o w, MvPowerSeries.constantCoeff (r o w) = 0 := fun o w => MvPowerSeries.constantCoeff_X _
  have hr := fun o => MvPowerSeries.hasSubst_of_constantCoeff_zero (cr o)
  have ce := expAt_cc H u
  have he := MvPowerSeries.hasSubst_of_constantCoeff_zero ce
  have cE : ∀ o (p : Fin 2 × κ), MvPowerSeries.constantCoeff ((X o).expPt p.1 p.2) = 0 := by
    intro o p
    unfold RawChart.expPt
    rw [cc_subst (fun i => comb_cc (fun c => (X o).u p.1 c i) (fun c => (⟨p.1, c⟩ : WV (I o)))), (hX o).1, H.exc]
  have hpt : ∀ o g x, expAt X₀ (fun w => (π o g).mulVec (u w)) x =
      MvPowerSeries.subst (r o) ((X o).expPt g x) := by
    intro o g x
    unfold RawChart.expPt expAt
    rw [comp_cc (fun i => comb_cc (fun c => (X o).u g c i) (fun c => (⟨g, c⟩ : WV (I o)))) (cr o), (hX o).1]
    congr 1
    funext i
    rw [subst_lin (cr o), Fintype.sum_sigma, Finset.sum_eq_single o, Fintype.sum_sigma, Finset.sum_eq_single g]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [MvPowerSeries.subst_X (hr o)]
      show (π o g).mulVec ((X o).u g c) i • _ = _
      rw [hfix]
    · intro g' _ hg
      refine Finset.sum_eq_zero fun c _ => ?_
      show (π o g).mulVec ((X o).u g' c) i • _ = _
      rw [hkill o g o g' c (by simp [Ne.symm hg]), Pi.zero_apply, zero_smul]
    · simp
    · intro o' _ ho
      refine Finset.sum_eq_zero fun c _ => ?_
      show (π o g).mulVec ((X o').u c.1 c.2) i • _ = _
      rw [hkill o g o' c.1 c.2 (by simp [Ne.symm ho]), Pi.zero_apply, zero_smul]
    · simp
  have hPu : ∀ w, P.mulVec (u w) = u w := by
    rintro ⟨o, g, c⟩
    show P.mulVec ((X o).u g c) = (X o).u g c
    rw [hP, Matrix.sum_mulVec, Finset.sum_eq_single o, Matrix.sum_mulVec, Finset.sum_eq_single g, hfix]
    · intro g' _ hg
      exact hkill o g' o g c (by simp [hg])
    · simp
    · intro o' _ ho
      rw [Matrix.sum_mulVec]
      exact Finset.sum_eq_zero fun g' _ => hkill o' g' o g c (by simp [ho])
    · simp
  have h1 : MvPowerSeries.subst (expAt X₀ u) (hEnd X₀ P (W * P)) =
      MvPowerSeries.subst (expAt X₀ u) (hEnd X₀ 1 W) := by
    simp only [subst_hEnd_expAt H, ← Matrix.mulVec_mulVec, hPu, Matrix.one_mulVec]
  have h2 : ∀ o, (X₀.k : C) • MvPowerSeries.subst (expAt X₀ u) (hEnd X₀ (π o 0) (π o 1)) =
      MvPowerSeries.subst (r o) (X o).hRow := by
    intro o
    unfold RawChart.hRow
    rw [MvPowerSeries.subst_smul (hr o), comp_cc (cE o) (cr o), subst_hEnd_expAt H, (hX o).2.1, (hX o).2.2]
    unfold hAt
    congr 2
    funext p
    obtain ⟨g, x⟩ := p
    fin_cases g
    · simpa using hpt o 0 x
    · simpa using hpt o 1 x
  have cH : ∀ o, MvPowerSeries.constantCoeff (X o).hRow = 0 := by
    intro o
    unfold RawChart.hRow
    rw [MvPowerSeries.constantCoeff_smul, cc_subst (cE o), (hX o).2.1, h_cc H, smul_zero]
  have c1 : MvPowerSeries.constantCoeff ((X₀.k : C) • hEnd X₀ 1 W) = 0 := by
    rw [MvPowerSeries.constantCoeff_smul, hEnd_cc H, smul_zero]
  have h3 : MvPowerSeries.subst (expAt X₀ u) ((X₀.k : C) • D + (X₀.k : C) • hEnd X₀ 1 W) =
      ∑ o, MvPowerSeries.subst (r o) (X o).hRow := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← smul_add, MvPowerSeries.subst_smul he, MvPowerSeries.subst_add he, ← h1, ← MvPowerSeries.subst_add he,
      hDdef, sub_add_cancel, ← MvPowerSeries.substAlgHom_apply he, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [MvPowerSeries.substAlgHom_apply, h2]
  refine ⟨(∏ o, MvPowerSeries.subst (fun p : Fin 2 × κ =>
    endP X₀ (π o p.1) (MvPowerSeries.X : κ → MvPowerSeries κ C) p.2) (f o)) * mvExp ((X₀.k : C) • D),
    intS_mul (intS_prod _ fun o => intS_subst (cπ o) (fun p => hπ o p.1 p.2) (hf o)) hkD.2, ?_⟩
  show MvPowerSeries.subst (expAt X₀ u) _ = ∏ o, MvPowerSeries.subst (r o) _
  rw [mul_assoc, ← mvExp_add hkD.1 c1, MvPowerSeries.subst_mul he,
    subst_mvExp ce (by rw [map_add (f := _), hkD.1, c1, add_zero]), h3,
    mvExp_sum _ (fun o => by rw [cc_subst (cr o), cH]), ← MvPowerSeries.substAlgHom_apply he, map_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_mul (hr o), subst_mvExp (cr o) (cH o), hgf o,
    comp_cc (cπ o) ce, comp_cc (cE o) (cr o)]
  simp only [subst_endomorphismSeries_expAt H, hpt]

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTangentChartMatrixOfBasis
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

open GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing in
private theorem ker_red_eq {R₀ : Type} [CommRing R₀] (O : LAlg R₀) (x : (dual O : Type))
    (hx : (red O).1 x = 0) :
    x = (incl O).1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * eta O := by
  have key : ∀ b : DualNumber (O : Type), TrivSqZeroExt.fst b = 0 →
      b = (TrivSqZeroExt.inl (TrivSqZeroExt.snd b) : DualNumber (O : Type)) * DualNumber.eps :=
    fun b hb => by ext <;> simp [hb]
  exact key x hx

private def liftAlg {R₀ : Type} [CommRing R₀] {O R : Type} [CommRing O] [CommRing R] [Algebra R₀ O]
    [Algebra R₀ R] (s : O →ₐ[R₀] R) (i : R) (hi : i * i = 0) : DualNumber O →ₐ[R₀] R where
  toFun x := s x.fst + s x.snd * i
  map_one' := by simp
  map_mul' x y := by
    simp only [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, map_mul, map_add (f := _)]
    linear_combination (-(s x.snd * s y.snd)) * hi
  map_zero' := by simp
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add (f := _)]; ring
  commutes' r := by simp [TrivSqZeroExt.algebraMap_eq_inl']

open GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing in
private theorem exists_lift {R₀ : Type} [CommRing R₀] {O R : LAlg R₀} (s : LHom O R) (i : (R : Type))
    (hi : i * i = 0) : ∃ f : LHom (dual O) R, f.comp (incl O) = s ∧ f.1 (eta O) = i := by
  refine ⟨⟨liftAlg s.1 i hi, ⟨fun x hx => ?_⟩⟩, Subtype.ext (AlgHom.ext fun x => ?_), ?_⟩
  · have hx' : IsUnit (s.1 (TrivSqZeroExt.fst (R := (O : Type)) (M := (O : Type)) x) +
      s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * i) := hx
    have hn : IsNilpotent (-(s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * i)) :=
      ⟨2, by linear_combination (s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x)) ^ 2 * hi⟩
    have h2 := hn.isUnit_add_left_of_commute hx' (Commute.all _ _)
    rw [add_neg_cancel_right] at h2
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (s.2.map_nonunit _ h2)
  · change s.1 x + s.1 0 * i = s.1 x
    simp
  · change s.1 0 + s.1 1 * i = i
    simp

private theorem chart_add {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ}
    {F : FGLaw (O : Type) g} {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R}
    (h : BXChart B O F.F Y) (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0)
    (a b : Fin g → (R : Type)) :
    Y R s (fun k => a k * e) + Y R s (fun k => b k * e) = Y R s (fun k => (a k + b k) * e) := by
  have hn : ∀ c : (R : Type), IsNilpotent (c * e) := fun c => ⟨2, by linear_combination c ^ 2 * he⟩
  have key : ∀ (a b : Fin g → (R : Type)) (k : Fin g),
      nv s.1.toRingHom (F.F k) ![fun k => a k * e, fun k => b k * e] =
        (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (F.F k)) * a j +
          ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (F.F k)) * b j) * e := by
    intro a b k
    have h1 := (nv_calculus _ _ s.1.toRingHom 2 g ![fun k => a k * e, fun k => b k * e]
      (fun i j => by fin_cases i <;> exact hn _)).2.2.2.2.2 (fun i j i' j' => by
        have : ∀ c d : (R : Type), c * e * (d * e) = 0 := fun c d => by linear_combination c * d * he
        fin_cases i <;> fin_cases i' <;> exact this _ _) (F.F k)
    rw [h1, F.const, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_two, add_mul,
      Finset.sum_mul, Finset.sum_mul]
    simp [_root_.mul_assoc]
  have law : ∀ a b : Fin g → (R : Type), Y R s (fun k => a k * e) + Y R s (fun k => b k * e) =
      Y R s (fun k => (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (F.F k)) * a j +
          ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (F.F k)) * b j) * e) := by
    intro a b
    rw [h.law R s _ _ (fun _ => hn _) (fun _ => hn _)]
    simp only [key]
  have hz : Y R s (fun k => (0 : Fin g → (R : Type)) k * e) = 0 := by
    rw [← h.zero R s]; congr 1; funext k; simp
  have ha := law a 0
  have hb := law 0 b
  rw [hz, add_zero] at ha
  rw [hz, zero_add] at hb
  have ha' := h.inj R s _ _ (fun _ => hn _) (fun _ => hn _) ha
  have hb' := h.inj R s _ _ (fun _ => hn _) (fun _ => hn _) hb
  rw [law]
  congr 1
  funext k
  have h1 := congrFun ha' k
  have h2 := congrFun hb' k
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at h1 h2
  rw [add_mul, add_mul, ← h1, ← h2]


open GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing in
theorem exists_tanMat : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ gb : Module.Basis (Fin g) R₀ B.gg, ∃ S : Matrix (Fin g) (Fin g) (O : Type), IsUnit S ∧ TanMat B O Y gb S := by
  intro R₀ _ B O g F Y h gb
  have hee := eta_mul_eta O
  have hn : ∀ c : (dual O : Type), IsNilpotent (c * eta O) :=
    fun c => ⟨2, by linear_combination c ^ 2 * hee⟩
  have hη : (red O).1 (eta O) = 0 := rfl
  have hex : ∀ l, ∃ a : Fin g → (dual O : Type), (∀ i, (red O).1 (a i) = 0) ∧
      B.tg (red O) (red_sqZero O) (gb l ⊗ₜ[R₀] ⟨eta O, hη⟩) = Y (dual O) (incl O) a := fun l =>
    h.surj (dual O) O (incl O) (red O) (incl O) (red_comp_incl O) (by rw [red_comp_incl]; rfl)
      (red_sqZero O) _ ((B.tg_ker _ _ _).2 ⟨_, rfl⟩)
  choose a ha0 ha using hex
  let S : Matrix (Fin g) (Fin g) (O : Type) :=
    Matrix.of fun k l => TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) (a l k)
  have haS : ∀ l, a l = fun k => (incl O).1 (S k l) * eta O := fun l =>
    funext fun k => ker_red_eq O _ (ha0 l k)
  have hT : TanMat B O Y gb S := by
    intro R R' s π hπ l i
    have hi : (i : (R : Type)) * i = 0 := by
      have : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul i.2 i.2
      rwa [hπ.2, Ideal.mem_bot] at this
    obtain ⟨f, hf1, hf2⟩ := exists_lift s (i : (R : Type)) hi
    have hf : ∀ x ∈ (red O).ker, f.1.toLinearMap x ∈ π.ker := fun x hx => by
      rw [ker_red_eq O x hx]
      change π.1 (f.1 (_ * _)) = 0
      have hi0 : π.1 (i : (R : Type)) = 0 := i.2
      rw [map_mul, map_mul, hf2, hi0, mul_zero]
    have h1 := B.tg_nat (red O) π (red_sqZero O) hπ f hf (gb l ⊗ₜ[R₀] ⟨eta O, hη⟩)
    rw [ha, haS, h.nat _ _ _ _ _ (fun _ => hn _), hf1, LinearMap.lTensor_tmul] at h1
    have h2 : (f.1.toLinearMap.restrict hf) ⟨eta O, hη⟩ = i := Subtype.ext hf2
    rw [h2] at h1
    rw [h1]
    congr 1
    funext k
    rw [map_mul, hf2, ← hf1]
    rfl
  refine ⟨S, Matrix.mulVec_surjective_iff_isUnit.1 fun v => ?_, hT⟩
  have hP : ∀ w, ∃ c : Fin g → (O : Type), B.tg (red O) (red_sqZero O) w =
      Y (dual O) (incl O) (fun k => (incl O).1 ((S *ᵥ c) k) * eta O) := by
    let P : B.G (dual O) → Prop := fun x => ∃ c : Fin g → (O : Type),
      x = Y (dual O) (incl O) (fun k => (incl O).1 ((S *ᵥ c) k) * eta O)
    have P0 : P 0 := ⟨0, by rw [← h.zero (dual O) (incl O)]; congr 1; funext k; simp⟩
    have Padd : ∀ x y, P x → P y → P (x + y) := by
      rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
      refine ⟨c + c', ?_⟩
      rw [chart_add h _ _ _ hee]
      simp only [Matrix.mulVec_add, Pi.add_apply, map_add (f := _)]
    intro w
    change P _
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact P0
    | add x y hx hy => rw [map_add (f := _)]; exact Padd _ _ hx hy
    | tmul m i =>
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← gb.sum_repr m, TensorProduct.sum_tmul, map_sum]
      refine Finset.sum_induction _ P Padd P0 fun l _ => ?_
      rw [TensorProduct.smul_tmul]
      generalize (gb.repr m l) • i = j
      refine ⟨Pi.single l (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) j.1), ?_⟩
      rw [hT]
      congr 1
      funext k
      rw [Matrix.mulVec_single]
      simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.smul_apply, Matrix.col_apply,
        map_mul, _root_.mul_assoc]
      rw [← ker_red_eq O j.1 j.2]
  have hx : B.map (red O) (Y (dual O) (incl O) (fun k => (incl O).1 (v k) * eta O)) = 0 := by
    rw [h.nat _ _ _ _ _ (fun _ => hn _), ← h.zero O ((red O).comp (incl O))]
    congr 1
    funext k
    rw [map_mul, hη, mul_zero]; rfl
  obtain ⟨w, hw⟩ := (B.tg_ker _ (red_sqZero O) _).1 hx
  obtain ⟨c, hc⟩ := hP w
  have h3 := h.inj _ _ _ _ (fun _ => hn _) (fun _ => hn _) (hc.symm.trans hw)
  refine ⟨c, funext fun k => ?_⟩
  have h4 := congrArg (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type))) (congrFun h3 k)
  have key : ∀ t : (O : Type), TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type))
      ((incl O).1 t * eta O) = t := fun t => by
    have : TrivSqZeroExt.snd ((TrivSqZeroExt.inl t : DualNumber (O : Type)) *
      (DualNumber.eps : DualNumber (O : Type))) = t := by simp
    exact this
  rwa [key, key] at h4

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusMemTypicalCurveSet
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.FrobCurve

variable {C : Type} [Field C]

theorem sum_rescale_tyS {l : ℕ} (hl : l.Prime) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l fun s => (l : C) * a (s + 1)) =
      ∑ j ∈ Finset.range l, PowerSeries.rescale (ζ ^ j) (tyS l a) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, PowerSeries.coeff_rescale, ← Finset.sum_mul]
  by_cases hn : l ∣ n
  · obtain ⟨q, rfl⟩ := hn
    have h1 : ∑ j ∈ Finset.range l, (ζ ^ j) ^ (l * q) = (l : C) := by
      have : ∀ j, (ζ ^ j) ^ (l * q) = 1 := fun j => by
        rw [← pow_mul, mul_left_comm, pow_mul, hζ.pow_eq_one, one_pow]
      simp [this]
    rw [h1, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hl.pos]
    by_cases hq : ∃ s, l ^ s = q
    · obtain ⟨s, rfl⟩ := hq
      rw [coeff_tyS_pow hl.two_le, ← pow_succ', coeff_tyS_pow hl.two_le]
    · push Not at hq
      rw [coeff_tyS_of_ne _ _ hq, coeff_tyS_of_ne, mul_zero]
      intro s hs
      cases s with
      | zero =>
        rw [pow_zero] at hs
        exact hl.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hs.symm)
      | succ s =>
        rw [pow_succ'] at hs
        exact hq s (Nat.eq_of_mul_eq_mul_left hl.pos hs)
  · have hc : n.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hn).symm
    have h0 : ∑ j ∈ Finset.range l, (ζ ^ j) ^ n = 0 := by
      rw [← (hζ.pow_of_coprime n hc).geom_sum_eq_zero hl.one_lt]
      exact Finset.sum_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h0, zero_mul, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow_of_not_dvd hl.pos _ _ hn]

theorem ge_zero_of_pow_eq_one (V : VF C) {ζ : C} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) : V.Ge 0 ζ := by
  have h1 : n • V.v ζ = 0 := by rw [← V.v.map_pow, h, V.v.map_one]
  unfold VF.Ge
  induction hv : V.v ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe r =>
    rw [hv, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, nsmul_eq_mul] at h1
    have : r = 0 := (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn.ne')
    rw [this]

theorem rescale_smul' (s c : C) (f : PowerSeries C) :
    PowerSeries.rescale s (c • f) = c • PowerSeries.rescale s f := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem frob_mem_tySet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g := by
  classical
  intro C _ V d _ I _ κ _ X hX g x hx
  haveI := hX.charZero
  haveI := hX.closed
  have hl := V.l_prime
  haveI : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  haveI : NeZero V.l := ⟨hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  obtain ⟨h0, hadd, -, hres⟩ := _root_.GlobalTheory.RowLaw.cv_group C V d I κ X hX g
  let lo : (I g ⊕ JJ I g → PowerSeries C) → (κ → PowerSeries C) × (JJ I g → PowerSeries C) := fun A =>
    (fun i => ∑ c : I g, X.u g c i • A (Sum.inl c),
     fun q => A (Sum.inr q) - ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • A (Sum.inl c) else 0)
  have hiff : ∀ y : ℕ → I g ⊕ JJ I g → C,
      y ∈ X.TySet V g ↔ lo (fun n => tyS V.l fun s => y s n) ∈ Cv X V g := fun y => by
    constructor
    · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
      exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.2 (h2 q)⟩
    · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
      exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.1 (h2 q)⟩
  have hsum : ∀ (M : ℕ) (f : ℕ → (κ → PowerSeries C) × (JJ I g → PowerSeries C)),
      (∀ j, f j ∈ Cv X V g) → ∑ j ∈ Finset.range M, f j ∈ Cv X V g := fun M f hf =>
    Finset.sum_induction f (· ∈ Cv X V g) (fun a b ha hb => hadd a ha b hb) h0 fun j _ => hf j
  have hint : ∀ j, V.Ge 0 (ζ ^ j) := fun j => (ge_zero_of_pow_eq_one V hl.pos hζ.pow_eq_one).pow j
  have hS := hsum V.l _ fun j => hres (ζ ^ j) (hint j) _ ((hiff x).1 hx)
  rw [hiff]
  refine GlobalTheory.RowLaw.mem_Cv_of_subst_X_pow C V d I κ X hX g V.l hl.pos _ ?_
  have hsub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ V.l) :=
    PowerSeries.HasSubst.X_pow hl.ne_zero
  have key : ∀ n, PowerSeries.substAlgHom (R := C) hsub (tyS V.l fun s => Fs V.l x s n) =
      ∑ j ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ j) (tyS V.l fun s => x s n) := fun n => by
    rw [PowerSeries.coe_substAlgHom]
    exact sum_rescale_tyS hl hζ fun s => x s n
  convert hS using 1
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [lo, Prod.fst_sum, Finset.sum_apply, ← PowerSeries.coe_substAlgHom hsub, map_sum, map_smul, key,
      rescale_smul', Finset.smul_sum]
      exact Finset.sum_comm
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [lo, Prod.snd_sum, Finset.sum_apply, ← PowerSeries.coe_substAlgHom hsub, map_sum, map_sub, key,
      Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs
      · simp only [map_smul, key, rescale_smul', Finset.smul_sum]
      · simp

end GlobalTheory.RowLaw.FrobCurve
end

