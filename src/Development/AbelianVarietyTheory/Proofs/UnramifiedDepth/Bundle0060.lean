module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CoeffActAdd
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0049
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
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndomorphismPairW0
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ActionLimit GlobalTheory.ActionEnd

namespace GlobalTheory.ActionEndSelf

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)
variable {d : ℕ} {I : Fin 2 → Type} (X : RawChart C d I (Fin dd))
  (hlg : X.lg = fun i => un1 (Y.lg i)) (hex : X.ex = fun i => un1 (Y.ex i)) (hh : X.h = Y.h)


include hlg hex hh in
theorem isEnd_act_raw (a : O) : IsEnd X V (dLin (Y.B.A.act a)) (dLin (Y.B.A.act (star a))) := by
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  refine isEnd_of_hom_raw Y X hlg hex hh _ _ (g _) (g _) (Y.B.A.hom _) (Y.B.A.hom _) (Y.intAct _) (Y.intAct _) ?_
  have h := Y.gauge.ad a
  rw [actK_self, actK_self] at h
  rw [← h]
  have e : FB.toK C (Y.B.ad a) = Y.B.ad a := by
    show MvPowerSeries.map (RingHom.id C) _ = _
    rw [MvPowerSeries.map_id]; rfl
  rw [e]
  exact Y.intAd a


include hlg hex hh in
theorem gauge_at_linearPart_action_eq_hermitianLift (a : O) : un1 (Y.B.hL C Y.h a) =
    hAt X (endP X 1 (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C))
      (endP X (dLin (Y.B.A.act a)) (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C)) := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
  have q0 : GP (pt C (n := 1) dd 0) := gp_pt 0
  have hs : MvPowerSeries.HasSubst
      (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hX q.2
  have e1 := matrixEnd_eq_subst' Y X hlg hex (pt C dd 0) q0 (by
    rw [germ_comp1_zero_point_left _ (gp_addOf _ Y.B.G.const _ _ p0 p1), germ_comp1_zero_point_left _ p0, germ_comp1_zero_point_left _ p1]) _ hX
  rw [germLinearPart_coordinatePoint_zero] at e1
  have e2 := matrixEnd_eq_subst' Y X hlg hex _ (g a) (Y.B.A.hom a) _ hX
  have e3 : comp1 (Y.B.A.act a) (pt C dd (0 : Fin 1)) = Y.B.A.act a := by
    funext i
    rw [germComp1_eq_subst]
    have : (fun q : Fin 1 × Fin dd => pt C dd (0 : Fin 1) q.2) = MvPowerSeries.X := by
      funext ⟨s, x⟩
      obtain rfl : s = 0 := Subsingleton.elim _ _
      rfl
    rw [this, MvPowerSeries.subst_self]; rfl
  have e4 : un1 (Y.B.hL C Y.h a) = MvPowerSeries.subst
      (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) (Y.B.hL C Y.h a) := by
    rw [← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]; rfl
  rw [e4, FB.hL, actK_self, e3, ev, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 2 × Fin dd => pair_points_zero_constant q0 (g a) q.1 q.2) hs,
    hAt, hh]
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s
  · exact (e1 x).symm
  · exact (e2 x).symm

theorem linear_parts_w0_sum_one : dLin (Y.B.A.act Y.w0) + dLin (Y.B.A.act (star Y.w0)) = 1 := by
  rw [← germLinearPart_coordinatePoint_zero, ← Y.B.A.one_act, ← Y.halfIntegralGenerator_add_conj_eq_one]
  ext i j
  exact (Nab.coeff_act_add Y.B _ _ i j).symm

end Chart

theorem exists_endomorphism_w0 : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∃ W W' : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C, IsEnd (Y.rawSelf p) V W W' ∧ W + W' = 1 ∧ (∀ (v : Fin 2 × Fin dd → C) (x : Fin 2 × Fin dd), W.mulVec v x = linAct (Y.B.A.act Y.w0) (fun i => v (x.1, i)) x.2) ∧ ∑ col : Fin 2, inCol col (un1 (Y.B.hL C Y.h Y.w0)) = hEnd (Y.rawSelf p) 1 W := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  let X : RawChart C d (fun _ => I0) (Fin dd) :=
    { lg := fun i => un1 (Y.lg i), ex := fun i => un1 (Y.ex i), h := Y.h, k := 0, u := fun _ => p.e,
      ty := fun _ => p.ty0, n := 0, j := 0, j' := 0, big := fun _ _ => True }
  have hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0
    rw [constantCoeff_uncurry, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.lg_lin i 0 (by simp)]
    simp
  have hex : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.ex i)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const i
  have hh : MvPowerSeries.constantCoeff X.h = 0 := by
    have := coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl (by
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' _ _ hg']
      rfl) Y.gauge.ax0 0 (by simp)
    simpa using this
  have blk : ∀ M M' : Matrix (Fin dd) (Fin dd) C, M + M' = 1 →
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = y.1 then M x.2 y.2 else 0) +
        (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = y.1 then M' x.2 y.2 else 0) = 1 := by
    intro M M' h
    ext ⟨a, i⟩ ⟨b, j⟩
    have := congrFun (congrFun h i) j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Prod.mk.injEq] at this ⊢
    by_cases hab : a = b
    · simp [hab, this]
    · simp [hab]
  have hone : (1 : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C) =
      fun x y => if x.1 = y.1 then (1 : Matrix (Fin dd) (Fin dd) C) x.2 y.2 else 0 := by
    rw [← blk 1 0 (add_zero _)]
    ext x y
    simp
  refine ⟨_, _, teichSelf_double C V dd d d _ _ X (Y.rawSelf p) hlg hex hh rfl rfl rfl _ _
    (isEnd_act_raw Y X rfl rfl rfl Y.w0), blk _ _ (linear_parts_w0_sum_one Y), fun v x => ?_, ?_⟩
  · show _ = (dLin (Y.B.A.act Y.w0)).mulVec (fun i => v (x.1, i)) x.2
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
      fun i => by simp
    have hX' : ∀ i : Fin 2 × Fin dd,
        MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2 × Fin dd) C) = 0 := fun i => by simp
    have hlg' : ∀ i, MvPowerSeries.constantCoeff ((Y.rawSelf p).lg i) = 0 := fun i =>
      constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hlg _)
    have hex' : ∀ i, MvPowerSeries.constantCoeff ((Y.rawSelf p).ex i) = 0 := fun i =>
      constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hex _)
    unfold hEnd
    rw [hone]
    refine Eq.trans ?_ (teichSelf_hAt_col X (Y.rawSelf p) rfl _ _ (teichSelf_cc_endP _ hlg' hex' _ _ hX')
      (teichSelf_cc_endP _ hlg' hex' _ _ hX')).symm
    refine Finset.sum_congr rfl fun col _ => ?_
    have c : ∀ y : Fin dd, MvPowerSeries.constantCoeff
        (MvPowerSeries.X (col, y) : MvPowerSeries (Fin 2 × Fin dd) C) = 0 := fun _ => hX' _
    rw [gauge_at_linearPart_action_eq_hermitianLift Y X rfl rfl rfl, inCol, teichSelf_subst_hAt X _ _ (teichSelf_cc_endP X hlg hex _ _ hX)
      (teichSelf_cc_endP X hlg hex _ _ hX) _ c]
    simp only [teichSelf_subst_endP X hlg _ _ hX _ c,
      MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero c)]
    congr 1 <;> funext y <;> exact (teichSelf_endP_col X (Y.rawSelf p) hlg rfl rfl _ _ hX' (col, y)).symm

end GlobalTheory.ActionEndSelf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFreeGenerators
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocalFactorFree

private theorem aux {R S M I : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite R M] [Module.Free R M]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) :
    ∃ (h : ℕ) (y : Fin h → M), LinearIndependent R (fun q : I × Fin h => (b q.1 : S) • y q.2) ∧
      ∀ m : M, m ∈ Submodule.span R (Set.range fun q : I × Fin h => (b q.1 : S) • y q.2) ↔ (1 - e) • m = 0 := by
  classical
  let f : LinearMap.range (LinearMap.mulLeft R e) →ₗ[R] (S ⧸ Ideal.span {1 - e}) :=
    (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})).toLinearMap ∘ₗ (Submodule.subtype _)
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨_, s, rfl⟩ hs
      have h1 : e * s ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.1 hs
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
      apply Subtype.ext
      change e * s = 0
      have h2 : e * (e * s) = e * s := by rw [← _root_.mul_assoc, he.eq]
      rw [← h2, ← ht]
      linear_combination t * he.mul_one_sub_self
    · intro a
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      refine ⟨⟨e * s, s, rfl⟩, ?_⟩
      change Ideal.Quotient.mk _ (e * s) = Ideal.Quotient.mk _ s
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton'.2 ⟨-s, by ring⟩
  let bA : Module.Basis I R (S ⧸ Ideal.span {1 - e}) := b.map (LinearEquiv.ofBijective f hf)
  haveI : Module.Finite R (S ⧸ Ideal.span {1 - e}) := Module.Finite.of_basis bA
  haveI : Module.Free R (S ⧸ Ideal.span {1 - e}) := Module.Free.of_basis bA
  let N : Submodule S M := Submodule.torsionBy S M (1 - e)
  haveI : Module.Finite R N := Module.Finite.of_injective (N.subtype.restrictScalars R) Subtype.val_injective
  letI : Module (S ⧸ Ideal.span {1 - e}) N := inferInstanceAs (Module (S ⧸ Submodule.span S {1 - e}) (Submodule.torsionBy S M (1 - e)))
  have hsm : ∀ (s : S) (n : N), (Ideal.Quotient.mk (Ideal.span {1 - e}) s) • n = s • n := fun _ _ => rfl
  haveI : IsScalarTower R (S ⧸ Ideal.span {1 - e}) N := ⟨fun r a n => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : r • Ideal.Quotient.mk (Ideal.span {1 - e}) s = Ideal.Quotient.mk (Ideal.span {1 - e}) (r • s) := rfl
    rw [this, hsm, hsm, smul_assoc]⟩
  haveI : Module.Finite (S ⧸ Ideal.span {1 - e}) N := Module.Finite.of_restrictScalars_finite R _ _
  haveI : Module.IsTorsionFree (S ⧸ Ideal.span {1 - e}) N := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a n han
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
    have h1 : r • n = 0 := by
      rw [← algebraMap_smul (S ⧸ Ideal.span {1 - e}) r n, hc, mul_comm, mul_smul, han, smul_zero]
    have h2 : r • (n : M) = 0 := congrArg Subtype.val h1
    exact Subtype.ext ((smul_eq_zero.1 h2).resolve_left hr)
  let y := Module.finBasis (S ⧸ Ideal.span {1 - e}) N
  let B := bA.smulTower y
  have hB : (fun q : I × Fin _ => (b q.1 : S) • (y q.2 : M)) = (N.subtype.restrictScalars R) ∘ B := by
    funext q
    simp only [B, Function.comp, Module.Basis.smulTower_apply]
    rfl
  refine ⟨_, fun j => (y j : M), ?_, fun m => ?_⟩
  · rw [hB]
    exact B.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · rw [hB, Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨n, rfl⟩
      exact n.2
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩

private theorem aux2 {R S I κ : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [Fintype κ] [DecidableEq κ]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) (ρ : S →ₐ[R] Matrix κ κ R) :
    ∃ (h : ℕ) (y : Fin h → κ → R), LinearIndependent R (fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) ∧
      Submodule.span R (Set.range fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) =
        LinearMap.range (Matrix.mulVecLin (ρ e)) := by
  letI : Module S (κ → R) := Module.compHom (κ → R) (ρ : S →+* Matrix κ κ R)
  have hsm : ∀ (s : S) (v : κ → R), s • v = ρ s *ᵥ v := fun _ _ => rfl
  haveI : IsScalarTower R S (κ → R) := ⟨fun r s v => by
    rw [hsm, hsm, map_smul, Matrix.smul_mulVec]⟩
  obtain ⟨h, y, h1, h2⟩ := aux (M := κ → R) e he b
  refine ⟨h, y, h1, ?_⟩
  ext m
  refine (h2 m).trans ⟨fun hm => ⟨m, ?_⟩, ?_⟩
  · change e • m = m
    rw [sub_smul, one_smul, sub_eq_zero] at hm
    exact hm.symm
  · rintro ⟨v, rfl⟩
    change (1 - e) • e • v = 0
    rw [← mul_smul, he.one_sub_mul_self, zero_smul]

theorem exists_free_generators : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]), ∃ (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) ∧ Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) := by
  intro p _ OE _ _ _ _ _ w b κ _ _ ρ
  obtain ⟨h1, h2, -⟩ := _root_.GlobalTheory.PlaceMono.place_monogenic p OE w
  exact aux2 w.e w.idem b ρ

end GlobalTheory.LocalFactorFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupSeriesSeparatedByTorsion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem mem_span_of_killed {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) (N : ℕ)
    (h : ∀ q : QF F N, (∀ φ : QF F N →ₐ[R] R, φ q = 0) → q = 0) (f : PS R 1 d)
    (hf : ∀ φ, Killed F N φ → φ f = 0) : f ∈ Ideal.span (Set.range (mulF F N)) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine h _ fun φ => ?_
  refine hf (φ.comp (Ideal.Quotient.mkₐ R _)) fun j => ?_
  have : Ideal.Quotient.mk (Ideal.span (Set.range (mulF F N))) (mulF F N j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
  simp [this]

theorem mem_span_mulF_of_killed_and_eq_zero_of_tors : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → (∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) → f ∈ Ideal.span (Set.range (mulF F.F (p ^ k)))) ∧ ∀ f : PS O 1 d, (∀ φ, Tors p F.F φ → φ f = 0) → f = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hc d F hFH
  have h1 : ∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) →
      f ∈ Ideal.span (Set.range (mulF F.F (p ^ k))) :=
    fun k f hf => mem_span_of_killed F.F (p ^ k) (hFH k).2.2 f hf
  refine ⟨h1, fun f hf => ?_⟩
  have hH := ((mem_sup_span_X_pow_iff_and_isAdicComplete O (Ideal.span {(p : O)}) (Fin 1 × Fin d)).2
    hc).toIsHausdorff
  refine hH.haus f fun k => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  refine (Ideal.span_le.2 ?_) (h1 k f fun φ hφ => hf φ ⟨k, hφ⟩)
  rintro _ ⟨j, rfl⟩
  exact (_root_.GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow O d F).2.2.2 p k j

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsAddCommMonoidStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst; (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧ (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧ ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  first | exact @GlobalTheory.FormalPts.points_addCommMonoid | exact GlobalTheory.FormalPts.points_addCommMonoid | (intros; apply GlobalTheory.FormalPts.points_addCommMonoid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AddCurve

section Rings
variable (R : Type) [CommRing R] (l : ℕ)

abbrev Tr : Type := AdjoinRoot (Polynomial.X ^ l : Polynomial R)

variable {R l}

def cf (n : ℕ) : Tr R l →ₗ[R] R := (Polynomial.lcoeff R n).comp (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow l))

variable (R l)

end Rings

section Points
variable {k : Type} [CommRing k]

variable {B : Over (Spec (CommRingCat.of k))}

variable {R : Type} [CommRing R] [Algebra k R]

end Points

end GlobalTheory.AddCurve
end
end

