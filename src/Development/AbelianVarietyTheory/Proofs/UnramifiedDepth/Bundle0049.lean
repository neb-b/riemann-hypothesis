module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ValOfKindIndep
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubstSame
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ActionConvergesLadicCauchyAndStar
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartLiftSquareZeroUnitPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_lift_square_zero_unit_point : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S], Kills I k S → ∀ (S' : Type) [CommRing S'] [Algebra R S'] (ρ : S →ₐ[R] S') (σ : S' →ₐ[R] S), ρ.comp σ = AlgHom.id R S' → RingHom.ker ρ ^ 2 = ⊥ → ∀ y : sp (R₀ := R) S ⟶ D.P.A, spMap ρ ≫ y = 1 → ∃ z : sp (R₀ := R) S ⟶ G, spMap ρ ≫ z = 1 ∧ QRel c S z y := by
  first | exact @GlobalTheory.ChF.qRel_lift | exact GlobalTheory.ChF.qRel_lift | (intros; apply GlobalTheory.ChF.qRel_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdmissibleRowsValueEqRowGauge
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal

open GlobalTheory.RowValueCheck

theorem valOf_eq_hRow : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ) (H : X.Hyps V) (N : ℕ) (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d)), RowsOK (X.rowData H).G (X.rowData H).Alt P kind → ∀ gr : Fin N → MvPowerSeries (WV I) C, ValOf (X.rowData H).hL P kind gr = jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ X.hRow))) := by
  intro C _ V d _ I _ κ _ X H N P kind hk gr
  classical
  rw [valOf_eq]
  set S : Set (Fin N × WV I) := {x | ∃ μ ∈ P.support, μ x ≠ 0} with hS
  have key : ∀ ρ, Agree {w | (ρ, w) ∈ S} (hOf (X.rowData H).hL (kind ρ)) X.hRow := by
    intro ρ μ hμ
    rcases hr : kind ρ with _ | ⟨g, a, a'⟩
    · obtain ⟨g, hg⟩ := hk.2 ρ hr
      have h1 : ∀ w, μ w ≠ 0 → w.1 = g := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hg ν hν w hν'
      show (0 : C) = _
      refine (H.axes μ ?_).symm
      have hg2 : g = 0 ∨ g = 1 := (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) g
      rcases hg2 with rfl | rfl
      · exact Or.inl fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
      · exact Or.inr fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
    · obtain ⟨-, -, hl⟩ := hk.1 ρ g a a' hr
      have h1 : ∀ w, μ w ≠ 0 → X.OnLf g a a' w := fun w hw => by
        obtain ⟨ν, hν, hν'⟩ := hμ w hw
        exact hl ν hν w hν'
      exact if_pos fun w hw => h1 w (Finsupp.mem_support_iff.1 hw)
  have hA := Agree.prod (S := S) Finset.univ (fun ρ =>
    Agree.mul (F := rowCopy ρ (gr ρ)) (F' := rowCopy ρ (gr ρ)) (fun _ _ => rfl)
      (agree_rowCopy S ρ _ _ (key ρ)).exp)
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [hA μ fun x hx => ⟨μ, hμ, hx⟩]

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDerivationPolynomialEqJetAt0
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.DerivJet

variable {C : Type} [Field C] {W : Type} [Fintype W]

theorem jetAt0_mul_lin (c : W → C) (Q : MvPolynomial W C) (G : MvPowerSeries W C) :
    jetAt0 (Q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X w) G =
      jetAt0 Q (∑ w, c w • MvPowerSeries.pderiv (R := C) w G) := by
  rw [Finset.mul_sum, GlobalTheory.MinorShiftJet.jetAt0_sum_left, GlobalTheory.MinorShiftJet.jetAt0_sum_smul_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_left_comm, GlobalTheory.MinorShiftJet.jetAt0_C_mul, GlobalTheory.MinorShiftJet.jetAt0_mul_X]

theorem jetAt0_iterate {A : Type} (S : A → MvPowerSeries W C) (D : A → A) (c : W → C) (k : ℕ)
    (h : k ≠ 0 → ∀ G, S (D G) = ∑ w, c w • MvPowerSeries.pderiv (R := C) w (S G)) (Q : MvPolynomial W C) (G : A) :
    jetAt0 Q (S (D^[k] G)) = jetAt0 (Q * (∑ w, MvPolynomial.C (c w) * MvPolynomial.X w) ^ k) (S G) := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
    have h' := h (Nat.succ_ne_zero k)
    rw [Function.iterate_succ_apply, ih (fun _ => h'), h', ← jetAt0_mul_lin, pow_succ, mul_assoc]

theorem jetAt0_foldr {A ι : Type} (S : A → MvPowerSeries W C) (D : ι → A → A) (c : ι → W → C) (m : ι → ℕ)
    (h : ∀ l, m l ≠ 0 → ∀ G, S (D l G) = ∑ w, c l w • MvPowerSeries.pderiv (R := C) w (S G)) (L : List ι)
    (Q : MvPolynomial W C) (G : A) :
    jetAt0 Q (S (L.foldr (fun l g => (D l)^[m l] g) G)) =
      jetAt0 (Q * (L.map fun l => (∑ w, MvPolynomial.C (c l w) * MvPolynomial.X w) ^ m l).prod) (S G) := by
  induction L generalizing Q with
  | nil => simp
  | cons l L ih =>
    rw [List.foldr_cons, jetAt0_iterate S (D l) (c l) (m l) (h l), ih, List.map_cons, List.prod_cons, mul_assoc]

theorem jetAt0_one_left {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 1 G = MvPowerSeries.constantCoeff G := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', GlobalTheory.MinorShiftJet.jetAt0_monomial]
  simp [mfact]

theorem constantCoeff_DpolyN_eq_jetAt0 : ∀ (C : Type) [Field C] (dd n : ℕ) (F : Fin dd → PS C 2 dd) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (W : Type) [Fintype W] (E : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (E s) = 0) → ∀ (co : ι → W → C) (P : MvPolynomial ι C), (∀ ℓ ∈ P.vars, ∀ G : PS C n dd, MvPowerSeries.subst E (DofN F (cp ℓ) (uv ℓ) G) = ∑ w, co ℓ w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst E G)) → ∀ G : PS C n dd, MvPowerSeries.constantCoeff (DpolyN F cp uv P G) = jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ w, MvPolynomial.C (co ℓ w) * MvPolynomial.X w) P : MvPolynomial W C) (MvPowerSeries.subst E G) := by
  intro C _ dd n F ι _ cp uv W _ E hE co P h G
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', GlobalTheory.MinorShiftJet.jetAt0_sum_left, DpolyN, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_mul, MvPowerSeries.constantCoeff_C, MvPolynomial.algebraMap_eq, GlobalTheory.MinorShiftJet.jetAt0_C_mul]
  congr 1
  rw [← cc_subst hE, ← jetAt0_one_left, DmonN,
    jetAt0_foldr (fun g => MvPowerSeries.subst E g) (fun l => DofN F (cp l) (uv l)) co m
      (fun l hl => h l ((MvPolynomial.mem_vars_iff_mem_support l).2 ⟨m, hm, Finsupp.mem_support_iff.2 hl⟩)),
    one_mul, Finset.prod_map_toList]

end GlobalTheory.DerivJet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPart
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ActionLimit

namespace GlobalTheory.ActionEnd

variable {C : Type} [Field C]

theorem germ_comp1_zero_point_left {dd n : ℕ} (a : Pt C n dd) (ha : GP a) : comp1 (pt C dd (0 : Fin 1)) a = a := by
  funext i
  rw [germComp1_eq_subst]
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) _

theorem actK_self [CharZero C] {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (B : FB C dd O) (a : O) :
    B.actK C a = B.A.act a := by
  funext i
  show MvPowerSeries.map (RingHom.id C) _ = _
  rw [MvPowerSeries.map_id]; rfl

theorem exists_isEnd_act : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I) (a : O), ∃ M M' : Matrix (Fin dd) (Fin dd) C, (∀ v, M.mulVec v = linAct (Y.B.A.act a) v) ∧ (∀ v, M'.mulVec v = linAct (Y.B.A.act (star a)) v) ∧ IsEnd (Y.raw p) V M M' ∧ un1 (Y.B.hL C Y.h a) = hEnd (Y.raw p) 1 M := by
  intro C _ _ V O _ _ dd Y d _ I _ p a
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  refine ⟨dLin (Y.B.A.act a), dLin (Y.B.A.act (star a)), fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · refine isEnd_of_hom Y p _ _ (g _) (g _) (Y.B.A.hom _) (Y.B.A.hom _) (Y.intAct _) (Y.intAct _) ?_
    have h := Y.gauge.ad a
    rw [actK_self, actK_self] at h
    rw [← h]
    have e : FB.toK C (Y.B.ad a) = Y.B.ad a := by
      show MvPowerSeries.map (RingHom.id C) _ = _
      rw [MvPowerSeries.map_id]; rfl
    rw [e]
    exact Y.intAd a
  · have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
    have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
    have q0 : GP (pt C (n := 1) dd 0) := gp_pt 0
    have hs : MvPowerSeries.HasSubst
        (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hX q.2
    have e1 := matrixEnd_eq_subst Y p (pt C dd 0) q0 (by
      rw [germ_comp1_zero_point_left _ (gp_addOf _ Y.B.G.const _ _ p0 p1), germ_comp1_zero_point_left _ p0, germ_comp1_zero_point_left _ p1]) _ hX
    rw [germLinearPart_coordinatePoint_zero] at e1
    have e2 := matrixEnd_eq_subst Y p _ (g a) (Y.B.A.hom a) _ hX
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
      hEnd, hAt]
    show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
    congr 1
    funext ⟨s, x⟩
    fin_cases s
    · exact (e1 x).symm
    · exact (e2 x).symm

end GlobalTheory.ActionEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimit
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ActionLimit

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)
variable {d : ℕ} {I : Fin 2 → Type} (X : RawChart C d I (Fin dd))
  (hlg : X.lg = fun i => un1 (Y.lg i)) (hex : X.ex = fun i => un1 (Y.ex i)) (hh : X.h = Y.h)

include hlg hex in
theorem matrixEnd_linearMap' (M : Matrix (Fin dd) (Fin dd) C)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP X M a i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) i) := by
  have h0 := gp_lg Y
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  have hL : GP (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) := gp_comp1 _ _ (gp_linMap _) h0
  have e0 : endP X M a i =
    MvPowerSeries.subst (fun x => ∑ y, M x y • MvPowerSeries.subst a (un1 (Y.lg y))) (un1 (Y.ex i)) := by
    unfold endP
    rw [hlg, hex]
  rw [e0, funext (subst_linMap M Y.lg h0 a ha)]
  generalize comp1 (LogExpAdaptedGauge.linMap M) Y.lg = L at hL ⊢
  have hz : ∀ x, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (L x)) = 0 :=
    fun x => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (fun q : Fin 1 × Fin dd => ha q.2) (hL x)
  rw [subst_singlePointUncurry _ hz, germComp1_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => hL q.2) hs]

include hlg hex in
theorem matrixEnd_eq_subst' (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP X (dLin e) a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  rw [matrixEnd_linearMap' Y X hlg hex _ a ha, ← eq_exp_lin_log Y e he hhom]

include hlg hex in
theorem matrixEnd_eq_comp' (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {n : ℕ} (a : Pt C n dd) (ha : GP a) : endP X (dLin e) a = comp1 e a := by
  funext i
  rw [matrixEnd_eq_subst' Y X hlg hex e he hhom a ha, germComp1_eq_subst]

include hh in
theorem hAt_eq_ev_raw {n : ℕ} (a b : Pt C n dd) : hAt X a b = ev ![a, b] Y.h := by
  unfold hAt
  rw [hh]
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

include hlg hex hh in
theorem isEnd_of_hom_raw (e e' : Pt C 1 dd) (he : GP e) (he' : GP e')
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    (hhom' : comp1 e' (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e' (pt C (n := 2) dd 0)) (comp1 e' (pt C (n := 2) dd 1)))
    (hi : ∀ i, IntS V (e i)) (hi' : ∀ i, IntS V (e' i))
    (hx : IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 e' (pt C dd 1)] Y.h))) :
    IsEnd X V (dLin e) (dLin e') := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have hc : MvPowerSeries.constantCoeff Y.h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt (0 : Fin 1))) Y.h, Y.gauge.ax0, map_zero]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_eq_subst' Y X hlg hex e he hhom _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi i _
  · rw [matrixEnd_eq_subst' Y X hlg hex e' he' hhom' _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi' i _
  · have g0 : gp C (Fin dd) (0 : Fin 2) = pt C dd 0 := rfl
    have g1 : gp C (Fin dd) (1 : Fin 2) = pt C dd 1 := rfl
    rw [g0, g1, matrixEnd_eq_comp' Y X hlg hex e he hhom _ (gp_pt 0), matrixEnd_eq_comp' Y X hlg hex e' he' hhom' _ (gp_pt 1),
      hAt_eq_ev_raw Y X hh, hAt_eq_ev_raw Y X hh, ← subst_exp_eq_mvExp]
    · exact hx
    · rw [map_sub, gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ he (gp_pt 0)) (gp_pt 1)) _ hc,
        gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ he' (gp_pt 1))) _ hc, sub_zero]

end Chart

theorem exists_isEnd_of_limit_raw : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) (I : Fin 2 → Type) (X : RawChart C d I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h → ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd X V M M' ∧ IsEnd X V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  intro C _ _ V O _ _ dd Y d I X hlg hex hh a ha
  obtain ⟨c1, c2⟩ := _root_.GlobalTheory.ActionLimit.main C V O dd Y a ha
  obtain ⟨e, eb, i1, i2, l1, l2, h1, x1⟩ := _root_.GlobalTheory.ActLimit.limit_endomorphisms C V O dd Y a c1 c2
  obtain ⟨f, fb, -, -, l3, l4, h2, x2⟩ := _root_.GlobalTheory.ActLimit.limit_endomorphisms C V O dd Y (fun n => star (a n)) c2
    (by simpa only [star_star] using c1)
  simp only [star_star] at l4
  obtain rfl : f = eb := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l3 N i μ) (fun N => l2 N i μ)
  obtain rfl : fb = e := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l4 N i μ) (fun N => l1 N i μ)
  have hz : ∀ (g : Pt C 1 dd) (s : ℕ → O), (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (g i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) → GP g := by
    intro g s hg i
    refine limit_unique V (fun n => MvPowerSeries.coeff 0 (Y.B.A.act (s n) i)) _ _ (fun N => hg N i 0)
      fun N => ⟨0, fun n _ => ?_⟩
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.B.A.const, sub_zero]
    exact VF.Ge.zero _
  have g1 := hz fb a l1
  have g2 := hz f (fun n => star (a n)) l2
  exact ⟨dLin fb, dLin f, isEnd_of_hom_raw Y X hlg hex hh fb f g1 g2 h1 h2 i1 i2 x1, isEnd_of_hom_raw Y X hlg hex hh f fb g2 g1 h2 h1 i2 i1 x2,
    linear_limit V fb _ l1, linear_limit V f _ l2⟩

end GlobalTheory.ActionLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLadicSeparatingSequenceEmbeddings
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SeparatingSeq

open TeichSeq

variable {C : Type} [Field C] {V : VF C}

theorem ge_of_mul_unit {w : ℝ} {a u : C} (hu : V.Ge 0 u) (hu' : ¬ V.MM u)
    (h : V.Ge w (a * u)) : V.Ge w a := by
  have h0 : V.v u = 0 := le_antisymm (not_lt.1 hu') (by simpa [VF.Ge] using hu)
  unfold VF.Ge at h ⊢
  rwa [V.v.map_mul, h0, add_zero] at h

theorem ge_pow_pow_sub {t c : C} (ht : V.Ge 0 t) (hc : V.Ge 0 c) (h : V.Ge 1 (t - c)) (n : ℕ) :
    V.Ge n (t ^ V.l ^ n - c ^ V.l ^ n) := by
  have hq : V.Ge 0 ((V.l : C)⁻¹ * (t - c)) := by simpa using h.l_inv_mul
  have hd : (V.l : intRing V) ∣ (⟨t, ht⟩ : intRing V) - ⟨c, hc⟩ :=
    ⟨⟨_, hq⟩, Subtype.ext (by
      show t - c = ((V.l : intRing V) : C) * ((V.l : C)⁻¹ * (t - c))
      rw [SubringClass.coe_natCast, mul_inv_cancel_left₀ VF.l_ne_zero])⟩
  obtain ⟨z, hz⟩ := (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub hd n)
  have hz' : t ^ V.l ^ n - c ^ V.l ^ n = (z : C) * (V.l : C) ^ n := by
    have := congrArg Subtype.val hz
    simpa [mul_comm] using this
  rw [hz']
  exact VF.Ge.mul_int z.2 (ge_l_pow V n)

theorem main : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧ ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∃ s : ℕ → O, (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ (∀ (a : ZMod d) (K : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge K (1 - em a (s n))) ∧ ∀ φ : O →+* C, (∀ x, V.Ge 0 (φ x)) → (∀ a, ∃ x, V.v (em a x - φ x) = 0) → ∀ K : ℕ, ∃ n0, ∀ n ≥ n0, V.Ge K (0 - φ (s n)) := by
  intro C _ _ V O _ d _ em hint hfrob ⟨ε, ⟨y0, hε2⟩, hε1, hεP⟩
  have hεpow : ∀ n, (V.l : O) ∣ ε ^ (n + 1) - ε := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have : ε ^ (n + 1 + 1) - ε = (ε ^ (n + 1) - ε) * ε + (ε * ε - ε) := by ring
      rw [this]
      exact dvd_add (ih.mul_right _) ⟨y0, hε2⟩
  have hprod : ∀ ψ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → V.Ge 1 ((ψ ε - 1) * ψ ε) := fun ψ hψ => by
    have h1 : (ψ ε - 1) * ψ ε = ψ y0 * (V.l : C) := by
      have := congrArg ψ hε2
      rw [map_sub, map_mul, map_mul, map_natCast] at this
      linear_combination this
    rw [h1]
    exact (hψ y0).mul_int VF.ge_l
  have hnot : ∀ t : C, V.MM t → ¬ V.MM (t - 1) := fun t h1 h2 => by
    have h3 : V.MM (-(t - 1)) := by unfold VF.MM; rw [V.v.map_neg]; exact h2
    have h4 : 0 < V.v (t + -(t - 1)) := V.v.map_lt_add h1 h3
    simp at h4
  refine ⟨fun n => ε ^ V.l ^ n, fun n => ?_, fun a K => ⟨K, fun n hn => ?_⟩,
    fun φ hφ hsep K => ⟨K, fun n hn => ?_⟩⟩
  · have h1 := hεpow (V.l - 1)
    rw [Nat.sub_add_cancel V.l_prime.one_lt.le] at h1
    have h2 := (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub h1 n)
    rw [← pow_mul, ← pow_succ'] at h2
    exact h2
  · have h1 : V.Ge 1 (em a ε - 1) :=
      ge_of_mul_unit (hint a ε) (fun h => hnot _ h (hε1 a)) (hprod _ (hint a))
    have h2 := (ge_pow_pow_sub (hint a ε) VF.Ge.one h1 n).neg
    rw [one_pow, neg_sub, ← map_pow] at h2
    exact h2.mono (by exact_mod_cast hn)
  · have hm : V.MM (φ ε) := by
      by_contra hu
      obtain ⟨a, ha⟩ := ResidueChar.main C V O d em hint hfrob φ hφ (fun x hx => by
        obtain ⟨y, hy⟩ := hεP x hx
        have h1 : φ x * φ ε = φ y * (V.l : C) := by
          have := congrArg φ hy
          rw [map_mul, map_mul, map_natCast] at this
          linear_combination this
        refine mm_of_ge_one V (ge_of_mul_unit (hφ ε) hu ?_)
        rw [h1]
        exact (hφ y).mul_int VF.ge_l)
      obtain ⟨x, hx⟩ := hsep a
      have h2 : 0 < V.v (φ x - em a x) := ha x
      rw [← neg_sub, V.v.map_neg, hx] at h2
      exact lt_irrefl _ h2
    have h1 : V.Ge 1 (φ ε - 0) := by
      rw [sub_zero]
      refine ge_of_mul_unit ((hφ ε).sub VF.Ge.one) (hnot _ hm) ?_
      rw [mul_comm]
      exact hprod φ hφ
    have h2 := (ge_pow_pow_sub (hφ ε) (VF.Ge.zero 0) h1 n).neg
    rw [zero_pow (pow_ne_zero _ V.l_prime.ne_zero), neg_sub, ← map_pow] at h2
    exact h2.mono (by exact_mod_cast hn)

end GlobalTheory.SeparatingSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdSubstDisjointVariables
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.JetProdSubst

theorem jetAt0_prod_subst : ∀ (C : Type) [Field C] (Orb : Type) [Fintype Orb] (σ : Orb → Type) [∀ o, Fintype (σ o)] (τ : Type) (e : ∀ o, σ o → τ), Function.Injective (fun x : (Σ o, σ o) => e x.1 x.2) → ∀ (P : ∀ o, MvPolynomial (σ o) C) (F : ∀ o, MvPowerSeries (σ o) C), jetAt0 (∏ o, MvPolynomial.rename (e o) (P o)) (∏ o, MvPowerSeries.subst (fun x : σ o => (MvPowerSeries.X (e o x) : MvPowerSeries τ C)) (F o)) = ∏ o, jetAt0 (P o) (F o) := by
  intro C _ Orb _ σ _ τ e he P F
  let e' : ∀ o, σ o ↪ τ := fun o => ⟨e o, fun x y h => by
    have h1 : (⟨o, x⟩ : Σ o, σ o) = ⟨o, y⟩ := he h
    simpa using h1⟩
  have hd : ∀ i j x y, e' i x = e' j y → i = j := fun i j x y h =>
    congrArg Sigma.fst (he (a₁ := ⟨i, x⟩) (a₂ := ⟨j, y⟩) h)
  rw [← GlobalTheory.JetProd.jetAt0_prod_rename e' hd]
  congr 1
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [MvPowerSeries.rename_eq_subst]
  rfl

end GlobalTheory.JetProdSubst
end

