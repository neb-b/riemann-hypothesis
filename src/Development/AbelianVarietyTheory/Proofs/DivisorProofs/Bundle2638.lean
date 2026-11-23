module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointNthMultipleGaloisFixedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalk
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbar
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')

theorem loc_pullback_eq {f : M' → M} {α : A.Fld} (hf : A.IsHolo A' f) (hα : A.IsForm α) (j : A'.ι) (i : A.ι) :
    IsOpen ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) ∧
    ∀ v ∈ (A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source),
      A'.loc (A.pullback A' f α) j v =
        pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) v) (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) v)) := by
  refine ⟨(A'.e j).continuousOn_symm.isOpen_inter_preimage (A'.e j).open_target
    ((A.e i).open_source.preimage hf.1), fun v hv => ?_⟩
  have hs : (A'.e j).symm v ∈ (A'.e j).source := (A'.e j).map_target hv.1
  have hτ : (A.e i ∘ f ∘ (A'.e j).symm) v ∈ (A.e i).target := (A.e i).map_source hv.2
  rw [HolAtlas.loc, dite_eq_left hv.1, HolAtlas.loc, dite_eq_left hτ,
    _root_.GlobalTheory.CxForm.pullback_eq_chart M M' n n' A A' f α hf hα ⟨(j, (A'.e j).symm v), hs⟩ i hv.2]
  have hc : (A'.e j) ((A'.e j).symm v) = v := (A'.e j).right_inv hv.1
  simp only [Pt.crd, Pt.ch, Pt.pt, hc]
  congr 2
  exact Subtype.ext (Prod.ext rfl ((A.e i).left_inv hv.2).symm)

theorem pullback_del_dbar (f : M' → M) (α : A.Fld) (hf : A.IsHolo A' f) (hα : A.IsForm α) :
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
      A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) := by
  have key : ∀ x : A'.Pt, A'.del (A.pullback A' f α) x = A.pullback A' f (A.del α) x ∧
      A'.dbar (A.pullback A' f α) x = A.pullback A' f (A.dbar α) x := by
    intro x
    have hi : f x.pt ∈ (A.e (A.cover (f x.pt)).choose).source := (A.cover (f x.pt)).choose_spec
    obtain ⟨hU, hloc⟩ := loc_pullback_eq A A' hf hα x.1.1 (A.cover (f x.pt)).choose
    have hx : x.crd ∈ (A'.e x.1.1).target ∩ (A'.e x.1.1).symm ⁻¹' (f ⁻¹' (A.e (A.cover (f x.pt)).choose).source) := by
      refine ⟨(A'.e x.1.1).map_source x.2, ?_⟩
      show (A'.e x.1.1).symm (A'.e x.1.1 x.1.2) ∈ f ⁻¹' (A.e (A.cover (f x.pt)).choose).source
      rw [(A'.e x.1.1).left_inv x.2]
      exact hi
    have hτx : (A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd =
        A.e (A.cover (f x.pt)).choose (f x.pt) := by
      show A.e _ (f ((A'.e x.1.1).symm (A'.e x.1.1 x.1.2))) = _
      rw [(A'.e x.1.1).left_inv x.2]
    have hdiff : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α (A.cover (f x.pt)).choose y) S)
        ((A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd) := by
      intro S
      rw [hτx]
      exact ((hα.smooth _ S).differentiableOn (by simp)).differentiableAt
        ((A.e _).open_target.mem_nhds ((A.e _).map_source hi))
    have hc := GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n' n _ _ (A.loc α (A.cover (f x.pt)).choose) x.crd hU hx (hf.2 x.1.1 _) hdiff
    have hl := (_root_.GlobalTheory.CxForm.delAt_dbarAt_linear_local n' x.crd).2.2.2.1 _ _ (Filter.eventually_of_mem (hU.mem_nhds hx) hloc)
    rw [hτx] at hc
    exact ⟨(hl.1.trans hc.1 : _), (hl.2.trans hc.2 : _)⟩
  exact ⟨funext fun x => (key x).1, funext fun x => (key x).2⟩

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ)
    (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A.IsForm (A.del α) → A.IsForm (A.dbar α) →
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧ A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) :=
  fun _ _ _ _ _ _ A A' f α hf hα _ _ => HolAtlas.pullback_del_dbar A A' f α hf hα
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointCharactersGaloisFixedOfRationalBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.TorusExt
attribute [local instance] GlobalTheory.TorusExt.gtGroup

namespace GlobalTheory.Mum.RatChar

theorem charFixed : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → (∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left) → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (p.g.s χ) (LB.pullGen D'.toPre.P.L _ _ (p.g.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ p₀ p hy hact hb χ
  let f : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing R) := σ.toAlgHom.toRingHom
  have hf : f.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) := σ.toAlgHom.comp_algebraMap
  have hB := D'.tau_bimult
  obtain ⟨h, ⟨hhb, hhs⟩, ⟨z, hz, hzι⟩, hhe⟩ := _root_.GlobalTheory.Mum.EDiv.exists_fixed_root T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ (F.xp p₀.y)
  have hya : p.y = F.xi (F.xp p₀.y) := by rw [hy, F.xi_xp]
  have hg : n • p.g = iota hB _ p.y := by
    obtain ⟨z', hz', hz'ι⟩ := p.eq
    rw [← (isNsmul_iff_eq _ _ _).1 hz', ← (isIota_iff_eq hB _ _).1 hz'ι]
  have hh : n • h = iota hB _ p.y := by
    rw [hya, ← (isNsmul_iff_eq _ _ _).1 hz, ← (isIota_iff_eq hB _ _).1 hzι]
  set t := p.g - h with ht
  have htn : n • t = 0 := by rw [ht, nsmul_sub, hg, hh, sub_self]
  have hte : GtPtAct F.o F.e t t :=
    _root_.GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd F.o F.e F.idem p₀.g p.g h t hact hhe ((isAdd_iff_eq _ _ _).2 (sub_add_cancel p.g h).symm)
  have hfixh : gtExt D'.toPre f hf h = h := ((eq_gtExt_iff f hf h h).2 ⟨hhb.symm, hhs⟩).symm
  have hgb : extMap f hf ≫ p.g.b = p.g.b := by
    obtain ⟨b, hb⟩ := hb
    apply Over.OverMorphism.ext
    rw [Over.comp_left, extMap_left, hb, ← Category.assoc]
    congr 1
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
  have htb : extMap f hf ≫ t.b = t.b := by
    have e1 : gtExt D'.toPre f hf t = gtExt D'.toPre f hf p.g - h := by rw [ht, map_sub, hfixh]
    have e2 := congrArg GtPtF.b e1
    rw [gtExt_b, sub_eq_add_neg, add_b, neg_b, gtExt_b, hgb] at e2
    rw [e2, ht, sub_eq_add_neg, add_b, neg_b]
  have htb' : spMap f ≫ t.b.left = t.b.left := by
    have := congrArg (fun q => q.left) htb
    simpa [Over.comp_left, extMap_left] using this
  have hts := _root_.GlobalTheory.Mum.ETors.corr_pullGen_of_torsion T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ t hte ⟨0, (isNsmul_iff_eq _ _ _).2 htn.symm, (isZero_iff_eq _).2 rfl⟩ htb'
  have hfixt : gtExt D'.toPre f hf t = t := ((eq_gtExt_iff f hf t t).2 ⟨htb'.symm, hts⟩).symm
  have hfixg : gtExt D'.toPre f hf p.g = p.g := by
    have : p.g = t + h := (sub_add_cancel p.g h).symm
    rw [this, map_add (f := _), hfixt, hfixh]
  exact ((eq_gtExt_iff f hf p.g p.g).1 hfixg.symm).2 χ

end GlobalTheory.Mum.RatChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenDecompositionIffShiftedProductsKillComaximaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenDecomposition_iff_shiftedProducts_kill_comaximal : ∀ (O T V : Type) [CommRing O] [CommRing T] [AddCommGroup V] [Module T V] (ψ : O →+* Module.End T V) (a : ℕ)
  (τ : Fin a → (O →+* T)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤) → ∀ v : V,
    ((∃ w : Fin a → V, (∀ i, w i ∈ eigSub ψ (τ i)) ∧ v = ∑ i, w i) ↔
      ∀ c : Fin a → O, (List.ofFn fun i => ψ (c i) - algebraMap T (Module.End T V) (τ i (c i))).prod v = 0) := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.decomp_iff_kill) | (exact GlobalTheory.UPel.HT.LieLin.decomp_iff_kill) | (intros; apply GlobalTheory.UPel.HT.LieLin.decomp_iff_kill  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBound
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.ShFam.PerPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_nat_smul_mem {N : ℕ} (X : Data E N) (v : Fin N → E) :
    ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ :=
  _root_.UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem X v

theorem perFr_natCast_smul {N : ℕ} (X : Data E N) (x : Frame X.Ψ N) (v : Fin N → E) (n : ℕ) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x ((n : E) • v) τ i = (n : ℂ) * perFr X x v τ i := by
  have he : ∀ τ : E →+* ℂ, Data.emb τ ((n : E) • v) = (n : ℂ) • Data.emb τ v := fun τ => funext fun a => by
    simp [Data.emb, map_natCast]
  unfold perFr
  split_ifs <;> simp [he, Matrix.mulVec_smul, ReciprocityTheory.ChartRestriction.G.FD.hermC, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.ShFam.PerPoly

namespace GlobalTheory.ShFam.PerPoly

theorem periods_le_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ (v : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr (U.X k) (xx w) v ρ i‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift v R
  obtain ⟨n, hn, hnv⟩ := exists_nat_smul_mem (U.X k) v
  obtain ⟨C₁, B, h₁⟩ := _root_.GlobalTheory.ShFam.PerPoly.periods_le_of_mem_lattice E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
    _ hnv R
  obtain ⟨C₃, h₃⟩ : ∃ C₃ : ℝ, ∀ᶠ w in imTop, (U.X k).p0 = 0 → ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := by
    by_cases h0 : (U.X k).p0 = 0
    · obtain ⟨C₃, h⟩ := _root_.GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
        h0 v
      exact ⟨C₃, h.mono fun w hw _ => hw⟩
    · exact ⟨0, .of_forall fun w h => absurd h h0⟩
  have him : ∀ᶠ w in imTop, 1 ≤ w.im :=
    (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_ge_atTop 1)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨max (C₁ / n) 0 + max C₃ 0, B, ?_⟩
  filter_upwards [h₁, h₃, him] with w hw1 hw3 hwi hR τ i
  have hpow : 1 ≤ w.im ^ B := one_le_pow₀ hwi
  have hK0 : 0 ≤ max (C₁ / n) 0 + max C₃ 0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hK1 : C₁ / n ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
  have hK3 : C₃ ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  have hlat : ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := by
    intro τ i h
    have h2 := hw1 hR τ i h
    rw [perFr_natCast_smul, norm_mul, Complex.norm_natCast] at h2
    have h3 : ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₁ / n * w.im ^ B := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn']
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_right hK1 (by positivity))
  have hzero : 0 ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := mul_nonneg hK0 (by positivity)
  by_cases hτ : τ ∈ (U.X k).Ψ
  · by_cases hi : i < N - (U.X k).p0
    · exact hlat τ i (Or.inl ⟨hτ, hi⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dite_eq_left hτ, dite_eq_right (by omega)]
      rw [e, norm_zero]
      exact hzero
  · by_cases hc : conjEmb τ ∈ (U.X k).Ψ
    · by_cases h0 : (U.X k).p0 = 0
      · calc ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := hw3 h0 τ i hτ
          _ ≤ max (C₁ / n) 0 + max C₃ 0 := hK3
          _ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := le_mul_of_one_le_right hK0 hpow
      · by_cases hi : i < (U.X k).p0
        · exact hlat τ i (Or.inr ⟨hc, hi⟩)
        · have e : perFr (U.X k) (xx w) v τ i = perFr (U.X k) (xx w) v τ ((U.X k).p0 - 1) := by
            have e1 : (U.X k).p0 - 1 - i = (U.X k).p0 - 1 - ((U.X k).p0 - 1) := by omega
            unfold perFr
            rw [dite_eq_right hτ, dite_eq_right hτ, dite_eq_left hc, dite_eq_left hc]
            simp only [e1]
          rw [e]
          exact hlat τ _ (Or.inr ⟨hc, by omega⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dite_eq_right hτ, dite_eq_right hc]
      rw [e, norm_zero]
      exact hzero

end GlobalTheory.ShFam.PerPoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerE8BundleIsoOfPrincipalSiegelIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_E8Bundle_iso_of_principalSiegelIso : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  first | exact @GlobalTheory.SharpIso.iso_of_sRel | exact GlobalTheory.SharpIso.iso_of_sRel | (intros; apply GlobalTheory.SharpIso.iso_of_sRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerEndomorphismLatticeAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighth_power_endomorphism_lattice_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E' : GlobalTheory.UT.EndU U'.toUnifPre, (∀ u, E'.aA ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → ∀ y, e (E'.h y) = fun u => ∑ v, a u v • e y v := by
  first | exact @GlobalTheory.Poinc.E8Endomorphism.endU_lattice_adjoint | exact GlobalTheory.Poinc.E8Endomorphism.endU_lattice_adjoint | (intros; apply GlobalTheory.Poinc.E8Endomorphism.endU_lattice_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsExtendUniformisedGroupsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_projections_extend_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∃ (pG : Fin 8 → (G' ⟶ G)) (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)) (e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X)), (∀ v, IsMonHom (pG v)) ∧ (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) ∧ (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) ∧ ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := by
  first | exact @GlobalTheory.Poinc.Eq8.e8data | exact GlobalTheory.Poinc.Eq8.e8data | (intros; apply GlobalTheory.Poinc.Eq8.e8data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerPsiOrdersProjectionLatticeCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Lattice

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e hsum ϖ β hs hp hτ y r hr
  refine GlobalTheory.Poinc.E8Order.main R hdvr D.toPre D'.toPre D'.tau_bimult D'.psi_even D.tau_bimult W hW ϖ β hs hp hτ c e hsum
    ?_ y r hr
  intro v a' b x x' hx hx'
  exact GlobalTheory.TauFormHom.main R hRb hdvr G hG D A U G' hG' D' A' U' (pG v) (hpG v) (c v)
    ((Pi.evalAddMonoidHom (fun _ : Fin 8 => D.toPre.X) v).comp e.toAddMonoidHom) (hc v)
    (GlobalTheory.T.torsionLabels_eighthPower_projections R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e hsum v)
    a' b x x' hx hx'

end GlobalTheory.Poinc.E8Lattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniformisedMonomialPeriodsLatticeIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.EighthPow

def matAct {X : Type} [AddCommGroup X] (M : Matrix (Fin 8) (Fin 8) ℤ) (t : Fin 8 → X) : Fin 8 → X :=
  fun v => ∑ u, M v u • t u

theorem matAct_mul {X : Type} [AddCommGroup X] (N M : Matrix (Fin 8) (Fin 8) ℤ) (t : Fin 8 → X) :
    matAct N (matAct M t) = matAct (N * M) t := by
  funext v
  simp only [matAct, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
  exact Finset.sum_comm

theorem matAct_one {X : Type} [AddCommGroup X] (t : Fin 8 → X) : matAct 1 t = t := by
  funext v
  simp [matAct, Matrix.one_apply, ite_smul]

def matEquiv {X : Type} [AddCommGroup X] (M : Matrix (Fin 8) (Fin 8) ℤ) (h : M.det = 1) :
    (Fin 8 → X) ≃+ (Fin 8 → X) where
  toFun := matAct M
  invFun := matAct M.adjugate
  left_inv t := by rw [matAct_mul, Matrix.adjugate_mul, h, one_smul, matAct_one]
  right_inv t := by rw [matAct_mul, Matrix.mul_adjugate, h, one_smul, matAct_one]
  map_add' s t := by funext v; simp [matAct, smul_add, Finset.sum_add_distrib]

def sumHom {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (c : Fin 8 → (X →+ Y)) : (Fin 8 → X) →+ Y :=
  AddMonoidHom.mk' (fun y => ∑ v, c v (y v)) fun s t => by simp [Finset.sum_add_distrib]

end GlobalTheory.Poinc.EighthPow


open GlobalTheory.Poinc.EighthPow in
theorem GlobalTheory.Poinc.EighthPow.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (ϖ : R) (β : LinearMap.BilinForm ℤ D.toPre.X), (∀ a b, β a b = β b a) → (∀ a, 0 ≤ β a a) → (∀ a b' (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b' x → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * algebraMap R (FractionRing R) ϖ ^ (β a b')) → ∃ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W β (e y) ∧ Associated r (ϖ ^ (qW W β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr a b f₁ → (Over.pullback (jK R)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL ϖ β hs hp hτ
  haveI := hdvr
  have hext : ∀ v, ∃ p : G' ⟶ G, IsMonHom p ∧
      (Over.pullback (jK R)).map p ≫ U.gen.hom = U'.gen.hom ≫ pr v := by
    intro v
    have h1 := U'.gen_hom
    have h2 := U.gen_hom
    have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    haveI := hpr v
    obtain ⟨F, ⟨hF, hFe⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G' G hG' hG
      (U'.gen.hom ≫ pr v ≫ U.gen.symm.hom) inferInstance
    refine ⟨F, hF, ?_⟩
    have hFe' : (Over.pullback (jK R)).map F = U'.gen.hom ≫ pr v ≫ U.gen.inv := hFe
    rw [hFe']
    simp
  choose pG hpGm hpG using hext
  have hc : ∀ v, ∃ ρ, TorMatch U U' (RingHom.id R) (pG v).left ρ := fun v =>
    GlobalTheory.Poinc.HomTor.exists_torMatch R hRb G hG D A U G' hG' D' A' U' (pG v) (hpGm v)
  choose c hc using hc
  obtain ⟨hbij, hmat⟩ := GlobalTheory.T.characters_eighthPower_elementaryMatrices_alt R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hpG c hc
  let Φ : (Fin 8 → D.toPre.X) ≃+ D'.toPre.X := AddEquiv.ofBijective (sumHom c) hbij
  let Mq : (Fin 8 → D.toPre.X) ≃+ (Fin 8 → D.toPre.X) := matEquiv (W + W.transpose) hW.2
  let e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X) := (Mq.trans Φ).symm
  have he : ∀ y, Φ (Mq (e y)) = y := fun y => (Mq.trans Φ).apply_symm_apply y
  have he' : ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := he
  refine ⟨e, ?_, ?_⟩
  · intro y r hr
    have hlab := fun v => GlobalTheory.T.torsionLabels_eighthPower_projections R hRb hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hpG c hc e
      he' v
    refine GlobalTheory.Poinc.E8Order.main R hdvr D.toPre D'.toPre D'.tau_bimult D'.psi_even D.tau_bimult W hW ϖ β hs hp hτ c e
      he' ?_ y r hr
    intro v a' b x x' hx hx'
    exact GlobalTheory.TauFormHom.main R hRb hdvr G hG D A U G' hG' D' A' U' (pG v) (hpGm v) (c v)
      ((Pi.evalAddMonoidHom (fun _ => D.toPre.X) v).comp e.toAddMonoidHom) (hc v) (hlab v) a' b x x' hx hx'
  · intro a b f f₁ m hf hf₁ hcomp hm y
    have hmc := hmat a b f f₁ m hf hf₁ hcomp hm
    have hy : y = Φ (Mq (e y)) := (he y).symm
    let t' : Fin 8 → D.toPre.X := fun w => if w = b then Mq (e y) a else 0
    have hmy : m y = Φ t' := by
      conv_lhs => rw [hy]
      show m (∑ w, c w (Mq (e y) w)) = ∑ w, c w (t' w)
      have hL : m (∑ w, c w (Mq (e y) w)) = c b (Mq (e y) a) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]; simp [hmc]
      have hR : ∑ w, c w (t' w) = c b (Mq (e y) a) := by
        rw [Finset.sum_eq_single b (fun w _ hw => by simp only [t', if_neg hw, map_zero]) (by simp)]
        simp only [t', if_pos rfl]
      rw [hL, hR]
    have hkey : Mq (e (m y)) = t' := Φ.injective (by rw [he, hmy])
    intro v
    have h := congrFun hkey v
    change ∑ u, (W + W.transpose) v u • e (m y) u = _ at h
    rw [h]
    rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerUniversalObjectAtModelStalkStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighth_power_universal_object_at_model_stalk : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ z : V.toScheme, ∃ (cO : SiegPre g n ζ ((V.toScheme.fromSpecStalk z ≫ v) ≫ F.s)) (prO : Fin 8 → ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G ⟶ cO.A)), SiegPB cO F.univ (V.toScheme.fromSpecStalk z ≫ v) ∧ (∀ a, IsMonHom (prO a)) ∧ (∀ (T' : Over (Spec (V.toScheme.presheaf.stalk z))) (y : Fin 8 → (T' ⟶ cO.A)), ∃! x : T' ⟶ (Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).obj FinalForm.G, ∀ a, x ≫ prO a = y a) ∧ LBIso (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom (V.toScheme.fromSpecStalk z ≫ V.ι))) (LB.LinComb cO.P (K := Fin 8 × Fin 8) (fun ab => (lift (prO ab.1) (prO ab.2)).left) (fun ab => W ab.1 ab.2)) ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G), MatOn FinalForm pr a b f → MatEnd prO a b ((Over.pullback (V.toScheme.fromSpecStalk z ≫ V.ι)).map f) := by
  first | exact @GlobalTheory.Poinc.Eq8.StalkPow.eighth_power_at_stalk | exact GlobalTheory.Poinc.Eq8.StalkPow.eighth_power_at_stalk | (intros; apply GlobalTheory.Poinc.Eq8.StalkPow.eighth_power_at_stalk <;> assumption)
end

