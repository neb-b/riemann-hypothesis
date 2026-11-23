module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtal
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2946
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSeparationDataDefinedOverCentreField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerStageRankFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTjCorrespondencePInvertible
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_tjCorr_finiteEtale : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ T : TjCorr M.toRepFam r w j c, IsFinite T.s ∧ Etale T.s ∧ Surjective T.s ∧ IsFinite T.t ∧ Etale T.t ∧ ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ T.Y, y ≫ T.s = x ∧ ∃ (m₀ : ObjMap o₁ T.o y) (m₁ : ObjMap o₁' T.o' y), m₀.φ ≫ T.ψ.left = ψ₁.left ≫ m₁.φ := by
  intro p _ D R _ _ b N hN hNp hp r w j c hw hu hj hc hm M
  haveI : LocallyOfFiniteType M.s := by
    haveI : Smooth M.s := M.smooth.smooth
    infer_instance
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, o₀, m₀, o', ψ, hfin, het, hisog, htj, huniv⟩ :=
    GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable p D R b N hN hNp hp r w j c hw hu hj hc hm M.X M.s M.univ
  obtain ⟨t, ⟨ht, ⟨mt⟩⟩, -⟩ := M.rep Y.left (Y.hom ≫ M.s) o'
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.UPel.HT.ESDual.finite_etale_target p D R b N hN hNp hp r w j c hw hu hj hc hm M Y.left Y.hom t ht.symm o₀ o' m₀ mt ψ
    hisog htj hfin het huniv
  have hsurj : Surjective Y.hom := by
    refine ⟨fun x => ?_⟩
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point M.X x
    obtain ⟨o₁, ⟨m⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp k) M.s a M.univ
    obtain ⟨o₁', ψ₁, h1, h2⟩ := _root_.GlobalTheory.UPel.HT.ES.TjExists.exists_isPIsog_isTj p D R b N hN hNp hp r w j c hw hu hj hc hm k (a ≫ M.s) o₁
    obtain ⟨y, ⟨hy, -⟩, -⟩ := huniv (Sp k) a o₁ o₁' m ψ₁ h1 h2
    have hx : x ∈ Set.range a.base := by rw [ha]; rfl
    obtain ⟨z', rfl⟩ := hx
    exact ⟨y.base z', by rw [← hy]; rfl⟩
  let T : TjCorr M.toRepFam r w j c :=
    { Y := Y.left, s := Y.hom, t := t, st := ht.symm, o := o₀, o' := o', ms := m₀, mt := mt, ψ := ψ,
      isog := hisog, tj := htj, wPrime := hw.isPrime, uLe := hu,
      pReg := fun U f hf => pReg_of_isUnit (Y.hom ≫ M.s) hp U f hf, sFin := hfin, tFin := h3, sSurj := hsurj }
  exact ⟨T, hfin, het, hsurj, h3, h4, fun S x o₁ o₁' m ψ₁ _ h1 h2 => huniv S x o₁ o₁' m ψ₁ h1 h2⟩

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointRigidTautologicalChartUnitaryBoundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem exists_tautB_chart_at : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTautB C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hB, hac, hnt, hC, hV⟩ :=
    _root_.GlobalTheory.UChartGeo.exists_monoFam_algClosed Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨k, _, m, e, C₁, ξ, θ, hT, hC₁, hθ, hξ⟩ :=
    _root_.GlobalTheory.UCanon.exists_taut_through Xo c φ hpq hpol hns zs i OZ N d J π j BD hU hS V hB hac C ξV hnt hC
  refine ⟨k, inferInstance, m, e, C₁, ξ, hT, hC₁, ?_⟩
  rw [← hV, ← hξ]
  change _ = ξ.base ((spMap θ).base (closedPoint V))
  have h0 : (spMap θ).base (closedPoint V) = closedPoint (ChartRing k m e) := by
    haveI := hθ
    exact IsLocalRing.comap_closedPoint θ
  rw [h0]

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChartSiegelNormalizedBlowup
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin

namespace GlobalTheory.AllChart

theorem preChart_all : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, PreChart F (π ≫ z) j φ BD d x := by
  intro g hg φ hφ hns n hn hodd F Z z i OZ d S π j _ BD hmin hblow x
  obtain ⟨C, G₁, _, y, α₁, ξ, hfam, hy, hx⟩ :=
    _root_.GlobalTheory.TChart.exists_chart_at g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow x
  have : IsCommMonObj G₁ := hfam.1.comm
  obtain ⟨het, hsep⟩ :=
    _root_.GlobalTheory.TChartEt.isEtaleCompletion_tautChart _root_.GlobalTheory.Poinc.Sep.sepSt g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy
  have h := _root_.GlobalTheory.TChartPre.preChart_of_isEtaleCompletion g hg φ hφ hns n hn hodd F Z z i OZ d S π j BD hmin hblow C G₁ y α₁ ξ hfam hy het hsep
  rwa [hx] at h

end GlobalTheory.AllChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep


set_option maxHeartbeats 1000000 in
theorem exists_system_with_traits_and_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (M : Scheme.{0}) (_ : IsIntegral M) (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] ((n ^ j) ^ 2) (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty ∧ j₀ ≤ j ∧ IsCov C g z₁ ζ ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U ∧ IsMember ζ Φ Cm ξ y ρ e h := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hV ξ hξ n hn hodd j₀
  obtain ⟨j, X₁, π, z₁, ζ, hdom, U, Φ, y, ρ, e, h, c₀, hj, hcov, hU, hT, hM, hunit, hm1, hE, hCS⟩ :=
    _root_.GlobalTheory.GSep.exists_vPre_traitsOn_chart E H Dw hpq l Xo c C φ V Cm hV ξ hξ n hn hodd (max j₀ 1)
  obtain ⟨-, -, hIC, -⟩ := GlobalTheory.T.modelStalk_normal_noetherian_fractionRing X₁ z₁
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hN : 3 ≤ (n ^ j) ^ 2 := by
    have h3 : 3 ≤ n := by
      rcases hodd with ⟨k, hk⟩
      have := hn.two_le
      omega
    have h2 : 3 ≤ n ^ j := le_trans h3 (Nat.le_self_pow (by omega) n)
    nlinarith
  have hLam : Φ.abelian₂ := _root_.GlobalTheory.Poinc.SepLam.lam_of_exact (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) (by norm_num) hN hE
  have hFour : Φ.Four ((n ^ j) ^ 2) := _root_.GlobalTheory.Poinc.SFour.four_of_classSums (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hCS
  let v : ∀ y', (Φ.V y')ˣ := fun y' => (hunit y').unit⁻¹
  have happ : ∀ e' : ℕ, ∃ a : X₁.M.Z.presheaf.stalk z₁, ∀ y', Φ.ev y' a - ((v y')⁻¹ : (Φ.V y')ˣ) ∈
      (maximalIdeal (X₁.M.Z.presheaf.stalk z₁) ^ e').map (Φ.ev y') := by
    intro e'
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.Poinc.Sep.coeffZero_approx (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hN hE hLam hFour
      (fun y₁ y₂ h₁ h₂ => (hm1 y₁ h₁).trans (hm1 y₂ h₂).symm) c₀ e'
    refine ⟨a, fun y' => ?_⟩
    simpa [v] using ha y'
  have hFour' : (Φ.rescale v).Four ((n ^ j) ^ 2) := _root_.GlobalTheory.Poinc.VPre.four_rescale (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hFour v happ
  have hLam' : (Φ.rescale v).abelian₂ := hLam
  refine ⟨j, X₁.M.Z, inferInstance, π, z₁, ζ, (Φ.rescale v).toVSys ((n ^ j) ^ 2) hLam' hFour', y, ρ, e, h, U, hU,
    le_trans (le_max_left _ _) hj, hcov, hT, ?_⟩
  obtain ⟨h1, h2, h3, h4, D, p, hT0⟩ := hM
  refine ⟨h1, h2, h3, h4, D, p, ?_⟩
  have h0 : Φ.term y (fun _ => e.symm 0) c₀ * ((v y : (Φ.V y)ˣ) : Φ.V y) = 1 := by
    have hz : (fun _ : Fin 1 => e.symm 0) = 0 := by
      funext a; simp
    rw [hz]
    simp [VPre.term, mono, qW, v]
  have := _root_.GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one (Φ.V y) D ((n ^ j) ^ 2) _ Φ.Q p.xe.symm
    (fun mu c => Φ.term y (fun _ => e.symm mu) c) (v y) c₀ hT0 h0
  refine cast (congrArg (fun T => GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) p.xe.symm T) ?_) this
  funext mu c
  show Φ.u y (fun _ => e.symm mu) c * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu) * ((v y : (Φ.V y)ˣ) : Φ.V y) =
    Φ.u y (fun _ => e.symm mu) c * ((v y : (Φ.V y)ˣ) : Φ.V y) * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)
  exact mul_right_comm _ _ _

end GlobalTheory.USep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalFirstOrderDeformationHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom)) ∧ ∀ o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, Nonempty (GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) := by
  first | (exact @GlobalTheory.HTUniv.main) | (exact GlobalTheory.HTUniv.main) | (intros; apply GlobalTheory.HTUniv.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinTrickFamilySiegelKernelKilledStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhinTrick_family_siegel_kernelKilled : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (O : Type) (_ : Ring O) (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), (∀ a b, bar (a + b) = bar a + bar b) ∧ Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) ∧ e * e = e ∧ (∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P bar act ∧ ZRel e jl o κ c z act) ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : O → (z₁.A ⟶ z₁.A)) (act₂ : O → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P bar act₁ → Adj z₂.A z₂.P bar act₂ → ZRel e jl o κ c z₁ act₁ → ZRel e jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  first | (exact @GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy) | (exact GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy) | (intros; apply GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerIsoSmoothSncToroidalModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKSAssembly

theorem entry_mem_of_mem_smul_top {R : Type} [CommRing R] {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R))
    (m : Ideal R) (y : N) (hy : y ∈ m • (⊤ : Submodule R N)) (a b : Fin n) : (y : Matrix (Fin n) (Fin n) R) a b ∈ m := by
  refine Submodule.smul_induction_on (p := fun y : N => (y : Matrix (Fin n) (Fin n) R) a b ∈ m) hy ?_ ?_
  · intro r hr x _
    simpa using m.mul_mem_right _ hr
  · intro x y hx hy
    simpa using m.add_mem hx hy

theorem exists_equiv {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L]
    {n : ℕ} (N : Submodule R (Matrix (Fin n) (Fin n) R)) [Module.Finite R N] [Module.Projective R N]
    (K : L → Matrix (Fin n) (Fin n) R → Prop) (hex : ∀ D, ∃ Θ, K D Θ) (huniq : ∀ D Θ Θ', K D Θ → K D Θ' → Θ = Θ')
    (hlin : ∀ D D' (r : R) Θ Θ', K D Θ → K D' Θ' → K (D + D') (Θ + Θ') ∧ K (r • D) (r • Θ))
    (hN : ∀ D Θ, K D Θ → Θ ∈ N)
    (hrk : ∀ m : Ideal R, m.IsMaximal →
      Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] L) = Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] N))
    (hfib : ∀ D Θ (m : Ideal R), m.IsMaximal → K D Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule R L)) :
    ∃ e : L ≃ₗ[R] N, ∀ D Θ, K D Θ ↔ Θ = (e D).1 := by
  classical
  choose Θ hΘ using hex
  let f : L →ₗ[R] N :=
    { toFun := fun D => ⟨Θ D, hN D _ (hΘ D)⟩
      map_add' := fun D D' => Subtype.ext (huniq _ _ _ (hΘ (D + D')) (hlin D D' 1 _ _ (hΘ D) (hΘ D')).1)
      map_smul' := fun r D => Subtype.ext (huniq _ _ _ (hΘ (r • D)) (hlin D D r _ _ (hΘ D) (hΘ D)).2) }
  have hf : Function.Bijective f :=
    GlobalTheory.ProjBij.bijective_of_injective_mod_maximal R L N f hrk
      (fun m hm x hx => hfib x (Θ x) m hm (hΘ x) (entry_mem_of_mem_smul_top N m (f x) hx))
  refine ⟨LinearEquiv.ofBijective f hf, fun D Θ' => ⟨fun h => huniq D Θ' (Θ D) h (hΘ D), fun h => ?_⟩⟩
  rw [h]
  exact hΘ D


set_option maxHeartbeats 2000000 in
theorem hasLogKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → HasLogKS Y.t Y.s (interior Y) := by
  intro E _ _ _ H Dw l Xo c Y hr hsm hsnc hrig
  unfold HasLogKS
  intro U n v A hv hb hA
  obtain ⟨hLf, hLp, hLr⟩ := GlobalTheory.LogDerProj.main E H Dw l Xo c Y hr hsm hsnc U
  obtain ⟨hBf, hBp, hBr⟩ := _root_.GlobalTheory.BalProj.balanced_finite_projective_rank E H Dw l Xo c Y hr hsm hsnc U n v A hv hb hA
  exact exists_equiv (balanced H.bar A) (fun D Θ => IsKS Y.t (interior Y) U v D.1 Θ)
    (_root_.GlobalTheory.KReg.exists_isKS_regular E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)
    (GlobalTheory.KSUniq.isKS_unique_model E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)
    (GlobalTheory.LogKSLin.isKS_linear E H Dw l Xo c Y U n v A hv hb hA)
    (GlobalTheory.LogKSBal.ksClass_mem_balanced E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)
    (fun m hm => (hLr m hm).trans (hBr m hm).symm)
    (_root_.GlobalTheory.logKS_inj_mod_maximal E H Dw l Xo c Y hr hsm hsnc hrig U n v A hv hb hA)

end GlobalTheory.LogKSAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesNoetherianLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelFamLocal

theorem exists_point_of_principal : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F R _ _ _ β c hc
  haveI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  haveI : Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine _root_.GlobalTheory.SiegFpqcDesc.classified_of_faithfullyFlat g n hg hn hodd F R (AdicCompletion (IsLocalRing.maximalIdeal R) R) β c hc ?_
  intro c' hc'
  have hp : c'.Principal := GlobalTheory.SiegLevCalc.sRel_principal ((sRel_one_one_iff c' c _).2 hc') hc
  exact _root_.GlobalTheory.SFamCompl.classified_of_complete g n hg hn hodd F (AdicCompletion (IsLocalRing.maximalIdeal R) R) inferInstance
    ((algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)).comp β) c' hp

end GlobalTheory.SiegelFamLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleFactorStepSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStep

theorem gbig_three {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

end GlobalTheory.SqStep

end
end

