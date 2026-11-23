module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0029
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverDvrExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentValuationFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeOne
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeTwo
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0018
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlace
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentGenericFibre
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0023
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ArithmeticRelationsStatementHolds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0103
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFlagCmTypeDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0079
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0060

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyUniformisation
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem chart_comp_eq {h : GenFrEx Xo c} {Z : Comp Xo c} (C : GlobalTheory.Reg.FChart h) (ψ : C.R →ₐ[c.F] Om Z)
    (z : FrPt Xo c (Om Z)) (t : Ix Dw → (Om Z)ˣ) (hz : FrMap ψ C.y z) (ht : FrBor t z (genFr h Z)) :
    C.Z = Z := by
  by_contra hne
  let s₀ : Sp (Om Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om Z))
  refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c C.Z Z hne) ?_ (GlobalTheory.AllWt.liesOn_genFr h Z s₀)
  rw [GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap hz, Scheme.Hom.comp_apply]
  let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
  let sC : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
  have he : spMap C.R.val.toRingHom sC = η :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
  have hη : GlobalTheory.AllWt.ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
    have hgen := GlobalTheory.AllWt.liesOn_genFr h C.Z sC
    rw [← GlobalTheory.UnifComp.ptF_frBor C.bor, GlobalTheory.UnifComp.ptF_frMap C.gen,
      Scheme.Hom.comp_apply, he] at hgen
    exact hgen
  have hspec : η ⤳ spMap ψ.toRingHom s₀ :=
    (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
  exact (hspec.map (GlobalTheory.AllWt.ptF C.y).continuous).mem_closed
    (isClosed_of_mem_irreducibleComponents _ C.Z.2) hη

attribute [local instance 1100] Subalgebra.algebra in
theorem comp_eq_of_algClosedAt (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h : GenFrEx Xo c)
    (Z : Comp Xo c) (hac : ∀ a : Om Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range)
    (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom)
    (hk : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y')
    (hk' : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k' x') y') : k = k' := by
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  obtain ⟨C, ψ, z, t, hz, ht⟩ := hA h (Om Z) (genFr h Z)
  have hCZ : C.Z = Z := chart_comp_eq C ψ z t hz ht
  have : Algebra.Smooth c.F C.R := C.sm
  have hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ))
      (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') →
      ∃ f : C.R → ℂ, GlobalTheory.GeomConn.ReadOn (Formalism.L2.PjFree.Unf.ofPj U) C.y f k := by
    rintro k x ⟨φ, y', t', hy', ht'⟩
    obtain ⟨w, hw⟩ := hL.bc _ _ φ z
    exact ⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw,
      hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩
  obtain ⟨f, hf⟩ := hread k x hk
  obtain ⟨f', hf'⟩ := hread k' x' hk'
  refine GlobalTheory.GeomConn.ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'
  have hac' : ∀ a : Om C.Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om C.Z)).range := by
    rw [hCZ]; exact hac
  exact GlobalTheory.GeomConn.isPreconnected_points_over C.R.val Subtype.val_injective hac' σ

end GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp

theorem GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp.comp_iff_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Comp Xo c) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), 1 ≤ r → IsUnf U → (∀ b : Om Z, IsAlgebraic c.F b → b ∈ (algebraMap c.F (Om Z)).range) → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → (Set.range y ⊆ (Z : Set (Xo.XF c)) ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) := by
  intro E _ _ _ H D l Xo c Z r U h1 hU hac
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨-, -, hcov, -, -, g, e, F, ik, φ, hEF, hP⟩ := id hU
  have hty : IsTypeFn H D.p D.q (fun j => relab c c.F.val.toRingHom (e j).1) :=
    (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 D g e
  have hinj := (GlobalTheory.CompBij.ik_bijective E H D l Xo c _ r U h1 hσ hU g e F ik φ hEF
    fun k x => (hP k x).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩).1
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
  choose q hq using GlobalTheory.UnifComp.exists_liesOn (Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model (Formalism.L2.PjFree.Unf.ofPj U) hU hG Z
  have hqk : q k = Z := GlobalTheory.UnifComp.eq_of_carries hk (hq k)
  have huniq : ∀ k', q k' = Z → k' = k := by
    intro k' hk'
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hG k'
    obtain rfl : Z' = Z := (GlobalTheory.UnifComp.eq_of_carries hZ' (hq k')).symm.trans hk'
    obtain ⟨P, w, x, t, hw, ht⟩ := hk
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp.comp_eq_of_algClosedAt U hσ hU hG Z' hac k' k x' x
      ⟨P', w', t', hw', ht'⟩ ⟨P, w, t, hw, ht⟩
  have hfr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      ∃ (k' : U.Comp) (x : (U.X k').dom) (t : Ix D → (CAt c.F.val.toRingHom)ˣ)
        (z : FrPt Xo c (CAt c.F.val.toRingHom)),
        FrBor t (U.un k' x) z ∧ z.x = under y ∧ GlobalTheory.AllWt.ptF z = y := by
    intro y hy
    have hover : under y ≫ Xo.s = sOf c ℂ := by
      show (y ≫ pullback.fst _ _) ≫ Xo.s = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, sOf, ← Spec.map_comp]
      rfl
    obtain ⟨z, hz⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (under y) hover
    obtain ⟨k', x, t, hb⟩ := hcov z
    refine ⟨k', x, t, z, hb, hz, ?_⟩
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hz
    · exact (pullback.lift_snd _ _ _).trans hy.symm
  refine ⟨g, _, F, ik k, hty, fun y hy => ⟨fun hZ => ?_, fun ⟨P, hP', hPy⟩ => ?_⟩⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    have hk' : q k' = Z := by
      by_contra hne
      let s₀ : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) ?_ (hZ ⟨s₀, rfl⟩)
      have := hq k' x s₀
      change GlobalTheory.AllWt.ptF (U.un k' x) s₀ ∈ _ at this
      rwa [← GlobalTheory.UnifComp.ptF_frBor hb, hzy] at this
    obtain rfl := huniq k' hk'
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    exact ⟨Pm, hPm, hzx.symm.trans (hb.1.trans hx)⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    have e1 : ik k' = ik k := F.disj _ _ Pm P hPm hP' (hx.symm.trans (hb.1.symm.trans (hzx.trans hPy)))
    obtain rfl := hinj e1
    rintro _ ⟨s, rfl⟩
    rw [← hqk, ← hzy, GlobalTheory.UnifComp.ptF_frBor hb]
    exact hq k' x s
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamily
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel

theorem model_on_hodge_of_family_pos : FamilyExistsPos → HodgeLatticeFlagBound := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV _ _ Fl S₀ T hT p hpS hpS₀ hHT hp2 hdisc φ hφ A _ _ _
  intro m _ hm O _ _ _ _ _ _ _
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · haveI : IsEmpty (Fin (D.p + D.q)) := by rw [h0]; exact Fin.isEmpty'
    intro τ k _ Q _
    have h1 : ((T.map (Int.castRingHom O)).comp fun i : Fin (D.p + D.q) => (τ, i)).ck (pointIdeal O y) k Q = 0 := by
      simp [LocPair.ck, GroundTheory.Heights₂.Heights.NumbersDVR.pairNum]
    have h3 : ∀ τ', liePs (Ψ := CMType H) (N := D.p + D.q) D.p (k - 1) τ' = 0 := by
      rintro (τ' | τ') <;> simp [liePs]
    have h2 : bracket (N := D.p + D.q) D.p φ p k τ = 0 := by
      simp [bracket, h3]
    rw [h1, h2]
    simp [cycNum]
  have hpP : p.Prime := 𝔐.S_prime p hpS
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨hAD, hAfin, hAinj, hAcst, hloc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.const_closure E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  haveI := hAD
  haveI := hAfin
  obtain ⟨hOint, hOfn⟩ := hloc m O
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hModel, hVert⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.pl_model K J Ω y A hAinj hAcst d hV m O
  have hT2 := hT
  obtain ⟨hS₀, hvb, hsub, e₀, e, hR₀, hR, hfg, hvo⟩ := hT2
  have hTv := hVert ϖ hϖ _ _ T hvo
  have hOinj : Function.Injective (algebraMap O Ω) := hOint.1
  have hb : ∀ t, LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t :=
    _root_.GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FlagBasis.flag_b_basis E H D l Xo c O₀ β Y S Ω K J y 𝔐 Fl
  have hfam := hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV hpos Fl.b hb p hpS hHT hp2 hdisc φ hφ A m hm O
  choose Sg hSg ε φ' F hF1 hF2 hF3 w σ Df hDf using hfam
  have hFc : ∀ t, 0 < Fintype.card (F t) - 1 := fun t => by
    have := Fintype.one_lt_card (α := F t)
    omega
  have hN0 : 0 < ∏ t, (Fintype.card (F t) - 1) := Finset.prod_pos fun t _ => hFc t
  obtain ⟨O', _, _, _, _, _, _, Ω', _, _, _, _, _, _, ζ, hO'inj, hζ, hadj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.exists_ext_primitive_root O Ω hOinj _ hN0
  have hζt : ∀ t, IsPrimitiveRoot (ζ ^ ((∏ t, (Fintype.card (F t) - 1)) / (Fintype.card (F t) - 1)))
      (Fintype.card (F t) - 1) := fun t =>
    hζ.pow hN0 (Nat.div_mul_cancel
      (Finset.dvd_prod_of_mem (fun t => Fintype.card (F t) - 1) (Finset.mem_univ t))).symm
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  haveI : CharZero Ω' := charZero_of_injective_ringHom (algebraMap Ω Ω').injective
  haveI : CharZero O' := (algebraMap O' Ω').charZero
  have hModel' := (_root_.GlobalTheory.CompanionTheory.Ar.Num.model_baseChange_algebraic O Ω K J y d hModel hOint O' Ω' hO'inj).2
  have hfn' := _root_.GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.FnExt.fnField_top_of_adjoin_root O Ω K J y hOfn O' Ω' ζ hadj
  have hTwin : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O'
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O' (fun v => algebraMap Ω Ω' (y v))) d :=
    (GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O' _ d).2 ⟨hV.1, hModel'⟩
  have hagree : ∀ s (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) → 𝔐.HT p s q = 𝔐.dR s q :=
    _root_.GlobalTheory.CompanionTheory.Ar.Top.HodgeModel.HtDr0.ht_eq_dR_of_not_inFibre E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
  have hLat := _root_.GlobalTheory.CompanionTheory.Ar.TwoLevelLat.latFlagPair_of_twoLevels E H D l Xo c O₀ β Y S Ω K J y 𝔐 Fl S₀ T hT p hpS hpS₀ hagree
  have hag2 : ∀ s, ∀ q : Cpt 𝔐.ξ, q ∈ overPrime 𝔐.ξ p → ¬ InFibre 𝔐.ξ p q → 𝔐.dR s q = 𝔐.HT p s q := by
    intro s q hq hqp
    refine (hagree s q fun p' hp' => ?_).symm
    by_cases h : p' = p
    · subst h; exact hqp
    · exact hq p' hp' h
  have hB := fun s => _root_.GlobalTheory.CompanionTheory.Ar.CoordRead.flagPair_coord 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie d hV A hAinj hAcst p hpP m hm O ϖ hϖ 𝔐.Li
    (labelRk D s) (Fl.b s) (hb s).1 (𝔐.dR s) (𝔐.HT p s) (labelPair D T s) (hLat s) (hag2 s)
  choose B B' v v' hBlat hBfp using hB
  have hC := fun s : CMType H ⊕ CMType H => _root_.GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair O Ω K J y ϖ _ (B s.swap) (B' s.swap) (v s.swap) (v' s.swap) _ _ _ _
    (hBfp s.swap)
  choose C C' u u' hClat hCfp using hC
  have hmm : ∀ {σ' : Type} (Q : LocPair J ℤ σ'),
      (Q.map (Int.castRingHom O)).map (algebraMap O O') = Q.map (Int.castRingHom O') := by
    intro σ' Q
    rw [map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hE := fun s => _root_.GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt.flagPair_ext O Ω K J y d hModel hOint O' Ω' hO'inj ϖ ϖ' hϖ hϖ' _ (B s) (B' s) (v s)
    (v' s) ((labelPair D T s).map (Int.castRingHom O)) (hBfp s)
  choose LB LB' lv lv' hLBlat hLBfp using hE
  have hE2 := fun s => _root_.GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt.flagPair_ext O Ω K J y d hModel hOint O' Ω' hO'inj ϖ ϖ' hϖ hϖ' _ (C s) (C' s) (u s)
    (u' s) ((omPair D T s).map (Int.castRingHom O)) (hCfp s)
  choose LC LC' lu lu' hLClat hLCfp using hE2
  have hRel : ∀ t, Relations (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (φ' t)
      (fun τ => (labelPair D T (ε t τ)).map (Int.castRingHom O'))
      (fun τ => (omPair D T (ε t τ)).map (Int.castRingHom O')) := by
    intro t
    obtain ⟨-, -, hpre, hfamOf⟩ := hDf t
    obtain ⟨χ, Df', hM3, hspan⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.PreFamExt.main O Ω K J y d hModel hOint O' Ω' hO'inj (F t) p _ (hζt t)
      (D.p + D.q) (Sg t) _ _ (w t) (σ t) (φ' t) (Df t) hpre
    refine _root_.GlobalTheory.CompanionTheory.Ar.Num.TopRel.relations O' Ω' K J (fun v => algebraMap Ω Ω' (y v)) ϖ' hϖ' d hTwin hfn' p hpP
      (algebraMap O O' (w t)) χ (φ' t) Df' hM3
      (fun τ => LB (ε t τ)) (fun τ => LB' (ε t τ)) (fun τ => LC (ε t τ)) (fun τ => LC' (ε t τ)) ?_ _ _ ?_
    · intro τ c hc
      have hc' : segreVec y c ≠ 0 := by
        intro h
        apply hc
        show ∏ k, algebraMap Ω Ω' (y ⟨k, c k⟩) = 0
        rw [← map_prod]
        exact (congrArg (algebraMap Ω Ω') h).trans (map_zero _)
      obtain ⟨hl, hW, ho, hoh⟩ := hfamOf c hc' τ
      obtain ⟨s1, s2, s3, s4⟩ := hspan c hc' τ
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [(hLBlat _ c hc').1, (hBlat _ c hc').1, s1, hl]; rfl
      · rw [(hLBlat _ c hc').2, (hBlat _ c hc').2, s2, hW]; rfl
      · rw [(hLClat _ c hc').1, (hClat _ c hc').1, (hBlat _ c hc').1, s3, ho]; rfl
      · rw [(hLClat _ c hc').2, (hClat _ c hc').2, (hBlat _ c hc').2, s4, hoh]; rfl
    · intro τ
      refine ⟨⟨lv (ε t τ), lv' (ε t τ), ?_⟩, ⟨lu (ε t τ), lu' (ε t τ), ?_⟩⟩
      · have h := hLBfp (ε t τ)
        rw [hmm] at h
        exact h
      · have h := hLCfp (ε t τ)
        rw [hmm] at h
        exact h
  have hLoc : LabelChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p φ
      (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPair D T s).map (Int.castRingHom O')) := by
    refine GlobalTheory.T.local_comparison_of_orbits_holds O' K J (CMType H ⊕ CMType H) _ d p hpP.two_le φ _ _ _ _ fun τ => ?_
    obtain ⟨hrange, hcomm, -, -⟩ := hDf τ
    exact ⟨Sg τ, inferInstance, ε τ, φ' τ, hrange, hcomm, hRel τ⟩
  have hLoc2 : LabelChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p φ
      (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPairM D T s).map (Int.castRingHom O')) := by
    intro k hk Q hQ τ
    rcases τ with τ | τ
    · exact hLoc k hk Q hQ (.inl τ)
    · exact hLoc k hk Q hQ (.inr τ)
  have hp0' : (p : O') ≠ 0 := Nat.cast_ne_zero.2 hpP.ne_zero
  have hFlag' := _root_.GlobalTheory.CompanionTheory.Ar.Num.flag_m3_of_local_m3 O' ϖ' hϖ' K J _ d hModel' p hp0' (CMType H) D.p D.q φ (T.map (Int.castRingHom O'))
    (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPairM D T s).map (Int.castRingHom O'))
    (fun τ => rfl)
    (fun τ => by
      show (dualRev (dualRev (T.comp _))).map _ = _
      rw [dualRev_dualRev]
      rfl)
    (fun τ k Q _ => (_root_.GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm O' K J D.q Fin.revPerm _ k Q).1 (p : O')
      (fun i => -(T.map (Int.castRingHom O')).x (τ, Fin.natAdd D.p i)))
    hLoc2
  have hT' : FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p D.p φ
      ((T.map (Int.castRingHom O)).map (algebraMap O O')) := by
    rw [hmm]
    exact hFlag'
  exact (_root_.GlobalTheory.CompanionTheory.Ar.Num.model_descends_from_dvr_ext O Ω K J y d hModel hOint O' Ω' hO'inj ϖ hϖ p).1 hpP.ne_zero (CMType H) (D.p + D.q) D.p φ
    (T.map (Int.castRingHom O)) hTv hT'

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
end

