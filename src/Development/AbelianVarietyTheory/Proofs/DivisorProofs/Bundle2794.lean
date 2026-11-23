module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemOfUniversalSectionBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelModuliTraitThroughCompactificationPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

theorem exists_complete_dvr_of_local (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : A →+* W), Function.Injective ψ ∧ IsLocalHom ψ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, ?_, PowerSeries.C,
      RingHom.injective _, inferInstance⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, φ, h1, h2⟩

theorem exists_trait_at : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n))
    [LocallyOfFiniteType s] [IsLocallyNoetherian S] (j : F.X ⟶ S) [IsOpenImmersion j], 3 ≤ n → Dense (Set.range j) →
    j ≫ s = F.s → ∀ x : S, ∃ (T : GlobalTheory.Poinc.Trait F) (ξT : Sp T.V ⟶ S) (b : cycAway n →+* T.V),
      ξT (closedPoint T.V) = x ∧ jK T.V ≫ ξT = T.y ≫ j ∧ ξT ≫ s = spMap b := by
  intro g n F S s _ _ j _ _ hd hjs x
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : Flat F.s := inferInstance
  obtain ⟨_, ⟨y0, rfl⟩, hw⟩ :=
    GlobalTheory.BlowOpen.exists_specializes_of_dense_scheme S _ j.isOpenEmbedding.isOpen_range hd x
  obtain ⟨y1, hy1, e1⟩ := Flat.generalizingMap F.s (genericPoint_specializes (F.s y0))
  have hη : j y1 ⤳ x := (hy1.map j.continuous).trans hw
  obtain ⟨q, hq⟩ : j y1 ∈ Set.range (S.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hη
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : IsLocalRing (S.presheaf.stalk x ⧸ q.asIdeal) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨W, _, _, _, hWc, ψ, hψi, hψl⟩ := exists_complete_dvr_of_local (S.presheaf.stalk x ⧸ q.asIdeal)
  haveI : IsLocalHom (Ideal.Quotient.mk q.asIdeal) := .of_surjective _ Ideal.Quotient.mk_surjective
  let ψ' : S.presheaf.stalk x →+* W := ψ.comp (Ideal.Quotient.mk q.asIdeal)
  haveI : IsLocalHom ψ' := RingHom.isLocalHom_comp _ _
  let ξ0 : Sp W ⟶ S := spMap ψ' ≫ S.fromSpecStalk x
  have hξc : ξ0 (closedPoint W) = x := by
    show S.fromSpecStalk x (spMap ψ' (closedPoint W)) = x
    have e : spMap ψ' (closedPoint W) = closedPoint (S.presheaf.stalk x) := IsLocalRing.comap_closedPoint ψ'
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint
  have hξg : ξ0 (⊥ : PrimeSpectrum W) = j y1 := by
    show S.fromSpecStalk x (spMap ψ' (⊥ : PrimeSpectrum W)) = j y1
    have : spMap ψ' (⊥ : PrimeSpectrum W) = q := by
      apply PrimeSpectrum.ext
      show Ideal.comap ψ' ⊥ = q.asIdeal
      rw [← RingHom.ker_eq_comap_bot, RingHom.ker_comp_of_injective _ hψi, Ideal.mk_ker]
    rw [this, hq]
  have hjKbot : ∀ pt : Sp (FractionRing W), jK W pt = (⊥ : PrimeSpectrum W) := fun pt => by
    apply PrimeSpectrum.ext
    have hpt : pt = (⊥ : PrimeSpectrum (FractionRing W)) := Subsingleton.elim (α := PrimeSpectrum (FractionRing W)) _ _
    subst hpt
    show Ideal.comap (algebraMap W (FractionRing W)) ⊥ = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W (FractionRing W))
  have hrange : Set.range (jK W ≫ ξ0) ⊆ Set.range j := by
    rintro _ ⟨pt, rfl⟩
    rw [Scheme.Hom.comp_apply, hjKbot, hξg]
    exact ⟨y1, rfl⟩
  let y : Sp (FractionRing W) ⟶ F.X := IsOpenImmersion.lift j (jK W ≫ ξ0) hrange
  have hy : y ≫ j = jK W ≫ ξ0 := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (ξ0 ≫ s)
  let b0 : cycAway n →+* W := θ.hom
  have hb0 : spMap b0 = ξ0 ≫ s := hθ
  have hb0i : Function.Injective b0 := by
    have h1 : (spMap b0) (⊥ : PrimeSpectrum W) = genericPoint (Sp (cycAway n)) := by
      rw [hb0]
      exact (Scheme.Hom.comp_apply ξ0 s _).trans (by rw [hξg, ← Scheme.Hom.comp_apply, hjs, e1])
    rw [genericPoint_eq_bot_of_affine] at h1
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    exact congrArg PrimeSpectrum.asIdeal h1
  haveI : CharZero W := charZero_of_injective_ringHom hb0i
  have hBase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hfl, -, hcomp, hTy⟩ := _root_.GlobalTheory.Poinc.traitExtSt g n (cycAway n) (zetaAway n) F W hBase inferInstance y
  haveI := hfl
  refine ⟨T, spMap f ≫ ξ0, f.comp b0, ?_, ?_, ?_⟩
  · show ξ0 (spMap f (closedPoint T.V)) = x
    have e : spMap f (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    rw [e, hξc]
  · have key : jK T.V ≫ spMap f = spMap fK ≫ jK W := by
      simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      exact (hcomp a).symm
    rw [hTy, Category.assoc, hy, ← Category.assoc, key, Category.assoc]
  · rw [Category.assoc, ← hb0]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.TChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveDiagonalLatticeMapTrait
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

namespace GlobalTheory.Poinc.Eq8.TraitOne

theorem factor_stalk (X : Scheme.{0}) (x : X) (V : Type) [CommRing V] [IsLocalRing V] (ξ : Sp V ⟶ X)
    (hx : ξ (IsLocalRing.closedPoint V) ⤳ x) :
    ∃ f : X.presheaf.stalk x →+* V, spMap f ≫ X.fromSpecStalk x = ξ := by
  refine ⟨(Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.stalkSpecializes hx).hom, ?_⟩
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hx
  conv_rhs => rw [← e1, ← e2]
  show Spec.map (CommRingCat.ofHom _) ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  rw [← Spec.map_comp]
  rfl

theorem subset_abLocus {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real}
    {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) :
    (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  intro z hz
  obtain ⟨z', rfl⟩ : z ∈ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hz
  rw [abLocus_pullback (G' := (Over.pullback FinalForm.u₀).obj ρ.P.A) abLocusOne FinalForm.semi FinalForm.cart.1]
  intro K _ _ t _
  haveI := ρ.P.isAb.proper
  show IsProper (pullback.snd (pullback.snd ρ.P.A.hom FinalForm.u₀) t)
  infer_instance

theorem main : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X), (∀ a b, ∃ (f : FinalForm.G ⟶ FinalForm.G) (fR : G ⟶ G), MatOn FinalForm pr a b f ∧ IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR (m a b)) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ (Fin 8 → T.D.toPre.X)), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (g' r) (h T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ hA S ρ hBig M U₀ EE FinalForm hAdm hEE x hx u c pr hS R _ _ _ j hR hj G _ _ gm hgm
    D A U hLB hPsi m hm T ξ hξU hsp
  set ξR : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξR
  obtain ⟨hft, hpj⟩ := GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar o' Ω M x hx
  obtain ⟨-, p, hp, hpm⟩ := hpj R j hj
  obtain ⟨f, hf⟩ := factor_stalk M.Z x T.V ξ hsp
  obtain ⟨V', _, _, _, h, g', hc, hinj, hloc, hcomp, hirr⟩ :=
    GlobalTheory.TraitLift.exists_lift_of_isCpl (M.Z.presheaf.stalk x) R T.V j hj f
  have heq : spMap g' ≫ ξR = spMap h ≫ ξ := by
    rw [hξR, ← hf, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp', hcomp]
  haveI : CharZero V' := (RingHom.charZero_iff hinj).1 inferInstance
  have hBV : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  have hle : nonZeroDivisors T.V ≤ (nonZeroDivisors V').comap h :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective h hinj
  let hK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (FractionRing V') h hle
  have hKc : ∀ a, hK (algebraMap T.V _ a) = algebraMap V' _ (h a) := IsLocalization.map_eq hle
  have hjK : spMap hK ≫ jK T.V = jK V' ≫ spMap h := by
    show spMap hK ≫ spMap (algebraMap T.V (FractionRing T.V)) = spMap (algebraMap V' (FractionRing V')) ≫ spMap h
    rw [← spMap_comp', ← spMap_comp']
    congr 1
    ext a
    exact hKc a
  obtain ⟨ξ₀, hξ₀, hξ₀y⟩ := hξU
  set ξ' : Sp V' ⟶ M.Z := spMap g' ≫ ξR with hξ'
  have hξ₀' : (spMap hK ≫ ξ₀) ≫ U₀.ι = jK V' ≫ ξ' := by
    rw [Category.assoc, hξ₀, ← Category.assoc, hjK, Category.assoc, heq]
  have hsub := subset_abLocus FinalForm
  let w' : Sp V' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V')
  have hw'U : ξ' w' ∈ (U₀ : Set M.Z) := by
    have e1 : w' = jK V' (IsLocalRing.closedPoint (FractionRing V')) := by
      apply PrimeSpectrum.ext
      show (⊥ : Ideal V') = Ideal.comap (algebraMap V' (FractionRing V')) (IsLocalRing.closedPoint (FractionRing V')).asIdeal
      rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint (FractionRing V')).asIdeal, ← RingHom.ker_eq_comap_bot]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V' (FractionRing V'))).symm
    rw [e1]
    show (jK V' ≫ ξ') (IsLocalRing.closedPoint (FractionRing V')) ∈ (U₀ : Set M.Z)
    rw [← hξ₀']
    show U₀.ι ((spMap hK ≫ ξ₀) (IsLocalRing.closedPoint (FractionRing V'))) ∈ (U₀ : Set M.Z)
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  obtain ⟨D', A', U', hLB', hPsi'⟩ := FinalForm.unif V' inferInstance inferInstance hc ξ' ⟨w', hsub hw'U⟩
  have hG'semi : IsSemiAbelian ((Over.pullback ξ').obj FinalForm.G) := IsSemiAbelian.pullback ξ' FinalForm.G FinalForm.semi
  have hpb' := isGrpPullback_pullback FinalForm.G ξ'
  have h'' : IsGrpPullback ((Over.pullback (spMap g')).obj G) FinalForm.G ξ' (pullback.fst G.hom (spMap g') ≫ gm) :=
    (isGrpPullback_pullback G (spMap g')).comp hgm
  obtain ⟨e, he1, he2⟩ := grpPullback_iso hpb' h''
  haveI := he1
  set β : ((Over.pullback ξ').obj FinalForm.G).left ⟶ G.left := e.hom.left ≫ pullback.fst G.hom (spMap g') with hβdef
  have hβ : IsGrpPullback ((Over.pullback ξ').obj FinalForm.G) G (spMap g') β :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G (spMap g'))).congr (Category.id_comp _) rfl
  have hβgm : β ≫ gm = pullback.fst FinalForm.G.hom ξ' := by
    rw [hβdef, Category.assoc, he2]
  clear_value β
  have hGsemi : IsSemiAbelian G := by
    obtain ⟨e2, he21, -⟩ := grpPullback_iso hgm (isGrpPullback_pullback FinalForm.G ξR)
    haveI := he21
    exact GlobalTheory.isSemiAbelian_of_grpIso e2 (IsSemiAbelian.pullback ξR FinalForm.G FinalForm.semi)
  have hLBβ : LBIso U'.LG.L (U.LG.L.pull β) := by
    have h1 : LBIso (U.LG.L.pull β) (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ')) :=
      GlobalTheory.Ex.GenericFibre.lbIso_pull hLB β hβgm.symm
    exact LBIso.trans U'.LG.isLB (pull_isLB FinalForm.L.isLB _) (pull_isLB U.LG.isLB _) hLB' (LBIso.symm h1)
  have hWo : IsOpen (ξR ⁻¹' (U₀ : Set M.Z)) := U₀.isOpen.preimage ξR.continuous
  have hPsiWo : ∀ y, PsiUnitOn D.toPre y (ξR ⁻¹' (U₀ : Set M.Z)) := fun y j' V hV hVW =>
    hPsi y j' V hV (hVW.trans (Set.preimage_mono hsub))
  have hker : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ ξR ⁻¹' (U₀ : Set M.Z) := by
    have e3 : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) = spMap g' w' :=
      PrimeSpectrum.ext (RingHom.ker_eq_comap_bot g')
    show ξR _ ∈ (U₀ : Set M.Z)
    rw [e3]
    exact hw'U
  obtain ⟨ρ0, hsurj, hcoord, hequiv⟩ := _root_.GlobalTheory.Poinc.Eq8.GenRestrict.exists_surjective_coordMap_equivMap R hR G hGsemi D A U V' hBV inferInstance
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' g' β p hp hpm _ hWo hPsiWo hker hβ hLBβ
  obtain ⟨c', pr', hS', hmat⟩ := GlobalTheory.Poinc.Eq8.PullAlong.main g n _ _ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm V' hBV
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' ξ' (pullback.fst FinalForm.G.hom ξ') hpb' hLB' (spMap hK ≫ ξ₀) hξ₀'
  have hpt : (spMap hK ≫ ξ₀) ≫ FinalForm.u₀ ≫ u = spMap hK ≫ T.y := by
    rw [Category.assoc, hξ₀y]
  have key : ∀ (v : Sp (FractionRing V') ⟶ F.X), v = spMap hK ≫ T.y → ∀ c₁ pr₁, SharpBy F W A' v c₁ pr₁ →
      ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧
        Associated r (h T.ϖ ^ (qW W T.β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G)
        (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr₁ a b f₁ →
        (Over.pullback (jK V')).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
    rintro v rfl c₁ pr₁ hS₁
    exact _root_.GlobalTheory.Poinc.TraitPow.exists_equiv g n _ _ F W hW T V' hBV inferInstance _ hG'semi D' A' U' h hK hloc hKc c₁ pr₁ hS₁
  obtain ⟨e8, hord, hrel⟩ := key _ hpt c' pr' hS'
  refine ⟨V', inferInstance, inferInstance, inferInstance, h, g', e8.toAddMonoidHom.comp ρ0, hinj, hirr _ T.irr, heq,
    e8.surjective.comp hsurj, ?_, ?_⟩
  · intro y r hr
    obtain ⟨⟨r', hr', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main V' D' inferInstance (ρ0 y)
    obtain ⟨h0, has⟩ := hord (ρ0 y) r' hr'
    exact ⟨h0, (hcoord y r r' hr hr').trans has⟩
  · intro a b y
    obtain ⟨f, fR, hMO, hfR, hcomm, hEC⟩ := hm a b
    haveI : IsMonHom f := hMO.1
    let f' : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G := (Over.pullback ξ').map f
    have hf'fst : f'.left ≫ pullback.fst FinalForm.G.hom ξ' = pullback.fst FinalForm.G.hom ξ' ≫ f.left := pullback.lift_fst _ _ _
    have hf' : IsMonHom f' := PullGtPf.isMonHom_of_grpPullback hpb' hpb' f f' hf'fst
    have hf'β : f'.left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc (f'.left ≫ β) ≫ gm = f'.left ≫ (β ≫ gm) := Category.assoc _ _ _
          _ = pullback.fst FinalForm.G.hom ξ' ≫ f.left := by rw [hβgm, hf'fst]
          _ = (β ≫ gm) ≫ f.left := by rw [hβgm]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, Category.assoc, hcomm]
      · calc (f'.left ≫ β) ≫ G.hom = f'.left ≫ (β ≫ G.hom) := Category.assoc _ _ _
          _ = ((Over.pullback ξ').obj FinalForm.G).hom ≫ spMap g' := by rw [hβ.1.w, ← Category.assoc, Over.w f']
          _ = β ≫ G.hom := hβ.1.w.symm
          _ = (β ≫ fR.left) ≫ G.hom := by rw [Category.assoc, Over.w fR]
    obtain ⟨m', hm'⟩ := endChar_exists_of_isMonHom V' hBV _ hG'semi D' A' U' f' hf'
    have hq := hequiv fR f' hfR hf' hf'β (m a b) m' hEC hm' y
    obtain ⟨f₁, hf₁, hf₁c⟩ := hmat a b f f' hMO hf'fst
    have hr := hrel a b f' f₁ m' hf' hf₁ hf₁c hm' (ρ0 y)
    simpa [hq] using hr

end GlobalTheory.Poinc.Eq8.TraitOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupTowerLargeRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.TowerLarge

theorem isDiagEnd_of_isAct {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (h : IsAct X₁ act) :
    IsDiagEnd F W X₁.ρ.P X₁.u act := by
  obtain ⟨c, hc, pr, hpr, hu, hL, hact⟩ := h
  exact ⟨c, hc, pr, hpr, hu, hL, fun E a => by simpa [List.ofFn_eq_map] using hact E a⟩

theorem isAct_of_isDiagEnd {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A))
    (h : IsDiagEnd F W X₁.ρ.P X₁.u act) : IsAct X₁ act := by
  obtain ⟨c, hc, pr, hpr, hu, hL, hact⟩ := h
  exact ⟨c, hc, pr, hpr, hu, hL, fun E a => by simpa [List.ofFn_eq_map] using hact E a⟩

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem exists_tower_ge : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ N₀ : ℕ, ∃ 𝔗 : Tower X₁ act, N₀ ≤ 𝔗.X₂.S.r * 𝔗.X₂.S.N := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ _ act hact N₀
  have hε₁ := isDiagEnd_of_isAct X₁ act hact
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j₀, hk, hBk, hj₀, big⟩ := GSetup.exists_big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 N₀
  have hun1 : IsUnit (X₁.ρ.n : X₁.o₁) := by
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [hL₁]; exact dvd_pow_self _ (by omega)
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) X₁.S.unit
  haveI : CharZero X₁.Ω₁ := ArithBase.char (o := X₁.o₁)
  have hM : 0 < X₁.S.r * X₁.S.N := by rw [hL₁]; exact pow_pos hℓp.pos _
  have hζ₀ : ∃ ζ₀ : X₁.Ω₁, IsPrimitiveRoot ζ₀ (X₁.S.r * X₁.S.N) :=
    ⟨_, (X₁.S.prim.pow (by positivity) (sq _)).map_of_injective (ArithBase.inj (o := X₁.o₁) (Ω := X₁.Ω₁))⟩
  have htors : ∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp X₁.S.R) (z : Over.mk x ⟶ X₁.ρ.P.A),
      z ^ (X₁.S.r * X₁.S.N) = 1 → ∃ y : baseOver (Sp X₁.S.R) ⟶ X₁.ρ.P.A,
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp X₁.S.R)) ≫ y = z := by
    intro E _ _ x z hz
    obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij E x z hz
    exact ⟨_, ha⟩
  set j := j₀ + (j₁ + 2 * X₁.ρ.k) with hj
  set K := (X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 with hK
  have hKpos : 0 < K := by have := hℓp.pos; positivity
  obtain ⟨Ω₂, _, _, Q, φQ, ζ, fd, gal, deg, hζ, hQg, hQpb, hQlb, ⟨levQ⟩⟩ :=
    _root_.GlobalTheory.LevelPrimePower.exists_level_primePower X₁.S.R.val.toRingHom X₁.ρ.P X₁.ρ.n (X₁.S.r * X₁.S.N) K hℓp hM
      (by rw [hL₁]; exact dvd_pow_self _ (by omega)) ⟨2 * (j + 2 * k), by rw [hK]; ring⟩ hζ₀ htors
  haveI := fd
  obtain ⟨o₂, _, _, _, κ, ze, hκ, hc, hze⟩ := GlobalTheory.Poinc.exists_arithBase_rootOfUnity (o₁ := X₁.o₁) (Ω₁ := X₁.Ω₁) Ω₂ K ζ hKpos hζ
  obtain ⟨R, h, hfg, hfr, hh, hfin, hic, hstab⟩ := _root_.GlobalTheory.Poinc.NormalClosureRing.exists_integralClosure_finite X₁.S.R X₁.S.fg X₁.S.frac κ hκ hc
  haveI := GlobalTheory.ThetaReal.isNoetherian_of_fg hfg
  haveI := GlobalTheory.GenSpread.isFractionRing_of_forall_div hfr
  have hun2 : IsUnit (X₁.ρ.n : o₂) := by simpa using hun1.map κ
  have hKunit : IsUnit (K : R) := by
    have := (hun2.map (algebraMap o₂ R))
    rw [map_natCast] at this
    rw [hK]; push_cast
    exact ((this.pow _).mul ((this.pow _).pow _)).pow _
  let zeR : (↥R)ˣ := Units.map (algebraMap o₂ R).toMonoidHom ze
  have hzeR : Units.map (algebraMap R Ω₂).toMonoidHom zeR = ζ := by
    rw [← hze]; ext; rfl
  have hQpb' : IsGrpPullback Q.A X₁.ρ.P.A (spMap ((algebraMap R Ω₂).comp h)) φQ := by
    have e : (algebraMap R Ω₂).comp h = (algebraMap X₁.Ω₁ Ω₂).comp X₁.S.R.val.toRingHom := RingHom.ext hh
    rw [e]; exact hQpb
  obtain ⟨P, ψ, hPg, hpb, hlb, ⟨lev⟩⟩ := _root_.GlobalTheory.SympLevelExt.level_extends X₁.ρ.P R Ω₂ h Q φQ K zeR hKpos hKunit hQg hQpb' hQlb
    ⟨by rw [hzeR]; exact levQ⟩
  have hS := GlobalTheory.Poinc.hypS_polAV_pullback X₁.ρ.P P (spMap h) ψ hpb hlb X₁.ρ.hypS
  obtain ⟨th, hth⟩ := _root_.GlobalTheory.SecBasisPull.exists_secBasis_pull X₁.ρ.P P h ψ hpb hlb X₁.ρ.th₁ X₁.ρ.th₁_basis
  obtain ⟨S₂, ρ₂, hR, φ₂, hSR, -, -, hN₂, hr₂, hg₂, hpb₂, hlb₂⟩ :=
    _root_.GlobalTheory.ThetaSBasis.exists_real_of_secBasis o₂ Ω₂ R hfg hfr P X₁.ρ.n k j ze hℓp X₁.ρ.n_odd hk (by omega) hun2 hS th hth lev
  set om : X₁.S.R →+* S₂.R := (Subalgebra.inclusion hR).toRingHom.comp h with hom
  have hval : ∀ a, ((om a : S₂.R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => hh a
  have hcart : IsGrpPullback ρ₂.P.A X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) := by
    rw [hom, ← spMap_comp']
    exact hpb₂.comp hpb
  have hlbc : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ₂ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (lbIso_pull_comp' hlb φ₂ rfl)
  obtain ⟨ε₂, hε₂, hεc⟩ := GlobalTheory.Poinc.isDiagEnd_pullback F W X₁.ρ.P ρ₂.P X₁.u (spMap om) (φ₂ ≫ ψ) act hε₁ hcart hlbc
  have hsharp : SharpOver F W ρ₂.P (spMap om ≫ X₁.u) := by
    obtain ⟨c, hc₁, pr, hpr, hun, hLc, -⟩ := hε₂
    exact ⟨c, hc₁, pr, hpr, hun, hLc⟩
  have key : spMap S₂.R.val.toRingHom ≫ spMap om = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [spMap_comp', spMap_comp']
    congr 1
    ext a
    exact hval a
  have hgen : ∀ w, (spMap S₂.R.val.toRingHom ≫ spMap om ≫ X₁.u) w ∈ genericPoints F.X := by
    intro w
    rw [← Category.assoc, key, Category.assoc, Scheme.Hom.comp_apply]
    exact X₁.gen _
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional X₁ o₂ Ω₂ κ hκ hc
  haveI := hq
  haveI := X₁.fin
  have hcomp : M₂.pt ≫ q ≫ X₁.π = spMap S₂.R.val.toRingHom ≫ (spMap om ≫ X₁.u) ≫ i := by
    rw [← Category.assoc, hqgen, Category.assoc, X₁.comp, Category.assoc, ← Category.assoc (spMap S₂.R.val.toRingHom),
      key, Category.assoc]
  have hbase : spMap S₂.R.val.toRingHom ≫ (spMap om ≫ X₁.u) ≫ F.s =
      spMap ((algebraMap o₂ Ω₂).comp (κ.comp X₁.κ)) := by
    rw [← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, X₁.base, spMap_comp', ← RingHom.comp_assoc, ← hc]
  have hbig : S₂.Big := big j (by omega) o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : Setup F W i := Setup.mk o₂ Ω₂ S₂ ρ₂ hbig (spMap om ≫ X₁.u) hsharp hgen M₂ hMn (q ≫ X₁.π) inferInstance hcomp
    X₁.one_le X₁.three_le X₁.odd X₁.z X₁.proj X₁.normalZ X₁.imm X₁.thetaSetup_structureMap_comp X₁.dense X₁.e8 X₁.thetaInt (κ.comp X₁.κ) hbase
  set d := X₁.ρ.n ^ (j₀ + 2 * k) with hd
  have hlev : S₂.r * S₂.N = X₁.S.r * X₁.S.N * d := by
    rw [hr₂, hN₂, hL₁, hd, hj, ← pow_mul, ← pow_add, ← pow_add, mul_comm k 2]
    ring_nf
  obtain ⟨lam, hlam, hlamr⟩ := _root_.GlobalTheory.Poinc.PullLab.exists_lab_of_isGrpPullback X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) d hcart hlev
  have hRS : ∀ x : Ω₂, x ∈ S₂.R ↔ x ∈ R := fun x => by rw [hSR]
  let sR : (Ω₂ ≃ₐ[X₁.Ω₁] Ω₂) → (S₂.R →+* S₂.R) := fun σ =>
    RingHom.codRestrict (((σ : Ω₂ ≃+* Ω₂) : Ω₂ →+* Ω₂).comp S₂.R.val.toRingHom) S₂.R
      (fun x => (hRS _).2 (hstab σ x ((hRS _).1 x.2)))
  have hsR : ∀ σ, (sR σ).comp om = om := fun σ => RingHom.ext fun a => Subtype.ext
    ((congrArg σ (hval a)).trans ((σ.commutes _).trans (hval a).symm))
  choose gl hgl using fun σ => _root_.GlobalTheory.Poinc.labelHom_of_comp_eq X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) hcart (sR σ) (hsR σ)
  have hgll : ∀ σ a, gl σ (lam a) = lam a := fun σ a => _root_.GlobalTheory.Poinc.Sep.realPt_inj_of_grpPullback S₂ ρ₂ X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) hcart _ _ (by
      rw [hgl, hlam, ← Category.assoc, spMap_comp', hsR])
  let 𝔗 : Tower X₁ act :=
    { X₂ := X₂
      act₂ := ε₂
      isAct := isAct_of_isDiagEnd X₂ ε₂ hε₂
      alg := inferInstance
      fd := fd
      gal := gal
      deg := deg
      d := d
      lev := hlev
      om := om
      om_eq := hval
      om_fin := RingHom.Finite.comp (RingHom.Finite.of_surjective _ fun x => ⟨⟨x.1, (hRS _).1 x.2⟩, rfl⟩) hfin
      sR := sR
      sR_eq := fun σ a => rfl
      p := q
      p_fin := hq
      p_pt := hqgen
      p_π := rfl
      φ := φ₂ ≫ ψ
      cart := hcart
      lb := hlbc
      act_eq := hεc
      lam := lam
      lam_pt := hlam
      lam_range := hlamr
      gl := gl
      gl_pt := hgl
      gl_lam := hgll }
  refine ⟨𝔗, ?_⟩
  show N₀ ≤ S₂.r * S₂.N
  rw [hN₂, hr₂]
  exact hBk.trans (Nat.le_mul_of_pos_left _ (by have := hℓp.pos; positivity))

end GlobalTheory.Poinc.Sep.TowerLarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackEqDegreeMulIntersectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_pullback_eq_degree_mul_intersection : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter) | (exact GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter  <;> assumption)
end

