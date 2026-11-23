module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.Bundle0002
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0229
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0258
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstChernPullback
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FirstChernPullback

theorem mem_VD_pb {X X' : Scheme.{0}} (D : E.LineData X) (u : X' ⟶ X) {V : X.Opens} (hV : V ∈ 𝒱D D) :
    u ⁻¹ᵁ V ∈ 𝒱D (D.pb u) := by
  obtain ⟨σ, hσ⟩ := hV
  refine ⟨Limits.pullback.lift ((u ∣_ V) ≫ σ) (u ⁻¹ᵁ V).ι ?_, ?_⟩
  · rw [Category.assoc, hσ, morphismRestrict_ι]
  · exact Limits.pullback.lift_snd _ _ _

theorem sSup_preimage {X X' : Scheme.{0}} (𝒲 : Set X.Opens) (u : X' ⟶ X) (h : sSup 𝒲 = ⊤) :
    sSup ((fun V : X.Opens => u ⁻¹ᵁ V) '' 𝒲) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have hx : u x ∈ sSup 𝒲 := by rw [h]; trivial
  obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
  exact TopologicalSpace.Opens.mem_sSup.2 ⟨_, ⟨V, hV, rfl⟩, hxV⟩

theorem u_congr {X : Scheme.{0}} (D : E.LineData X) {A : CommRingCat.{0}} {a a' b b' : Spec A ⟶ D.Y} (ea : a = a') (eb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) :
    (Scheme.ΓSpecIso A).hom.hom (D.u a b h) = (Scheme.ΓSpecIso A).hom.hom (D.u a' b' h') := by
  subst ea eb
  rfl

end GlobalTheory.CompanionTheory.FirstChernPullback


open GlobalTheory.CompanionTheory.FirstChernPullback in
theorem GlobalTheory.CompanionTheory.FirstChernPullback.firstChern_pullback : ∀ {O O' R R' : Type} [CommRing O] [CommRing O'] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O')}
    {κ : O →+* R ⧸ I} {κ' : O' →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q' κ' σ) {p : ℕ}
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q₀ : ObjectProperty (Thick (nlFun γ' p X' q' κ'))) (hQ : Used Q₀)
    (h : ∀ T, St Q₀ {⊤} T → Q ((m.mor p).obj T)) (D : E.LineData X) (N : ℕ) (z : HO Q 2) (z' : HO (St Q₀ {⊤}) 2),
    sSup (𝒱D D) = ⊤ → IsFirstChernThickening Q D N z → IsFirstChernThickening (St Q₀ {⊤}) (D.pb m.u) N z' → (m.smor Q (St Q₀ {⊤}) h).o.pull 2 z = z' := by
  intro O O' R R' _ _ _ _ I I' γ γ' X X' q q' κ κ' σ m p Q Q₀ hQ h D N z z' hD hz hz'
  let 𝒱 : Set X'.Opens := (fun V : X.Opens => m.u ⁻¹ᵁ V) '' 𝒱D D
  have h1 : St Q₀ 𝒱 ≤ St Q₀ {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, fun _ _ => trivial⟩
  have hc : ∀ W ∈ ({⊤} : Set X'.Opens), W ≤ sSup 𝒱 := by
    rintro W rfl
    exact (sSup_preimage _ m.u hD).ge
  apply (_root_.GlobalTheory.CompanionTheory.NlZar.zariski_descent Q₀ hQ 𝒱 {⊤} h1 hc 2).2.2.1
  let G' : (St Q₀ 𝒱).FullSubcategory ⥤ (St Q₀ {⊤}).FullSubcategory := ObjectProperty.ιOfLE h1
  let sm := m.smor Q (St Q₀ {⊤}) h
  let G'' : (St Q₀ 𝒱).FullSubcategory ⥤ Q.FullSubcategory := G' ⋙ sm.G
  have hV' : ∀ T, ∃ V ∈ 𝒱D (D.pb m.u), InU V (G'.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨_, mem_VD_pb D m.u hV, hT⟩
  have hV : ∀ T, ∃ V ∈ 𝒱D D, InU V (G''.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨V, hV, hT⟩
  obtain ⟨Λ'⟩ := _root_.GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift (q := q') (b := nlBase R' I' γ' p) (ht := rfl) (κ := κ') (G' ⋙ (St Q₀ {⊤}).ι) (D.pb m.u) (fun T => by
    obtain ⟨V, ⟨s, hs⟩, hT⟩ := hV' T
    have hr : Set.range (pt (G'.obj T).obj) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hT (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt (G'.obj T).obj) hr ≫ s, ?_⟩
    rw [Category.assoc, hs, IsOpenImmersion.lift_fac]
    rfl)
  let Λ : B.CLift (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) (G'' ⋙ Q.ι) D :=
    { p := fun T => Λ'.p T ≫ Limits.pullback.fst D.f m.u
      hp := fun T => by
        have e := Λ'.hp T
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ m.u) e
      w := fun φ => Λ'.w φ
      hw := fun {T T'} φ hh => by
        have hh' : (B.thSp ((G' ⋙ (St Q₀ {⊤}).ι).map φ) ≫ Λ'.p T) ≫ (D.pb m.u).f = Λ'.p T' ≫ (D.pb m.u).f := by
          rw [Category.assoc, Λ'.hp T, Λ'.hp T']
          exact congrArg (fun y => y.1.2) ((G' ⋙ (St Q₀ {⊤}).ι).map φ).pt
        refine (Λ'.hw φ hh').trans ?_
        exact u_congr D (Category.assoc _ _ _) rfl _ hh }
  obtain ⟨hz1, hcl1⟩ := hz' _ G' hV' Λ'
  obtain ⟨hz2, hcl2⟩ := hz _ G'' hV Λ
  let ψ : CH.Mor (G' ⋙ CH.modF (sP (St Q₀ {⊤})).A) (CH.modF (sP (St Q₀ 𝒱)).A) (RingHom.id R') :=
    { G := 𝟭 _, τ := fun T => (incl h1).o.τ T, nat := fun φ x => (incl h1).o.nat φ x }
  let μ : CH.Mor (G'' ⋙ CH.modF (sP Q).A) (CH.modF (sP (St Q₀ 𝒱)).A) σ :=
    { G := 𝟭 _, τ := fun T => sm.o.τ (G'.obj T), nat := fun φ x => sm.o.nat (G'.map φ) x }
  have e1 : (incl h1).o.pull 2 z' = ψ.pull 2 ((CH.Mor.restrict (CH.modF (sP (St Q₀ {⊤})).A) G').pull 2 z') := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
    rfl
  have e2 : (incl h1).o.pull 2 (sm.o.pull 2 z) = μ.pull 2 ((CH.Mor.restrict (CH.modF (sP Q).A) G'').pull 2 z) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  have hE : μ.pullC 2 (Λ.coc (RingHom.id R) N) = ψ.pullC 2 (Λ'.coc (RingHom.id R') N) := by
    funext s
    rfl
  have b1 : CH.d _ 2 (ψ.pullC 2 (Λ'.coc (RingHom.id R') N)) = 0 := by
    rw [ψ.d_pullC, hz1, map_zero]
  have b2 : CH.d _ 2 (μ.pullC 2 (Λ.coc (RingHom.id R) N)) = 0 := by
    rw [μ.d_pullC, hz2, map_zero]
  have k1 : ψ.pull 2 ((CH.cx _).cls _ hz1) = (CH.cx _).cls _ b1 := CrystallineSemistableComparison.P.mapH_cls ψ.hom 2 _ hz1 b1
  have k2 : μ.pull 2 ((CH.cx _).cls _ hz2) = (CH.cx _).cls _ b2 := CrystallineSemistableComparison.P.mapH_cls μ.hom 2 _ hz2 b2
  have key : ∀ (a b : CH.Cn (CH.modF (sP (St Q₀ 𝒱)).A) 2) (ha : CH.d _ 2 a = 0) (hb : CH.d _ 2 b = 0), a = b →
      (CH.cx _).cls a ha = (CH.cx _).cls b hb := by
    rintro a _ ha hb rfl
    rfl
  rw [e1, e2, ← hcl1, ← hcl2, k1, k2]
  exact key _ _ b2 b1 hE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatCompEnvelopeAlgebraMap
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SitePD

theorem pdPoly_flat_comp : ∀ {A B : Type} [CommRing A] [CommRing B] (i : A →+* B), i.Flat →
    ((algebraMap B (pq B).P).comp i).Flat := by
  intro A B _ _ i hi
  have hfree : Module.Free B (pq B).P := Module.Free.of_basis (pq B).e
  have h2 : (algebraMap B (pq B).P).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  exact RingHom.Flat.comp hi h2

end GlobalTheory.CompanionTheory.SitePD
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTatePeriodNotFiltered
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem exact_degrees_of_product : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    ∀ t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l, (∀ μ, PrePer K χ μ (t μ)) →
      ∀ μ, (μ = K.1.val → t μ ∉ FB l 2) ∧ (μ ≠ K.1.val → t μ ∉ FB l 1) := by
  intro l _ K χ hN t ht
  haveI hfK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  obtain ⟨L, hLdef⟩ : ∃ L : IntermediateField ℚ_[l] (Om l),
      L = IntermediateField.normalClosure ℚ_[l] ↥K.1 (Om l) := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ_[l] ↥L := by
    subst hLdef
    infer_instance
  have hμL : ∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), μ x ∈ L := fun μ x => by
    subst hLdef
    exact μ.fieldRange_le_normalClosure ⟨x, rfl⟩
  have hKL : ∀ x ∈ K.1, x ∈ L := fun x hx => hμL K.1.val ⟨x, hx⟩
  let res : Gal(Om l/↥L) → GQ l := fun σ => σ.restrictScalars ℚ_[l]
  have hresv : ∀ (σ : Gal(Om l/↥L)) (y : ↥L), res σ y = y := fun σ y => σ.commutes y
  have hres : ∀ σ, res σ ∈ GK K := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hresv σ ⟨x, hKL x hx⟩
  obtain ⟨s, hs⟩ : ∃ s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l), ∀ μ, μ ∈ s :=
    ⟨(Set.toFinite (Set.univ : Set (↥K.1 →ₐ[ℚ_[l]] Om l))).toFinset, fun μ => by simp⟩
  have hT0 : (∏ μ ∈ s, t μ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => (ht μ).1
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2
      (GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
        GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one)
  obtain ⟨n, u, hTu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hT0 htirr
  have hTu' : ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l) := by
    rw [hTu, mul_comm]
  have hcyc : ∀ σ : Gal(Om l/↥L),
      (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot (res σ)) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) =
        (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun σ => by
    have h1 := GroundTheory.PAdicHodge.gal_smul_fontaineT σ (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h2 := GroundTheory.PAdicHodge.gal_smul_fontaineT (Formalism.Per6.toBot (res σ))
      (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h3 := h2.symm.trans h1
    exact (algebraMap ℚ_[l] (Formalism.Per6.BdRp l)).injective (mul_right_cancel₀ htirr.ne_zero h3)
  have hn : n = 1 := GlobalTheory.T.hodge_tate_character_weight L (_root_.GlobalTheory.CompanionTheory.LTPer.cycloChar_inertia_image_infinite GlobalTheory.T.sen_unramified_character_period L) u n
    (fun σ => Algebra.norm ℚ_[l] ((χ ⟨res σ, hres σ⟩ : (↥K.1)ˣ) : ↥K.1))
    (fun σ => by
      rw [← hTu']
      exact GlobalTheory.T.galois_action_period_product K χ t s hs ht (res σ) (hres σ) fun μ x => hresv σ ⟨μ x, hμL μ x⟩)
    (fun σ hσ => (hN (res σ) (hres σ) hσ).trans (hcyc σ))
  subst hn
  intro μ
  exact _root_.GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count s t K.1.val (hs _) u (by rw [hTu', pow_one]) ((ht _).2.2 rfl) μ (hs μ)

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemFBOfNear
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem keyL : ∀ {l : ℕ} [Fact l.Prime] (b : Formalism.Per6.BdRp l) (k : ℕ),
    ∃ (c : ℕ) (a : Wl l), (l : Formalism.Per6.BdRp l) ^ c * b - wB l a ∈ FB l k := by
  intro l _ b k
  have hξ := GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[l] l
  set ξ := GroundTheory.PAdicHodge.IsPerfectoidField.kerThetaGenerator ℂ_[l] l with hξdef
  have hfg := GroundTheory.PAdicHodge.fg_ker_fontaineThetaInvertP hξ
  have hm : FB l k = Ideal.span {GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l ξ ^ k} := by
    rw [FB, ker_thB_eq, GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hξ,
      Ideal.span_singleton_pow]
  have h' : Ideal.span {GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l ξ ^ k} =
      (RingHom.ker (fontaineThetaInvertP _ l) ^ k).map
        (GroundTheory.PAdicHodge.toBDeRhamPlus _ l) := by
    rw [GroundTheory.PAdicHodge.ker_fontaineThetaInvertP hξ, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, map_pow]
    rfl
  obtain ⟨a0, ha0⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP _ l)) k b)
  have hz : b - GroundTheory.PAdicHodge.toBDeRhamPlus _ l a0 ∈ FB l k := by
    let I := RingHom.ker (fontaineThetaInvertP (↥(GroundTheory.PAdicHodge.normInteger ℂ_[l])) l)
    let b' : AdicCompletion I (Localization.Away (l : Wl l)) := b
    let c' : AdicCompletion I (Localization.Away (l : Wl l)) := algebraMap _ _ a0
    have e : (AdicCompletion.evalₐ I k) c' = Ideal.Quotient.mk _ a0 := by
      simp only [c']
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        AdicCompletion.evalₐ_of]
    have h1 : b' - c' ∈ RingHom.ker (AdicCompletion.evalₐ I k).toRingHom := by
      rw [RingHom.mem_ker]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.map_sub]
      rw [e, ha0, sub_self]
    rw [GroundTheory.PAdicHodge.ker_adicCompletion_evalₐ hfg k] at h1
    rw [hm, h']
    exact h1
  obtain ⟨⟨w, ⟨_, c, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers ((l : Wl l))) a0
  refine ⟨c, w, ?_⟩
  have e : (l : Formalism.Per6.BdRp l) ^ c * GroundTheory.PAdicHodge.toBDeRhamPlus _ l
      (IsLocalization.mk' _ w (⟨(l : Wl l) ^ c, c, rfl⟩ : Submonoid.powers (l : Wl l))) = wB l w := by
    have h2 := IsLocalization.mk'_spec (Localization.Away (l : Wl l)) w
      (⟨(l : Wl l) ^ c, c, rfl⟩ : Submonoid.powers (l : Wl l))
    have h3 := congrArg (GroundTheory.PAdicHodge.toBDeRhamPlus _ l) h2
    rw [map_mul] at h3
    have h4 : GroundTheory.PAdicHodge.toBDeRhamPlus _ l (algebraMap (Wl l) (Localization.Away (l : Wl l)) ((l : Wl l) ^ c)) =
        (l : Formalism.Per6.BdRp l) ^ c := by
      simp only [map_pow, map_natCast]
    simp only [] at h3
    rw [h4] at h3
    rw [mul_comm]
    exact h3
  rw [← e, ← mul_sub]
  exact Ideal.mul_mem_left _ _ hz

theorem normL : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)),
    ∀ s ∈ latS K', ‖thB l s‖ ≤ 1 := by
  intro l _ K' s hs
  have hle : latS K' ≤ (GroundTheory.PAdicHodge.normInteger ℂ_[l]).comap (thB l) := by
    refine (Subring.closure_le).2 ?_
    rintro z (⟨a, rfl⟩ | ⟨x, ⟨hx, hi⟩, rfl⟩)
    · change thB l (wB l a) ∈ GroundTheory.PAdicHodge.normInteger ℂ_[l]
      have e : thB l (wB l a) = _ :=
        GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus (K := ℂ_[l]) l a
      rw [e]
      exact Subtype.property _
    · change thB l (rB l x) ∈ GroundTheory.PAdicHodge.normInteger ℂ_[l]
      have e : thB l (rB l x) = ((x : Om l) : ℂ_[l]) := GroundTheory.PAdicHodge.thetaAlgHom_algClToBdR l x
      rw [e, GroundTheory.PAdicHodge.mem_normInteger, PadicComplex.norm_extends,
        ← GlobalTheory.isIntegral_padicInt_iff_norm_le_one]
      exact hi
  exact GroundTheory.PAdicHodge.mem_normInteger.1 (hle hs)

theorem galL : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [Normal ℚ_[l] K']
    (g : GQ l), ∀ s ∈ latS K', actB g s ∈ latS K' := by
  intro l _ K' hn g s hs
  have hle : latS K' ≤ (latS K').comap (actB g) := by
    refine (Subring.closure_le).2 ?_
    rintro z (⟨a, rfl⟩ | ⟨x, ⟨hx, hi⟩, rfl⟩)
    · change actB g (wB l a) ∈ latS K'
      have e : actB g (wB l a) = wB l (Formalism.Per6.toBot g • a) :=
        GroundTheory.PAdicHodge.gal_smul_wittToBDeRhamPlus (Formalism.Per6.toBot g) a
      rw [e]
      exact wB_mem_latS K' _
    · change actB g (rB l x) ∈ latS K'
      have e : actB g (rB l x) = rB l (g x) :=
        GroundTheory.PAdicHodge.gal_smul_algClToBdR (Formalism.Per6.toBot g) x
      rw [e]
      refine rB_mem_latS K' ?_ (hi.map ((g : Om l →ₐ[ℚ_[l]] Om l).restrictScalars ℤ_[l]))
      exact (IntermediateField.normal_iff_forall_map_le.1 hn) (g : Om l →ₐ[ℚ_[l]] Om l) ⟨x, hx, rfl⟩
  exact hle hs

theorem xpowL : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) (x : Om l),
    x ∈ K' → ‖((x : Om l) : ℂ_[l])‖ < 1 →
    ∃ (N : ℕ) (y : Om l), 0 < N ∧ y ∈ K' ∧ IsIntegral ℤ_[l] y ∧ x ^ N = (l : Om l) * y := by
  intro l _ K' x hx h1
  rw [PadicComplex.norm_extends] at h1
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlp : 0 < ‖(l : Om l)‖ := norm_pos_iff.2 hl0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hlp h1
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · exfalso
      have hle : ‖(l : Om l)‖ ≤ 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
        exact Padic.norm_p_lt_one.le
      rw [pow_zero] at hN
      exact absurd hN (not_lt.2 hle)
    · exact h
  refine ⟨N, x ^ N / (l : Om l), hNpos, ?_, ?_, ?_⟩
  · refine div_mem (pow_mem hx N) ?_
    exact natCast_mem K' l
  · rw [GlobalTheory.isIntegral_padicInt_iff_norm_le_one, norm_div, norm_pow]
    exact (div_le_one hlp).2 hN.le
  · field_simp

end GlobalTheory.CompanionTheory.LTPer

namespace GlobalTheory.CompanionTheory.LTPer

theorem mem_FB_of_near {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (T : Finset (Formalism.Per6.BdRp l))
    (hS : ∀ s ∈ S, ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t)) (k : ℕ)
    (x : Formalism.Per6.BdRp l) (h : ∀ m : ℕ, ∃ s ∈ S, x - (l : Formalism.Per6.BdRp l) ^ m * s ∈ FB l k) :
    x ∈ FB l k := by
  choose cf af hcf using fun t : Formalism.Per6.BdRp l => keyL t k
  set c := T.sup cf with hc
  have hT : ∀ t ∈ T, (l : Formalism.Per6.BdRp l) ^ c * t -
      wB l ((l : Wl l) ^ (c - cf t) * af t) ∈ FB l k := by
    intro t ht
    have hle : cf t ≤ c := Finset.le_sup ht
    have e : (l : Formalism.Per6.BdRp l) ^ c * t - wB l ((l : Wl l) ^ (c - cf t) * af t) =
        (l : Formalism.Per6.BdRp l) ^ (c - cf t) * ((l : Formalism.Per6.BdRp l) ^ cf t * t - wB l (af t)) := by
      rw [map_mul, map_pow, map_natCast, mul_sub, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [e]
    exact Ideal.mul_mem_left _ _ (hcf t)
  have hSa : ∀ s ∈ S, ∃ a : Wl l, (l : Formalism.Per6.BdRp l) ^ c * s - wB l a ∈ FB l k := by
    intro s hs
    obtain ⟨a, rfl⟩ := hS s hs
    refine ⟨∑ t ∈ T, (l : Wl l) ^ (c - cf t) * af t * a t, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun t ht => ?_
    have e : (l : Formalism.Per6.BdRp l) ^ c * (t * wB l (a t)) -
        wB l ((l : Wl l) ^ (c - cf t) * af t * a t) =
        ((l : Formalism.Per6.BdRp l) ^ c * t - wB l ((l : Wl l) ^ (c - cf t) * af t)) * wB l (a t) := by
      rw [map_mul (wB l) _ (a t)]; ring
    rw [e]
    exact Ideal.mul_mem_right _ _ (hT t ht)
  have hm : FB l k = IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) ^ k := by rw [FB, ker_thB_eq]
  rw [hm]
  refine GroundTheory.PAdicHodge.IsPerfectoidField.mem_maximalIdeal_pow_of_forall_sub_mem (K := ℂ_[l]) (p := l)
    fun M => ?_
  obtain ⟨s, hs, hx⟩ := h (M + c)
  obtain ⟨a, ha⟩ := hSa s hs
  refine ⟨a, ?_⟩
  rw [← hm]
  have e : x - (l : Formalism.Per6.BdRp l) ^ M * GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l a =
      (x - (l : Formalism.Per6.BdRp l) ^ (M + c) * s) +
        (l : Formalism.Per6.BdRp l) ^ M * ((l : Formalism.Per6.BdRp l) ^ c * s - wB l a) := by
    rw [pow_add, wB]; ring
  rw [e]
  exact add_mem hx (Ideal.mul_mem_left _ _ ha)

theorem FB_sep {l : ℕ} [Fact l.Prime] (x : Formalism.Per6.BdRp l) (h : ∀ k, x ∈ FB l k) : x = 0 := by
  refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l)) inferInstance x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← ker_thB_eq]
  exact h n

theorem FB_complete {l : ℕ} [Fact l.Prime] (x : ℕ → Formalism.Per6.BdRp l)
    (h : ∀ k, x (k + 1) - x k ∈ FB l k) : ∃ t, ∀ k, t - x k ∈ FB l k := by
  have hc : IsPrecomplete (IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l)) (Formalism.Per6.BdRp l) := inferInstance
  have hstep : ∀ m n, m ≤ n → x n - x m ∈ FB l m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : x (n + 1) - x n ∈ FB l m := Ideal.pow_le_pow_right hmn (h n)
      have := add_mem h1 ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨t, ht⟩ := hc.prec (f := x) (fun {m n} hmn => by
    rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← ker_thB_eq]
    exact hstep m n hmn)
  refine ⟨t, fun k => ?_⟩
  have := ht k
  rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← ker_thB_eq] at this
  exact this

theorem lattice_main : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] K'] [Normal ℚ_[l] K'],
    ∃ S : Subring (Formalism.Per6.BdRp l), (∀ a, wB l a ∈ S) ∧
      (∀ x ∈ K', IsIntegral ℤ_[l] x → rB l x ∈ S) ∧
      (∀ (g : GQ l), ∀ s ∈ S, actB g s ∈ S) ∧ (∀ s ∈ S, ‖thB l s‖ ≤ 1) ∧
      ∀ x ∈ K', IsIntegral ℤ_[l] x → x ≠ 0 → ‖((x : Om l) : ℂ_[l])‖ < 1 →
        PerEnv S (FB l) (rB l x) ∧ ∀ u : Tl l, u ≠ 0 → ∀ s ∈ S, tch l u ≠ rB l x * s := by
  intro l _ K' _ _
  refine ⟨latS K', wB_mem_latS K', fun x hx hi => rB_mem_latS K' hx hi, galL K', normL K', ?_⟩
  intro x hxK hxi hx0 hx1
  obtain ⟨T, hT, hS⟩ := latS_finite_span K'
  obtain ⟨N, y, hN, hyK, hyi, hxy⟩ := xpowL K' x hxK hx1
  have hϖ : rB l x ∈ latS K' := rB_mem_latS K' hxK hxi
  have hy : rB l y ∈ latS K' := rB_mem_latS K' hyK hyi
  have hϖy : rB l x ^ N = (l : Formalism.Per6.BdRp l) * rB l y := by
    rw [← map_pow, hxy, map_mul, map_natCast]
  have hnear : ∀ k x', (∀ m : ℕ, ∃ s ∈ latS K', x' - (l : Formalism.Per6.BdRp l) ^ m * s ∈ FB l k) → x' ∈ FB l k :=
    fun k x' h => mem_FB_of_near (latS K') T hS k x' h
  have hsep : ∀ x' : Formalism.Per6.BdRp l, (∀ m : ℕ, ∃ s ∈ latS K', x' = (l : Formalism.Per6.BdRp l) ^ m * s) → x' = 0 := by
    intro x' h
    refine FB_sep x' fun k => hnear k x' fun m => ?_
    obtain ⟨s, hs, e⟩ := h m
    exact ⟨s, hs, by rw [← e, sub_self]; exact zero_mem _⟩
  refine ⟨⟨by simp [FB], fun k => Ideal.pow_le_pow_right (Nat.le_succ k),
    fun a b => by rw [FB, FB, FB, pow_add], FB_sep, FB_complete,
    (IsUnit.map (rB l) (isUnit_iff_ne_zero.2 hx0)), hϖ, ?_, ?_⟩,
    tch_ne_mul_of_pow_eq (latS K') T (wB_mem_latS K') hT hS (rB l x) (rB l y) N hy hϖy⟩
  · exact PowerSeriesSum.sum_with_tails (wB l) l (latS K') T (wB_mem_latS K') hT hS hsep (rB l x) (rB l y) N hN hϖ hy hϖy
  · intro k x' _ h
    refine hnear k x' fun m => ?_
    obtain ⟨s, hs, e⟩ := h (N * m)
    refine ⟨rB l y ^ m * s, mul_mem (pow_mem hy m) hs, ?_⟩
    have e2 : rB l x ^ (N * m) * s = (l : Formalism.Per6.BdRp l) ^ m * (rB l y ^ m * s) := by
      rw [pow_mul, hϖy, mul_pow, mul_assoc]
    rwa [e2] at e

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonemptyOpenIdealNotNilpotentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_open_ideal_not_nilpotent : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (W : J.subscheme.Opens), (W : Set J.subscheme).Nonempty → ∃ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V → J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W) ∧ ∀ m, ¬ powIdeal J₀ m ≤ J := by
  first | exact @GlobalTheory.CompanionTheory.GE.NonIso.exists_ideal_not_pow_le | exact GlobalTheory.CompanionTheory.GE.NonIso.exists_ideal_not_pow_le | (intros; apply GlobalTheory.CompanionTheory.GE.NonIso.exists_ideal_not_pow_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenRestrictionFunctionsCompatibleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_restriction_functions_compatible : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; ∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a) := by
  first | exact @GlobalTheory.CompanionTheory.GE.RingCompat.toFunctions_preimage | exact GlobalTheory.CompanionTheory.GE.RingCompat.toFunctions_preimage | (intros; apply GlobalTheory.CompanionTheory.GE.RingCompat.toFunctions_preimage <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeCriterionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_prime_criterion : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ q : Ideal Γ(Z, U), q.IsPrime → f ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) → (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ ∃ v : Γ(Z, U), v ∉ q ∧ v * (algebraMap Γ(X, V) Γ(Z, U) t * c) = v * algebraMap Γ(X, V) Γ(Z, U) b) ∧ (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * algebraMap Γ(X, V) Γ(Z, U) b = 0) → ∃ t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus | exact GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus | (intros; apply GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus <;> assumption)
end

