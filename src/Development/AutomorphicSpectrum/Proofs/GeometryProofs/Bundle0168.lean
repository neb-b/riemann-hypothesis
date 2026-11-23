module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFgIsSeparated
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LocallyQuasiFiniteSpMap
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpaceOfDivisible
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem eq_one_of_divisible {P Q : Type*} [CommGroup P] [Finite Q] (c : P → Q)
    (hc : ∀ a b t : P, c a = c b → c (a * t) = c (b * t))
    (hd : ∀ n : ℕ, n ≠ 0 → ∀ x : P, ∃ y : P, y ^ n = x) (x : P) : c x = c 1 := by
  let H : Subgroup P :=
    { carrier := {a | c a = c 1}
      one_mem' := rfl
      mul_mem' := fun {a b} ha hb => by
        have := hc a 1 b ha
        rw [_root_.one_mul] at this
        exact this.trans hb
      inv_mem' := fun {a} ha => by
        have := hc a 1 a⁻¹ ha
        rw [_root_.mul_inv_cancel, _root_.one_mul] at this
        exact this.symm }
  have hinj : Function.Injective (fun q : P ⧸ H => c q.out) := by
    intro q r hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r, QuotientGroup.eq]
    have := hc _ _ (q.out)⁻¹ hqr
    simp only [mul_inv_cancel] at this
    change c _ = c 1
    rw [mul_comm, this.symm]
  have : Finite (P ⧸ H) := Finite.of_injective _ hinj
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨y, rfl⟩ := hd _ hi x
  exact Subgroup.pow_index_mem H y

theorem connectedSpace_of_divisible : ∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → ∀ x : 𝟙_ (Over (Sp K)) ⟶ G, ∃ y : 𝟙_ (Over (Sp K)) ⟶ G, y ^ n = x) → ConnectedSpace G.left := by
  intro K _ _ G _ _ hl hq hd
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  let pt : (𝟙_ (Over (Sp K))).left := IsLocalRing.closedPoint K
  let F : (𝟙_ (Over (Sp K)) ⟶ G) → G.left := fun x => x.left pt
  have hopen : ∀ x : G.left, IsOpen (connectedComponent x) :=
    fun x => isOpen_connectedComponent_of_noetherianSpace x
  have : DiscreteTopology (_root_.ConnectedComponents G.left) :=
    ConnectedComponents.discreteTopology_iff.2 hopen
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  let c : (𝟙_ (Over (Sp K)) ⟶ G) → _root_.ConnectedComponents G.left := fun x => F x
  have htr : ∀ a t : 𝟙_ (Over (Sp K)) ⟶ G,
      F (a * t) = (GrpObj.mulRight t).hom.left (F a) := by
    intro a t
    have h : a ≫ (GrpObj.mulRight t).hom = a * t := by
      simp [comp_lift_assoc, Hom.mul_def]
    simp only [F, ← h, Over.comp_left, Scheme.Hom.comp_apply]
  have hc : ∀ a b t, c a = c b → c (a * t) = c (b * t) := by
    intro a b t hab
    have := congrArg (Continuous.connectedComponentsMap (GrpObj.mulRight t).hom.left.continuous) hab
    simpa [c, htr] using this
  have hall := eq_one_of_divisible c hc hd
  have hsurj : ∀ x : G.left, IsClosed {x} → ∃ a, F a = x := by
    intro x hx
    refine ⟨Over.homMk (pointOfClosedPoint G.hom x hx) (pointOfClosedPoint_comp G.hom x hx), ?_⟩
    exact pointOfClosedPoint_apply G.hom x hx _
  have huniv : connectedComponent (F 1) = Set.univ := by
    by_contra hne
    obtain ⟨x, hx, hcl⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.2 hne)
      (IsOpen.isLocallyClosed isClosed_connectedComponent.isOpen_compl)
    obtain ⟨a, rfl⟩ := hsurj x hcl
    apply hx
    have h1 : connectedComponent (F a) = connectedComponent (F 1) :=
      ConnectedComponents.coe_eq_coe.1 (hall a)
    rw [← h1]
    exact mem_connectedComponent
  exact connectedSpace_iff_connectedComponent.2 ⟨F 1, huniv⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedSpaceOfIsFieldGlobalFunctions
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem connectedSpace_of_isField_globalFunctions (Z : Scheme.{0}) (h : IsField Γ(Z, ⊤)) :
    ConnectedSpace Z := by
  have hne : Nonempty Z := by
    by_contra hZ
    have hb : (⊤ : Z.Opens) = ⊥ := by
      ext x
      exact (hZ ⟨x⟩).elim
    have hs : Subsingleton Γ(Z, ⊤) := by
      rw [hb]
      infer_instance
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  have hp : PreconnectedSpace Z := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    obtain ⟨e, he, hUe⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z U hU
    by_cases h0 : e = 0
    · left
      rw [← hUe, h0, Z.basicOpen_zero]
      rfl
    · right
      obtain ⟨b, hb⟩ := h.mul_inv_cancel h0
      have h1 : e = 1 := by
        calc e = e * e * b := by rw [_root_.mul_assoc, hb, _root_.mul_one]
          _ = e * b := by rw [he]
          _ = 1 := hb
      rw [← hUe, h1, Z.basicOpen_of_isUnit isUnit_one]
      rfl
  exact { toPreconnectedSpace := hp, toNonempty := hne }

theorem geometricallyConnected_of_isIso_appTop :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), QuasiCompact p → QuasiSeparated p →
      IsIso p.appTop → GeometricallyConnected p := by
  intro K _ X p _ _ _
  refine ⟨fun L _ y Z a q H => ?_⟩
  have hy : Flat y := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    rw [Flat.SpecMap_iff]
    algebraize [φ.hom]
    exact inferInstanceAs (Module.Flat K L)
  have hq : IsIso q.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  let e₁ : Γ(Spec (.of L), ⊤) ≃+* Γ(Z, ⊤) := (asIso q.appTop).commRingCatIsoToRingEquiv
  let e₂ : Γ(Spec (.of L), ⊤) ≃+* L := (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
  have hL : IsField Γ(Spec (.of L), ⊤) := MulEquiv.isField (Field.toIsField L) e₂.toMulEquiv
  exact connectedSpace_of_isField_globalFunctions Z (MulEquiv.isField hL e₁.symm.toMulEquiv)

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstructibleStableOpen
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isClosed_of_stable_of_noetherian {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] (V : Set X)
    (hg : StableUnderGeneralization V) (hs : StableUnderSpecialization V) : IsClosed V := by
  have key : ∀ x ∈ V, irreducibleComponent x ⊆ V := by
    intro x hx y hy
    have hS : IsGenericPoint (isIrreducible_irreducibleComponent (x := x)).genericPoint
        (irreducibleComponent x) :=
      (isIrreducible_irreducibleComponent (x := x)).isGenericPoint_genericPoint
        isClosed_irreducibleComponent
    exact hs (hS.specializes hy) (hg (hS.specializes mem_irreducibleComponent) hx)
  have hV : V = ⋃₀ {C | C ∈ irreducibleComponents X ∧ C ⊆ V} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x, key x hx⟩, mem_irreducibleComponent⟩
    · exact Set.sUnion_subset fun C hC => hC.2
  rw [hV, Set.sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (by exact fun C hC => hC.1))
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

theorem isOpen_of_stable (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k))
    (hg : StableUnderGeneralization U) (hs : StableUnderSpecialization U) : IsOpen U := by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stable_of_noetherian Uᶜ
    (stableUnderGeneralization_compl_iff.mpr hs) (stableUnderSpecialization_compl_iff.mpr hg)

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LabPt

theorem valAt_of_const {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) {R : Type} [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of R) ⟶ X) (ρ : O →+* R) (hz : z ≫ s = Spec.map (CommRingCat.ofHom ρ))
    (h : genPt ξ ⤳ centre z) (o : O) : ValAt ξ z (algebraMap O Ω o) (ρ o) := by
  refine ⟨h, (X.presheaf.germ ⊤ (centre z) trivial).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)),
    Flat.ConstReg.genMap_germ_const ξ s hs ⟨centre z, h⟩ o, ?_⟩
  have h1 : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  have h1' := congrArg (fun q => q.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  refine h1'.trans ?_
  have h2 : z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hz]; simp only [Scheme.Hom.comp_appTop]; rfl
  have h3 := congrArg (fun q => q.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ o) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = ρ o
  rw [h2, ← h3']
  simp

theorem valAt_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) {a : Ω} {r r' : R} (h₁ : ValAt ξ z a r) (h₂ : ValAt ξ z a r') : r = r' := by
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨_, e₁⟩ := (hφ a r).1 h₁
  obtain ⟨_, e₂⟩ := (hφ a r').1 h₂
  exact e₁.symm.trans e₂

theorem injective_of_charZero {A : Type} [CommRing A] [IsDomain A] [Algebra.IsIntegral ℤ A] {L : Type} [Field L]
    [CharZero L] (t : A →+* L) : Function.Injective t := by
  have hk : RingHom.ker t = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp [Ideal.mem_comap, RingHom.mem_ker]
  exact (RingHom.injective_iff_ker_eq_bot t).2 hk

theorem card_hom_le (E : Type) [Field E] [NumberField E] (L : Type) [Field L] [CharZero L] :
    Finite (𝓞 E →+* L) ∧ Nat.card (𝓞 E →+* L) ≤ Module.finrank ℚ E := by
  let f : (𝓞 E →+* L) → (E →ₐ[ℚ] AlgebraicClosure L) := fun t =>
    ((algebraMap L (AlgebraicClosure L)).comp
      (IsFractionRing.lift (K := E) (injective_of_charZero t))).toRatAlgHom
  have hf : Function.Injective f := by
    intro t t' h
    refine RingHom.ext fun a => (algebraMap L (AlgebraicClosure L)).injective ?_
    have := DFunLike.congr_fun h (algebraMap (𝓞 E) E a)
    simpa [f] using this
  have hc : Nat.card (E →ₐ[ℚ] AlgebraicClosure L) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card, AlgHom.card]
  haveI : Finite (𝓞 E →+* L) := Finite.of_injective f hf
  exact ⟨inferInstance, (Nat.card_le_card_of_injective f hf).trans hc.le⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bijective_of_injective (H : Host E) {L : Type} [Field L] [CharZero L]
    (f : CMType H ⊕ CMType H → (𝓞 E →+* L)) (hf : Function.Injective f) : Function.Bijective f := by
  obtain ⟨hfin, hle⟩ := card_hom_le E L
  refine hf.bijective_of_nat_card_le (hle.trans ?_)
  rw [Nat.card_eq_of_bijective _ (LabelCount.labelCx_bijective H), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

theorem isCMFam_of_bijective {A : Type} [Fintype A] (f g : A → (𝓞 E →+* ℂ))
    (hb : Function.Bijective (Sum.elim f g)) (hc : ∀ τ, g τ = (starRingEnd ℂ).comp (f τ)) :
    IsCMFam f ∧ IsCMFam g := by
  have cc : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s :=
    fun s => RingHom.ext fun a => by simp
  have hf : Function.Injective f := fun a b h =>
    Sum.inl_injective (hb.1 (a₁ := .inl a) (a₂ := .inl b) h)
  have hg : Function.Injective g := fun a b h =>
    Sum.inr_injective (hb.1 (a₁ := .inr a) (a₂ := .inr b) h)
  have hd : ∀ a b, f a ≠ g b := fun a b h => by
    have := hb.1 (a₁ := .inl a) (a₂ := .inr b) h
    simp at this
  refine ⟨⟨hf, fun s => ⟨?_, fun hn => ?_⟩⟩, ⟨hg, fun s => ⟨?_, fun hn => ?_⟩⟩⟩
  · rintro ⟨τ, rfl⟩ ⟨τ', h⟩
    exact hd τ' τ (h.trans (hc τ).symm)
  · obtain ⟨x, hx⟩ := hb.2 s
    rcases x with τ | τ
    · exact ⟨τ, hx⟩
    · have hx' : g τ = s := hx
      exact absurd ⟨τ, by rw [← hx', hc, cc]⟩ hn
  · rintro ⟨τ, rfl⟩ ⟨τ', h⟩
    refine hd τ τ' (Eq.symm (h.trans ?_))
    rw [hc, cc]
  · obtain ⟨x, hx⟩ := hb.2 s
    rcases x with τ | τ
    · have hx' : f τ = s := hx
      exact absurd ⟨τ, by rw [← hx', hc]⟩ hn
    · exact ⟨τ, hx⟩

theorem exists_labVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ 𝔐.X), ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* L), 𝔐.LabVal z id σ ∧ (∀ σ', 𝔐.LabVal z id σ' → σ' = σ) ∧ Function.Bijective σ ∧ (∀ s, Function.Injective (σ s)) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E ∧ ∀ e : L →+* ℂ, IsCMFam (fun τ => e.comp (σ (.inl τ))) ∧ IsCMFam (fun τ => e.comp (σ (.inr τ))) ∧ ∀ τ, e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* L, spMap ρ = z ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  let κ : c.F →+* L := IsFractionRing.lift (injective_of_charZero ρ)
  have hκ : ∀ o, κ (algebraMap (𝓞 c.F) c.F o) = ρ o := fun o => IsFractionRing.lift_algebraMap _ o
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hsp : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hval : ∀ (s : CMType H ⊕ CMType H) (a : 𝓞 E), ValAt 𝔐.ξ z (𝔐.emb s a) (κ (labelEmb c s a)) := by
    intro s a
    have hint : IsIntegral ℤ (labelEmb c s a) :=
      (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
    have hm : algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = labelEmb c s a :=
      IsIntegralClosure.algebraMap_mk' _ _ hint
    have h := valAt_of_const 𝔐.ξ (𝔐.f ≫ Y.s) 𝔐.cst_over z ρ hρ.symm hsp (IsIntegralClosure.mk' (𝓞 c.F) _ hint)
    have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb s a := by
      show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
      rw [hm]
    rw [he, ← hκ, hm] at h
    exact h
  let σ : CMType H ⊕ CMType H → (𝓞 E →+* L) := fun s => κ.comp (labelEmb c s)
  have hinj : ∀ {L' : Type} [Field L'] (κ' : c.F →+* L'),
      Function.Injective fun s : CMType H ⊕ CMType H => κ'.comp (labelEmb c s) := fun κ' s t h =>
    LabelCount.labelEmb_injective c (RingHom.ext fun a => κ'.injective (RingHom.congr_fun h a))
  have hconj : ∀ (e : L →+* ℂ) (τ : CMType H),
      e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
    intro e τ
    refine RingHom.ext fun a => ?_
    let ψ : E →+* ℂ := (e.comp κ).comp (τ.1.codRestrict c.F (c.conj τ.1))
    show ψ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (ψ (a : E))
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  refine ⟨σ, hval, fun σ' h' => ?_, bijective_of_injective H σ (hinj κ), fun s => injective_of_charZero _, ?_,
    fun e => ?_⟩
  · funext s
    refine RingHom.ext fun a => ?_
    exact valAt_unique 𝔐.ξ 𝔐.tie.gen z hsp (h' s a) (hval s a)
  · have h := (LabelCount.labels_injective_card E H l c c.F (RingHom.id _)).2
    rw [Fintype.card_sum] at h
    omega
  · have hb : Function.Bijective (fun s => e.comp (σ s)) :=
      bijective_of_injective H _ (hinj (e.comp κ))
    have hb' : Function.Bijective (Sum.elim (fun τ => e.comp (σ (.inl τ))) fun τ => e.comp (σ (.inr τ))) := by
      convert hb using 1
      funext s
      rcases s with τ | τ <;> rfl
    obtain ⟨h1, h2⟩ := isCMFam_of_bijective _ _ hb' (hconj e)
    exact ⟨h1, h2, hconj e⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.LabPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFgIsClosedPreimageRange
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.Approx


open GlobalTheory.Spread GlobalTheory.SpreadSep in
theorem exists_fg_isClosed_preimage_range (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V]
    [Algebra k V] (X P : Scheme.{0}) (j : X ⟶ P) (q : P ⟶ Sp k) (hj : IsImmersion j)
    (h₁ : LocallyOfFiniteType q) (h₂ : QuasiCompact q)
    (h : IsClosed (pullback.fst q (spMap (algebraMap k V)) ⁻¹' Set.range j)) :
    ∃ R : Subalgebra k V, R.FG ∧
      IsClosed (pullback.fst q (spMap (algebraMap k R)) ⁻¹' Set.range j) := by
  classical
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace ↥P := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian P := {}
  have : QuasiSeparated q := (quasiSeparated_iff_quasiSeparatedSpace q).mpr inferInstance
  obtain ⟨U, Z, hU, hZ, eΔ⟩ := j.isLocallyClosed_range
  let s : (Finset V)ᵒᵖ := .op ∅
  let π : (bcDiagram q V).obj s ⟶ P := pullback.fst q _
  have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst q _))
  let O : P.Opens := ⟨U, hU⟩
  let O' : P.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have key : ((π ⁻¹ᵁ O : Set _) \ (π ⁻¹ᵁ O' : Set _)) = π ⁻¹' Set.range j := by
    rw [eΔ]
    ext x
    change π x ∈ U ∧ ¬ π x ∉ Z ↔ π x ∈ U ∧ π x ∈ Z
    rw [not_not]
  obtain ⟨i, f, hi⟩ := exists_isClosed_preimage_diff (bcDiagram q V) (bcCone q V) (isLimitBcCone q V)
    (π ⁻¹ᵁ O) (π ⁻¹ᵁ O')
    (QuasiCompact.isCompact_preimage (f := π) _ O.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (QuasiCompact.isCompact_preimage (f := π) _ O'.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (by
      have e : (bcCone q V).π.app s ≫ π = pullback.fst q _ := bcMap_fst _ _
      rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e]
      exact h)
  refine ⟨Algebra.adjoin k (i.unop : Set V), Subalgebra.fg_adjoin_finset _, ?_⟩
  have e : (bcDiagram q V).map f ≫ π = pullback.fst q _ := bcMap_fst _ _
  rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e] at hi
  exact hi

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreUniformisedFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isGeom_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → Z.IsGeom := by
  exact @PositivityTheory.Xgn.geometric_of_periods

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSqBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem lieNormSq_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (ω : R) (ω' : R') (C : Ell H R ω) (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (σ : R' →+* ℂ) (r : ℝ), EllMap C' C f φ → (IsLieNormSq C.P C.v (σ.comp f) r ↔ IsLieNormSq C'.P C'.v σ r) := by
  intro E _ _ _ H R R' _ _ ω ω' C C' f φ σ r h
  exact (GlobalTheory.CM.EllComp.isLieNormSq_iff h.2.1 h.2.2.1 σ r).symm

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PderivZeroOfJetPthPowerDiffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pderiv_zero_of_jet_pth_power_diff : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d : ℕ) (F f : MvPowerSeries (Fin 1 × Fin d) k), (∀ q, MvPowerSeries.pderiv (R := k) q f = 0) → (∀ m, ∃ v : Jet k (Fin 1 × Fin d) m, psJet m F = v ^ p - psJet m f) → ∀ q, MvPowerSeries.pderiv (R := k) q F = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.pderiv_eq_zero_of_jet_pow_sub | exact GlobalTheory.CompanionTheory.Ar.Coc.pderiv_eq_zero_of_jet_pow_sub | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.pderiv_eq_zero_of_jet_pow_sub <;> assumption)
end

