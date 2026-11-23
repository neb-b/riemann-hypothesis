module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.CorrOpEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.FrEx
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.frEx :
    FrEx := by
  intro p f hp κ kb _ _ _ hκ X t h τ hτ
  have K : absFrob (geom kb t) p f hp h ≫ pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (τ : kb →+* kb)) := by
    by_cases hk : (p : kb) = 0
    · have hk' : (p : Γ(Spec (CommRingCat.of kb), ⊤)) = 0 := by
        rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom p]
        erw [hk]
        exact map_zero _
      rw [GlobalTheory.SS.FrobField.absFrob_nat _ p f hp h hk']
      congr 1
      exact GlobalTheory.SS.FrobField.absFrob_spec kb p f hp hk' (τ : kb →+* kb) hτ
    · haveI : IsEmpty (geom kb t) := by
        refine ⟨fun x => hk ?_⟩
        have hinj := (((geom kb t).presheaf.germ ⊤ x trivial).hom.comp
          ((pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))).appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom)).injective
        apply hinj
        rw [map_zero]
        simp only [RingHom.comp_apply]
        rw [map_natCast, map_natCast, h, map_zero]
      exact isInitialOfIsEmpty.hom_ext _ _
  have hc : (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) ≫ t =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (algebraMap κ kb)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, K, Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    simp
  refine ⟨pullback.lift (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
    (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) hc, pullback.lift_snd _ _ _, ?_, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, galMap_fst, pullback.lift_fst]
    · rw [Category.assoc, galMap_snd, ← Category.assoc, pullback.lift_snd, K]
  · intro Ω _ φ hφ x
    have hΩ := GlobalTheory.SS.FrobField.cast_zero_of_hom x h
    have e := GlobalTheory.SS.FrobField.absFrob_nat x p f hp hΩ h
    have e2 : absFrob (gp Ω) p f hp hΩ = Mod.sp φ := GlobalTheory.SS.FrobField.absFrob_spec Ω p f hp hΩ φ hφ
    rw [pullback.lift_fst, ← Category.assoc, ← e, e2, Category.assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PBaseFacts
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem nml_spec (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    (y : Spec (CommRingCat.of O)) :
    IsDomain ((Spec (CommRingCat.of O)).presheaf.stalk y) ∧
      IsIntegrallyClosed ((Spec (CommRingCat.of O)).presheaf.stalk y) := by
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  letI : Algebra O ((Spec (CommRingCat.of O)).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of O) y
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of O)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of O) y
  exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain y.asIdeal _

private theorem natCast_eq_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O)) (p : ℕ) :
    (p : Γ(Y, ⊤)) = fn g (p : O) := by
  simp [fn]

private theorem mem_basicOpen_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O)) (a : O)
    (y : Y) : y ∈ Y.basicOpen (fn g a) ↔ g y ∈ PrimeSpectrum.basicOpen a := by
  rw [fn, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

private theorem exists_generic {O : Type} [CommRing O] [IsDomain O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O))
    [Flat g] (a : O) (ha : a ≠ 0) (y : Y) : ∃ η ∈ Y.basicOpen (fn g a), η ⤳ y := by
  let s : Spec (CommRingCat.of O) := ⟨⊥, Ideal.isPrime_bot⟩
  have hs : s ⤳ g y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨η, hη, rfl'⟩ := (Flat.generalizingMap g) hs
  refine ⟨η, ?_, hη⟩
  rw [mem_basicOpen_fn, rfl']
  exact ha

theorem UpperTheory.Gal.Mod.baseFacts :
    BaseFacts := by
  intro p O _ _ _ ϖ hϖ hp0 hpu Y g _
  haveI : Flat g := inferInstance
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hbo : Y.basicOpen (p : Γ(Y, ⊤)) = Y.basicOpen (fn g (p : O)) := by
    rw [natCast_eq_fn g p]
  have hϖp : ϖ ∣ (p : O) := by
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
    cases n with
    | zero => exact absurd (hn.isUnit_iff.mpr (by simp)) hpu
    | succ n => exact (dvd_pow_self ϖ (Nat.succ_ne_zero n)).trans hn.symm.dvd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact TranscendenceTraces.nmlLoc_holds Y
      (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g (nml_spec O)) (Or.inr inferInstance)
  · intro y hy
    obtain ⟨η, hη, hηy⟩ := exists_generic g (p : O) hp0 y
    rw [hbo, ← hy η hηy]
    exact hη
  · intro y
    obtain ⟨η, hη, hηy⟩ := exists_generic g (p : O) hp0 y
    exact ⟨η, hbo ▸ hη, hηy⟩
  · intro y hy
    rw [hbo, mem_basicOpen_fn] at hy
    rw [mem_basicOpen_fn]
    change (p : O) ∉ (g y).asIdeal at hy
    change ϖ ∉ (g y).asIdeal
    intro h
    obtain ⟨c, hc⟩ := hϖp
    exact hy (hc ▸ Ideal.mul_mem_right c _ h)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PClopenAt
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma clopen_basicOpen {X : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClopen (X.basicOpen e : Set X) := by
  have hsum : X.basicOpen e ⊔ X.basicOpen (1 - e) = ⊤ := by
    apply le_antisymm le_top
    have h := X.basicOpen_add_le e (1 - e)
    rwa [add_sub_cancel, Scheme.basicOpen_one] at h
  have hprod : X.basicOpen e ⊓ X.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, mul_sub, mul_one, he.eq, sub_self, Scheme.basicOpen_zero]
  have hc : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro hx hx'
      have hin : x ∈ X.basicOpen e ⊓ X.basicOpen (1 - e) := TopologicalSpace.Opens.mem_inf.mpr ⟨hx, hx'⟩
      rw [hprod] at hin
      simpa using hin
    · intro hx
      have hin : x ∈ X.basicOpen e ⊔ X.basicOpen (1 - e) := by
        rw [hsum]
        trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hin with h | h
      · exact h
      · exact absurd h hx
  refine ⟨?_, (X.basicOpen e).isOpen⟩
  rw [hc]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

private noncomputable def rho {κ : Type} [Field κ] {W : Scheme.{0}} (z : gp κ ⟶ W) : Γ(W, ⊤) →+* κ :=
  (z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom

private lemma mem_basicOpen_iff {κ : Type} [Field κ] {W : Scheme.{0}} (z : gp κ ⟶ W) (e : Γ(W, ⊤)) :
    pt z ∈ W.basicOpen e ↔ rho z e ≠ 0 := by
  have h1 : pt z ∈ W.basicOpen e ↔ IsLocalRing.closedPoint κ ∈ (gp κ).basicOpen (z.appTop e) := by
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  rw [h1, basicOpen_eq_of_affine']
  refine (PrimeSpectrum.mem_basicOpen _ _).trans ?_
  change _ ∉ IsLocalRing.maximalIdeal κ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]
  rfl

private lemma rho_inj {κ : Type} [Field κ] {W : Scheme.{0}} [IsAffine W] {z z' : gp κ ⟶ W}
    (h : rho z = rho z') : z = z' := by
  apply ext_of_isAffine
  have : z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom = z'.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom :=
    CommRingCat.hom_ext h
  exact (cancel_mono _).mp this

private lemma rho_comp (V : Type) [CommRing V] [IsLocalRing V] {W : Scheme.{0}}
    (g : W ⟶ Spec (CommRingCat.of V)) (z : gp (IsLocalRing.ResidueField V) ⟶ W) (hz : z ≫ g = resPt V) :
    (rho z).comp ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ g.appTop).hom = IsLocalRing.residue V := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ (z ≫ g).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField V))).hom =
      CommRingCat.ofHom (IsLocalRing.residue V) := by
    rw [hz, resPt, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have h2 := congrArg CommRingCat.Hom.hom key
  exact h2

theorem UpperTheory.Gal.Mod.clopenAt :
    ResClosed → HensSplit → ClopenAt := by
  intro _ hHS V _ _ _ _ W g _ z₀ hz₀
  haveI : IsAffine W := isAffine_of_isAffineHom g
  set φ : V →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ g.appTop).hom with hφ
  have hfin : φ.Finite := by
    have h1 := g.finite_appTop
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (fun a => ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom a, by simp⟩)
    exact h1.comp h2
  letI : Algebra V Γ(W, ⊤) := φ.toAlgebra
  haveI : Module.Finite V Γ(W, ⊤) := hfin
  have hc : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V →
      ∀ v : V, rho z (φ v) = IsLocalRing.residue V v := by
    intro z hz v
    exact RingHom.congr_fun (rho_comp V g z hz) v
  have hsurj : ∀ z : gp (IsLocalRing.ResidueField V) ⟶ W, z ≫ g = resPt V →
      Function.Surjective (rho z) := by
    intro z hz r
    obtain ⟨v, hv⟩ := IsLocalRing.residue_surjective r
    exact ⟨φ v, by rw [hc z hz v, hv]⟩
  have hmax : (RingHom.ker (rho z₀)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (hsurj z₀ hz₀)
  obtain ⟨e, he, hem, hoth⟩ := hHS V Γ(W, ⊤) (RingHom.ker (rho z₀)) hmax
  refine ⟨W.basicOpen e, clopen_basicOpen he, ?_⟩
  intro z hz
  rw [SetLike.mem_coe, mem_basicOpen_iff]
  constructor
  · intro hne
    have hk : RingHom.ker (rho z) = RingHom.ker (rho z₀) := by
      by_contra hk
      exact hne (RingHom.mem_ker.mp
        (hoth _ (RingHom.ker_isMaximal_of_surjective _ (hsurj z hz)) hk))
    apply rho_inj
    ext a
    obtain ⟨v, hv⟩ := IsLocalRing.residue_surjective (rho z₀ a)
    have hmem : a - φ v ∈ RingHom.ker (rho z₀) := by
      rw [RingHom.mem_ker, map_sub, hc z₀ hz₀ v, hv, sub_self]
    rw [← hk, RingHom.mem_ker, map_sub, sub_eq_zero, hc z hz v, hv] at hmem
    exact hmem
  · rintro rfl
    exact fun h => hem (RingHom.mem_ker.mpr h)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCorrComm
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.corrComm :
    CorrComm := by
  intro l _ p Y S S' B B' O g s bS β hS i bS' γ hcomm hl T w c c' hc hc' k j
  obtain ⟨v, hv, hf, hb, hw⟩ := hc
  obtain ⟨v', hv', hf', hb', hw'⟩ := hc'
  have hsq : v' ≫ T.p = (c'.p ≫ i) ≫ s := by
    rw [Category.assoc]
    exact hv'.w
  obtain ⟨u, huv, hup⟩ : ∃ u, u ≫ v = v' ∧ u ≫ c.p = c'.p ≫ i :=
    ⟨hv.lift v' (c'.p ≫ i) hsq, hv.lift_fst _ _ _, hv.lift_snd _ _ _⟩
  subst huv
  have hpb : IsPullback u c'.p c.p i := IsPullback.of_right hv' hup hv
  have hfu : c'.f ≫ i = u ≫ c.f := by
    apply hS.hom_ext
    · simp only [Category.assoc]
      rw [hf', hf, Category.assoc]
    · calc (c'.f ≫ i) ≫ bS = (c'.f ≫ bS') ≫ γ := by rw [Category.assoc, hcomm, Category.assoc]
        _ = (c'.p ≫ bS') ≫ γ := by rw [hb']
        _ = c'.p ≫ i ≫ bS := by rw [Category.assoc, hcomm]
        _ = (u ≫ c.p) ≫ bS := by rw [hup, Category.assoc]
        _ = (u ≫ c.f) ≫ bS := by rw [Category.assoc, Category.assoc, hb]
  have hwu : c'.w = Wt.comap u c.w := by
    rw [hw', hw]
    funext Ω _ _ z
    simp only [Wt.comap, Category.assoc]
  exact TranscendenceTraces.corrBCQ_holds a8 l k j c' c i i u hpb hfu hwu hl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCorrOpEq
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem isIso_reindex {W P : Scheme.{0}} {J : Type} {m : ℕ} (e : Fin m ≃ J) (f : J → (W ⟶ P))
    (h : IsIso (Sigma.desc f : ∐ (fun _ : J => W) ⟶ P)) :
    IsIso (Sigma.desc (fun i => f (e i)) : ∐ (fun _ : Fin m => W) ⟶ P) := by
  have heq : (Sigma.desc (fun i => f (e i)) : ∐ (fun _ : Fin m => W) ⟶ P) =
      (Sigma.reindex e (fun _ : J => W)).hom ≫ Sigma.desc f := by
    ext i
    have h2 : Sigma.ι (fun _ : Fin m => W) i ≫ (Sigma.reindex e (fun _ : J => W)).hom =
        Sigma.ι (fun _ : J => W) (e i) := Sigma.ι_reindex_hom e (fun _ : J => W) i
    rw [← Category.assoc, h2]
    simp
  rw [heq]
  infer_instance

private theorem existsUnique_sec {U P : Scheme.{0}} (p' : P ⟶ U) {m : ℕ} (s' : Fin m → (U ⟶ P))
    (hs : ∀ j, s' j ≫ p' = 𝟙 U) (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P))
    {Ω : Type} [Field Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P) (hy : y ≫ p' = x0) :
    ∃! j, x0 ≫ s' j = y := by
  classical
  set D : ∐ (fun _ : Fin m => U) ⟶ P := Sigma.desc s' with hD
  have hι : ∀ j, Sigma.ι (fun _ : Fin m => U) j ≫ D = s' j := fun j => Sigma.ι_desc _ _
  have huniq : ∀ j₁ j₂, x0 ≫ s' j₁ = x0 ≫ s' j₂ → j₁ = j₂ := by
    intro j₁ j₂ h
    rw [← hι j₁, ← hι j₂, ← Category.assoc, ← Category.assoc, cancel_mono] at h
    have h2 := congrArg (fun f : gp Ω ⟶ ∐ (fun _ : Fin m => U) => f (IsLocalRing.closedPoint Ω)) h
    simp only [Scheme.Hom.comp_apply] at h2
    have h3 := (sigmaι_eq_iff (fun _ : Fin m => U) j₁ j₂ _ _).mp h2
    exact (Sigma.mk.inj_iff.mp h3).1
  obtain ⟨⟨j, u⟩, hju⟩ :=
    (sigmaMk (fun _ : Fin m => U)).surjective ((y ≫ inv D) (IsLocalRing.closedPoint Ω))
  rw [sigmaMk_mk] at hju
  have hrange : Set.range (y ≫ inv D).base ⊆ Set.range (Sigma.ι (fun _ : Fin m => U) j).base := by
    rintro _ ⟨z, rfl⟩
    refine ⟨u, ?_⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
    exact hju
  obtain ⟨t, ht⟩ : ∃ t, t ≫ Sigma.ι (fun _ : Fin m => U) j = y ≫ inv D :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hy2 : t ≫ s' j = y := by
    rw [← hι j, ← Category.assoc, ht, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have htx : t = x0 := by
    rw [← hy, ← hy2, Category.assoc, hs, Category.comp_id]
  have hy3 : x0 ≫ s' j = y := by
    rw [← htx]
    exact hy2
  exact ⟨j, hy3, fun j₁ hj₁ => huniq _ _ (hj₁.trans hy3.symm)⟩

private theorem push_one {W S : Scheme.{0}} (c : W ⟶ S) [IsFinite c] [Surjective c] {G : Type} [Finite G]
    (a : G → (W ⟶ W)) (hs : Splits c c a) : (Wt.const W 1).push c = Wt.const S (Nat.card G : ℤ) := by
  classical
  obtain ⟨hac, hiso⟩ := hs
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (Fin m ≃ G) := ⟨Nat.card G, ⟨(Finite.equivFin G).symm⟩⟩
  have hiso' := isIso_reindex e _ hiso
  funext Ω _ _ x
  show ∑ᶠ (z : gp Ω ⟶ W) (_ : z ∈ fib c x), (1 : ℤ) = (Nat.card G : ℤ)
  obtain ⟨v, hv⟩ := c.surjective (pt x)
  obtain ⟨z0, hz0, -⟩ := TranscendenceTraces.ptLift_holds c Ω x v hv
  have key := fun (y : gp Ω ⟶ pullback c c) (hy : y ≫ pullback.snd c c = z0) =>
    existsUnique_sec (pullback.snd c c)
      (fun j => pullback.lift (a (e j)) (𝟙 W) (by rw [hac, Category.id_comp]))
      (fun j => pullback.lift_snd _ _ _) hiso' z0 y hy
  have hlift : ∀ g : G, z0 ≫ pullback.lift (a g) (𝟙 W) (by rw [hac, Category.id_comp]) =
      pullback.lift (z0 ≫ a g) z0 (by rw [Category.assoc, hac]) := by
    intro g
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
  have hfib : fib c x = Set.range (fun g : G => z0 ≫ a g) := by
    ext z
    constructor
    · intro hz
      have hzc : z ≫ c = z0 ≫ c := by
        rw [hz0]
        exact hz
      obtain ⟨j, hj, -⟩ := key (pullback.lift z z0 hzc) (pullback.lift_snd _ _ _)
      refine ⟨e j, ?_⟩
      have h1 := congrArg (· ≫ pullback.fst c c) hj
      simp only [Category.assoc, pullback.lift_fst] at h1
      exact h1
    · rintro ⟨g, rfl⟩
      show (z0 ≫ a g) ≫ c = x
      rw [Category.assoc, hac, hz0]
  have hinj : Function.Injective (fun g : G => z0 ≫ a g) := by
    intro g₁ g₂ h
    have h' : z0 ≫ a g₁ = z0 ≫ a g₂ := h
    obtain ⟨j, -, huniq⟩ := key (pullback.lift (z0 ≫ a g₁) z0 (by rw [Category.assoc, hac]))
      (pullback.lift_snd _ _ _)
    have e1 := huniq (e.symm g₁) (by
      simp only [Equiv.apply_symm_apply]
      exact hlift g₁)
    have e2 := huniq (e.symm g₂) (by
      simp only [Equiv.apply_symm_apply]
      rw [hlift g₂]
      congr 1
      exact h'.symm)
    exact e.symm.injective (e1.trans e2.symm)
  rw [hfib, finsum_mem_range hinj]
  haveI := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp

private theorem pull_inj (l : ℕ) [Fact l.Prime] {W S : Scheme.{0}} (c : W ⟶ S) [IsFinite c] [Etale c] [Surjective c]
    {G : Type} [Finite G] [Nonempty G] (a : G → (W ⟶ W)) (hs : Splits c c a) (hl : IsUnit (l : Γ(S, ⊤))) (k : ℤ) :
    Function.Injective (pullHQ l (sch.map c) k 0) := by
  have wt : IsWt c (Wt.const W 1) := by
    rw [← UpperTheory.Gal.TranscendenceTraces.multBasic_holds.2.2 c]
    exact UpperTheory.Gal.TranscendenceTraces.wtFlat_holds c
  have hd := UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.1 l k 0 c (Wt.const W 1) (Nat.card G : ℤ) wt hl (push_one c a hs)
  have hne : (((Nat.card G : ℤ) : ℤ) : ℚ_[l]) ≠ 0 := by
    have : (Nat.card G : ℤ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    exact_mod_cast this
  intro x y hxy
  have h1 := LinearMap.congr_fun hd x
  have h2 := LinearMap.congr_fun hd y
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 h2
  rw [hxy, h2] at h1
  exact (smul_right_injective _ hne h1).symm

theorem UpperTheory.Gal.Mod.corrOpEq :
    CorrOpEq := by
  intro l _ S c _ hw hl T hT
  obtain ⟨W, c', G, _, _, a, J, _, σ, hgal, hsplit, hTx⟩ := hT
  obtain ⟨hfin, het, hsurj, -, -, hsc⟩ := hgal
  haveI := hfin
  haveI := het
  haveI := hsurj
  haveI : IsFinite c.p := c.fin
  haveI : Nonempty G := ⟨1⟩
  obtain ⟨hσ, hiso⟩ := hsplit
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (Fin m ≃ J) := ⟨Fintype.card J, ⟨(Fintype.equivFin J).symm⟩⟩
  have hiso' := isIso_reindex e _ hiso
  have hsplitQ : ∀ k : ℤ, pullHQ l (sch.map c') k 0 ∘ₗ TranscendenceTraces.trHQ l c.p (Wt.const c.Z 1) k 0 =
      ∑ j : Fin m, pullHQ l (sch.map (σ (e j))) k 0 := fun k =>
    TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2 l k 0 c.p hl W c' m (fun j => σ (e j)) (fun j => hσ (e j)) hiso'
  have hinj : Function.Injective (pullTot l (sch.map c')) := by
    intro x y hxy
    refine DFinsupp.ext fun k => ?_
    have h := congrArg (fun z => z k) hxy
    simp only [pullTot, DirectSum.lmap_apply] at h
    exact pull_inj l c' a hsc hl k h
  apply LinearMap.ext
  intro x
  apply hinj
  rw [hTx x]
  refine DFinsupp.ext fun k => ?_
  have h1 := LinearMap.congr_fun (hsplitQ k) (pullHQ l (sch.map c.f) k 0 (x k))
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h1
  erw [DirectSum.sum_apply]
  simp only [pullTot, DirectSum.lmap_apply, TranscendenceTraces.Corr.opQ, hw, LinearMap.comp_apply, h1,
    TranscendenceTraces.pullHQ_comp]
  exact (e.sum_comp (fun j => pullHQ l (sch.map (σ j)) k 0 (pullHQ l (sch.map c.f) k 0 (x k)))).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCorrPull
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.corrPull :
    CorrPull := by
  intro p Y S B O g s bS β hS T w hw hr
  have hsq : (pullback.fst T.p s ≫ T.r) ≫ g = (pullback.snd T.p s ≫ bS) ≫ β := by
    rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, hS.w,
      Category.assoc]
  haveI := T.fin
  refine ⟨⟨pullback T.p s, pullback.snd T.p s, hS.lift _ _ hsq, Wt.comap (pullback.fst T.p s) w,
    inferInstance,
    TranscendenceTraces.wtBC_holds _ _ _ _ w (IsPullback.of_hasPullback T.p s) hw⟩,
    pullback.fst T.p s, IsPullback.of_hasPullback T.p s, hS.lift_fst _ _ _, ?_, rfl⟩
  exact hS.lift_snd _ _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFrobQ
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.frobQ :
    FrobTors → FrobQ := by
  intro hT l _ X p f hp h hl k
  have key : pullHl l (sch.map (absFrob X p f hp h)) k 0 = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun j => ?_)
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hu : IsUnit (((l ^ j : ℕ)) : Γ(X, ⊤)) := by
      rw [Nat.cast_pow]; exact hl.pow j
    exact hT (l ^ j) X p f hp h hu k (x.1 j)
  unfold pullHQ
  rw [key]
  exact LinearMap.baseChange_id
end

