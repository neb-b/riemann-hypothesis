module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.EtaleCohomology.EtaleSheaves.Bundle0072
public import Development.EtaleCohomology.EtaleSheaves.Bundle0043
public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.ResMapNsmulHomotopy
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuPf
public import Development.EtaleCohomology.EtaleSheaves.KummerFields.H0Naturality
public import Development.EtaleCohomology.EtaleSheaves.KummerFields.GmSecSurj
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.EtaleCohomology.EtaleSheaves.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.FMrangePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf Topology

namespace LateralTheory.E.FMrangePf

def RRsub : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    RR w q ⊆ closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal})

theorem range_spec_atPrime {W : Type} [CommRing W] (q : PrimeSpectrum W) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))).base =
      {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal} := by
  have h := PrimeSpectrum.localization_comap_range (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  ext p
  change p ∈ Set.range (PrimeSpectrum.comap (algebraMap W (Localization.AtPrime q.asIdeal))) ↔ _
  rw [h]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hd x hx
    by_contra hq
    exact Set.disjoint_left.1 hd (show x ∈ (q.asIdeal.primeCompl : Set W) from hq) hx
  · intro hle
    exact Set.disjoint_left.2 fun x hx hp => hx (hle hp)

theorem mem_basicOpen_toNorm {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (s : Γ(w.normalization, ⊤)) (p : Spec (CommRingCat.of W)) :
    w.toNormalization p ∈ w.normalization.basicOpen s ↔ phi w s ∉ p.asIdeal := by
  change p ∈ w.toNormalization ⁻¹ᵁ w.normalization.basicOpen s ↔ _
  rw [Scheme.preimage_basicOpen_top, AlgebraicGeometry.basicOpen_eq_of_affine']
  rfl

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.appTop) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  exact h2.comp h1

theorem closure_sub_RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) :
    closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) ⊆ RR w q := by
  intro y hy s hs hsq
  have hid : IsIdempotentElem s := phi_injective w (by rw [map_mul]; exact hs.eq)
  have hcl : IsClosed (w.normalization.basicOpen s : Set w.normalization) := by
    rw [← isOpen_compl_iff]
    have : (w.normalization.basicOpen s : Set w.normalization)ᶜ = w.normalization.basicOpen (1 - s) := by
      ext x
      exact LateralTheory.E.SysFMPfSys.basicOpen_one_sub hid x
    rw [this]
    exact (w.normalization.basicOpen (1 - s)).isOpen
  refine closure_minimal ?_ hcl hy
  rintro _ ⟨p, hp, rfl⟩
  exact (mem_basicOpen_toNorm w s p).2 fun h => hsq (hp h)

def IdemLift : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ e : W, IsIdempotentElem e → ∃ s, phi w s = e

def QcIdem : Prop := ∀ (W : Type) [CommRing W], ProdACF W → ∀ U : (Spec (CommRingCat.of W)).Opens,
  IsCompact (U : Set (Spec (CommRingCat.of W))) → ∃ e : W, IsIdempotentElem e ∧ ∀ p : Spec (CommRingCat.of W),
    p ∈ U ↔ e ∉ p.asIdeal

theorem RRsub_of (hI : IdemLift) (hQ : QcIdem) : RRsub := by
  intro P _ _ W _ w hW q y hy
  by_contra hc
  rw [mem_closure_iff] at hc
  push Not at hc
  obtain ⟨o, ho, hyo, hoT⟩ := hc
  obtain ⟨V, hV, hyV, hVo⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens w.normalization))
    (show y ∈ (⟨o, ho⟩ : TopologicalSpace.Opens w.normalization) from hyo)
  have hVc : IsCompact (w.toNormalization ⁻¹ᵁ V : Set (Spec (CommRingCat.of W))) :=
    QuasiCompact.isCompact_preimage _ V.isOpen (IsAffineOpen.isCompact hV)
  obtain ⟨e, he, hpe⟩ := hQ W hW _ hVc
  have heq : e ∈ q.asIdeal := by
    by_contra hnq
    have hmem : w.toNormalization q ∈ V := (hpe q).2 hnq
    have : w.toNormalization q ∈ o ∩ (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) :=
      ⟨hVo hmem, q, show q.asIdeal ≤ q.asIdeal from le_refl _, rfl⟩
    rw [hoT] at this
    exact this
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hfq : (1 - e) ∉ q.asIdeal := fun h => q.2.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.asIdeal.add_mem heq h))
  obtain ⟨s, hs⟩ := hI W w hW (1 - e) hf
  have hys : y ∈ w.normalization.basicOpen s := hy s (by rw [hs]; exact hf) (by rw [hs]; exact hfq)
  obtain ⟨_, ⟨hz1, hz2⟩, p, rfl⟩ := w.toNormalization.denseRange.inter_open_nonempty
    ((w.normalization.basicOpen s ⊓ V : w.normalization.Opens) : Set w.normalization)
    (w.normalization.basicOpen s ⊓ V).isOpen ⟨y, hys, hyV⟩
  have h1 : phi w s ∉ p.asIdeal := (mem_basicOpen_toNorm w s p).1 hz1
  have h2 : e ∉ p.asIdeal := (hpe p).1 hz2
  rw [hs] at h1
  have : e * (1 - e) ∈ p.asIdeal := by rw [mul_sub, mul_one, he.eq, sub_self]; exact p.asIdeal.zero_mem
  rcases p.2.mem_or_mem this with h | h
  · exact h2 h
  · exact h1 h

theorem FMrange_of (hC : RRsub) : FMrange := by
  intro P _ _ W _ w hW q m e1 e2
  set a := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  have : IsIntegralHom (m ≫ w.fromNormalization) := by rw [e2]; infer_instance
  have : IsIntegralHom m := IsIntegralHom.of_comp m w.fromNormalization
  have hcl : IsClosedMap m.base := m.isClosedMap
  have hd : closure (Set.range (a ≫ w).toNormalization.base) = Set.univ :=
    (a ≫ w).toNormalization.denseRange.closure_range
  have himg : m.base '' Set.range (a ≫ w).toNormalization.base =
      w.toNormalization.base '' Set.range a.base := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext x
    simpa only [Function.comp_apply, ← Scheme.Hom.comp_apply] using
      congrArg (fun f : Spec (CommRingCat.of (Localization.AtPrime q.asIdeal)) ⟶
        w.normalization => f x) e1.symm
  rw [subset_antisymm (hC W w hW q) (closure_sub_RR w q), ← range_spec_atPrime q, ← Set.image_univ, ← hd,
    ← hcl.closure_image_eq_of_continuous m.continuous, himg]

theorem FMrange_of_leaves (hI : IdemLift) (hQ : QcIdem) : FMrange :=
  FMrange_of (RRsub_of hI hQ)

end LateralTheory.E.FMrangePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FiltrationLevelBase
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
  LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelBase

def Step0 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
    rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
    ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
      LateralTheory.E.FiltGenPf.V ((chains R).map g) (-1) n ((z : Cochain _ _ n) - δ (n - 1) n c)

theorem Filt_of (h0 : Step0) : LateralTheory.E.FiltrationLevelInjectivity.Filt := by
  intro _ R _ F n Z' Z X' X g h a b comm ha hb hlev
  have hk : ∀ p : ℕ, 1 ≤ p → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map g).f (-(p : ℤ)))))
      (res R F) n) := by
    intro p hp
    refine LateralTheory.E.CechFiltPf.Piece_of LateralTheory.E.DiscLvlPf.DiscLvl_of LateralTheory.E.ShiftLvlPf.ShiftLvl_of R F g p n ?_
    obtain ⟨hi, hs⟩ := hlev p hp (n - p) (by omega)
    refine LateralTheory.E.RelativeTruncationSingleDegree.sub_of R F _ _ ⟨fun m hm => ?_, hi⟩ (LateralTheory.E.RelativeTruncationSingleDegree.pull_fgt R F _ _)
    obtain rfl : m = n - p - 1 := by omega
    exact hs
  have hk' : ∀ k : ℤ, k ≤ -1 → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) k).map (((chains R).map g).f k))) (res R F) n) := by
    intro k hk1
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact hk p (by omega)
  have claim : ∀ m : ℕ, ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
      rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
      ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
        LateralTheory.E.FiltGenPf.V ((chains R).map g) (-((m : ℤ) + 1)) n ((z : Cochain _ _ n) - δ (n - 1) n c) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      have e : (-(((0 : ℕ) : ℤ) + 1)) = -1 := by norm_num
      rw [e]
      exact h0 R F n g h a b comm ha hb z hz
    | succ m ih =>
      intro z hz
      obtain ⟨c, hc⟩ := ih z hz
      have hkm := hk' (-((m : ℤ) + 1)) (by omega)
      have hs1 := LateralTheory.E.FiltGenPf.step ((chains R).map g) (-((m : ℤ) + 1)) n hkm
      have hzz : δ n (n + 1) ((z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c) = 0 := by
        rw [δ_sub, δ_δ, sub_zero]; exact Cocycle.δ_eq_zero z (n + 1)
      have hs2 := hs1 _ hzz
      obtain ⟨c', hc'⟩ := hs2 hc
      refine ⟨c + c', ?_⟩
      have e : (-((((m + 1 : ℕ) : ℤ)) + 1)) = -((m : ℤ) + 1) - 1 := by push_cast; ring
      rw [e, δ_add, ← sub_sub]
      exact hc'
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨c, hc1, hc2⟩ := claim (n.toNat + 1) z hx
  change CohomologyClass.mk z = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨c, ?_⟩
  have hz0 : (z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c = 0 := by
    rw [mappingCone.ext_cochain_from_iff _ (n - 1) n (by omega)]
    constructor
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc1 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc2 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
  rw [sub_eq_zero] at hz0
  exact hz0.symm

end LateralTheory.E.FiltrationLevelBase
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.Geo
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfB
open LateralTheory.E.LeafTw0LocGenPfA

theorem geo {q : ℕ} [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)) :
    Loc V fun W h => ∃ a : (ZMod q)ˣ, h.appTop ξ.1 = (h.appTop ζ.1) ^ (a : ZMod q).val := by
  classical
  have key : ∀ x : V, ∃ (Wx : V.Opens) (_ : x ∈ Wx) (a : (ZMod q)ˣ),
      V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op ξ.1 =
        V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op (ζ.1 ^ (a : ZMod q).val) := by
    intro x
    have hq : IsUnit ((q : V.presheaf.stalk x)) := by
      simpa using ζ.2.1.map (V.presheaf.germ ⊤ x trivial).hom
    have hr : ∀ z : Γ(V, ⊤), Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
        Polynomial.aeval ((V.presheaf.germ ⊤ x trivial).hom z) (Polynomial.cyclotomic q ℤ) = 0 := by
      intro z hz
      have h := Polynomial.aeval_algHom_apply (V.presheaf.germ ⊤ x trivial).hom.toIntAlgHom z (Polynomial.cyclotomic q ℤ)
      rw [hz, map_zero] at h
      exact h
    obtain ⟨a, ha⟩ := local_pow hq (hr _ ζ.2.2) (hr _ ξ.2.2)
    have h2 : (V.presheaf.germ ⊤ x trivial).hom ξ.1 = (V.presheaf.germ ⊤ x trivial).hom (ζ.1 ^ (a : ZMod q).val) := by
      rw [map_pow]; exact ha
    obtain ⟨Wx, hx, i1, i2, he⟩ := TopCat.Presheaf.germ_eq V.presheaf (U := ⊤) (V := ⊤) x trivial trivial _ _ h2
    refine ⟨Wx, hx, a, ?_⟩
    have e1 : i1 = homOfLE le_top := Subsingleton.elim _ _
    have e2 : i2 = homOfLE le_top := Subsingleton.elim _ _
    subst e1 e2
    exact he
  choose Wx hx a ha using key
  have fin : ∀ (x : V) {W : Scheme.{0}} (g' : W ⟶ (Wx x).toScheme),
      (g' ≫ (Wx x).ι).appTop ξ.1 = ((g' ≫ (Wx x).ι).appTop ζ.1) ^ (a x : ZMod q).val := by
    intro x W g'
    have hle : (Wx x).ι ''ᵁ ⊤ ≤ Wx x := by simp
    have hW : ∀ z : Γ(V, ⊤), (Wx x).ι.appTop z =
        V.presheaf.map (homOfLE hle).op (V.presheaf.map (homOfLE le_top : Wx x ⟶ ⊤).op z) := by
      intro z
      rw [Scheme.Opens.ι_appTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hW, hW, ha x]
    simp only [map_pow]
    exact map_pow (ConcreteCategory.hom (Scheme.Hom.appTop g')) _ _
  let 𝒰 : V.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers V (fun x => (Wx x).toScheme) (fun x => (Wx x).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  refine ⟨_, Scheme.Cover.mem_grothendieckTopology 𝒰, fun W h hh => ?_⟩
  obtain ⟨x, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  exact ⟨a x, fin x g⟩

end LateralTheory.E.LeafTw0LocGenPfB
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GeoProof
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.GeoProof
open LateralTheory.E.E4 LateralTheory.E.Bridge_yfiPf

theorem affNbhd {B : Scheme.{0}} (U : B.Etale) (u : U.left) :
    ∃ (U' : B.Etale) (a : U' ⟶ U) (R : CommRingCat.{0}) (_ : U'.left ≅ Spec R) (u' : U'.left), a.left u' = u := by
  let f := U.left.affineCover.f (U.left.affineCover.idx u)
  have : IsOpenImmersion f := U.left.affineCover.map_prop _
  refine ⟨Scheme.Etale.mk (f ≫ U.hom), MorphismProperty.Over.homMk f rfl trivial, _, Iso.refl _, ?_⟩
  exact U.left.affineCover.covers u

def AffGeo : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (R : CommRingCat.{0}) (_ : U.left ≅ Spec R) (m : ℤ) (u : U.left), Nonempty (Sys q i p ι U m u)

def Shrink : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U U' : B.Etale)
  (a : U' ⟶ U) (m : ℤ) (u' : U'.left), Sys q i p ι U' m u' → Nonempty (Sys q i p ι U m (a.left u'))

theorem Geo_of (hA : AffGeo) (hS : Shrink) : Geo := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m u
  obtain ⟨U', a, R, e, u', rfl⟩ := affNbhd U u
  obtain ⟨S⟩ := hA hH q k hq i toK ι p hp U' R e m u'
  exact hS q i p ι U U' a m u' S

end LateralTheory.E.GeoProof
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IdemSecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.SysFMPf

namespace LateralTheory.E.IdemSecPf

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.app ⊤) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  intro a b h
  exact h1 (h2 h)

theorem phi_idem {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (e : W) (he : IsIdempotentElem e) : ∃ s, phi w s = e := by
  let t : Γ(Spec (CommRingCat.of W), w.toNormalization ⁻¹ᵁ ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv e
  have ht : (w.toNormalization.app ⊤).hom.IsIntegralElem t := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num))
    · have : t * t = t := by
        show (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e * (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom e = _
        rw [← map_mul, he.eq]
      rw [sq, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, this, sub_self]
  obtain ⟨s, hs⟩ := GlobalTheory.mem_range_toNormalization_app w ⊤ t ht
  refine ⟨s, ?_⟩
  show (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom (w.toNormalization.app ⊤ s) = e
  rw [hs]
  show ((Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom e = e
  simp

theorem IdemSec_of : LateralTheory.E.SysFMPfSys.IdemSec := by
  intro P _ _ W _ w
  exact ⟨phi_injective w, fun e he => phi_idem w e he⟩

end LateralTheory.E.IdemSecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.KummerFields
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKumFieldPf

open LateralTheory.E.E4

theorem kumMu : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumMu := fun hy =>
  LateralTheory.E.H2CurveOrder.LeafKumMuPf.LeafKumMu_of hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2.2.1
    LateralTheory.E.H2CurveOrder.muUnits hy

theorem etale_kummer_sequence_degree_zero_global_sections : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.KummerUnitsSurjectH0 := fun hy =>
  LateralTheory.E.H2CurveOrder.KummerH0Surjection.etale_kummer_degree_zero_cohomology_of_sections_and_units_surjective LateralTheory.E.H2CurveOrder.kumSecSurj
    (LateralTheory.E.LeafKumFieldPf.H0Naturality.etale_degree_zero_cohomology_natural_in_sheaf hy.2.2.2.2.2.2.2.1)
    LateralTheory.E.LeafKumFieldPf.GmSecSurj.LeafGmSecSurj_of hy

theorem kumSeq : LateralTheory.E.LeafKumCut.LeafKumSeq :=
  LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumSeq_of kumMu etale_kummer_sequence_degree_zero_global_sections

end LateralTheory.E.LeafKumFieldPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf LateralTheory.E.LeafObjGluePf GlobalTheory.GlueModels

namespace LateralTheory.E.LeafGlueTwoPf

def LeafPushoutFP : Prop := ∀ {DW DU DV S : Scheme.{0}} (φU : DW ⟶ DU) (φV : DW ⟶ DV) [IsOpenImmersion φU]
    [IsOpenImmersion φV] (qU : DU ⟶ S) (qV : DV ⟶ S) (h : φU ≫ qU = φV ≫ qV), IsAffine S →
    FP qU → FP qV → FP (φU ≫ qU) → FP (pushout.desc qU qV h)

set_option backward.isDefEq.respectTransparency false in
theorem LeafGlueTwo_of (hF : LeafPushoutFP) : LeafGlueTwo := by
  intro k _ Ω _ _ X f U V R hUV ⟨DU, DV, DW, qU, qV, qW, vU, vV, vW, φU, φV, hqU, hqV, hqW, hφU, hφV, eU, eV,
    pU, pV, pW, cU, cV⟩
  have hc : ∀ x : X, x ∈ Set.range U.ι ∨ x ∈ Set.range V.ι := by
    intro x
    have hx : x ∈ (U ⊔ V : X.Opens) := by rw [hUV]; trivial
    rcases hx with hx | hx
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (by simpa using hx)
  have hsq : IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι := isPullback_opens_inf U V
  have hab : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ vU ≫ pushout.inl φU φV =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ vV ≫ pushout.inr φU φV := by
    rw [← Category.assoc, ← Category.assoc, ← cU, ← cV, Category.assoc, Category.assoc, pushout.condition]
  obtain ⟨v, h1, h2⟩ := exists_glue hsq hc _ _ hab
  have hh : φU ≫ qU = φV ≫ qV := eU.trans eV.symm
  have := isOpenImmersion_inl φU φV
  have := isOpenImmersion_inr φU φV

  have HV : IsPullback vW (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) φV vV := by
    refine IsPullback.of_bot ?_ cV pV
    rw [← Category.assoc, Scheme.homOfLE_ι, eV]; exact pW
  have HU : IsPullback vW (X.homOfLE (inf_le_left : U ⊓ V ≤ U)) φU vU := by
    refine IsPullback.of_bot ?_ cU pU
    rw [← Category.assoc, Scheme.homOfLE_ι, eU]; exact pW
  have e1 (x : U.toScheme) : v (U.ι x) = pushout.inl φU φV (vU x) := congrArg (fun g => g x) h1
  have e2 (x : V.toScheme) : v (V.ι x) = pushout.inr φU φV (vV x) := congrArg (fun g => g x) h2
  refine ⟨pushout φU φV, pushout.desc qU qV hh, v, hF φU φV qU qV hh inferInstance hqU hqV (eU ▸ hqW), ?_⟩
  refine isPullback_of_two (pushout_cover φU φV) (u' := U.ι) (v' := V.ι) (aU := vU) (aV := vV) ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback HV w x hw
        refine ⟨X.homOfLE inf_le_left z, ?_⟩
        exact congrArg (fun g => g z) hsq.w
    · rintro ⟨y, rfl⟩
      exact ⟨vU y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback HU w x hw
        refine ⟨X.homOfLE inf_le_right z, ?_⟩
        exact (congrArg (fun g => g z) hsq.w).symm
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨vV y, (e2 y).symm⟩
  · simpa only [pushout.inl_desc] using pU
  · simpa only [pushout.inr_desc] using pV

end LateralTheory.E.LeafGlueTwoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSHSievePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHSievePf

theorem LeafSHSieve_of : LateralTheory.E.LeafClosedSH0Pf.LeafSHSieve := by
  intro X _ hSH S hS
  obtain ⟨hHens, hSep⟩ := hSH
  let A : Type := Γ(X, ⊤)
  let K : Type := IsLocalRing.ResidueField A
  let π : A →+* K := IsLocalRing.residue A
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  let x : Spec (.of K) ⟶ X := Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber K).jointly_surjective _
    (Scheme.Cover.mem_grothendieckTopology 𝒰) x
  obtain ⟨Z, h, _, ⟨i⟩, rfl⟩ := hg
  have hy' : (y ≫ h) ≫ 𝒰.f i = Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv := by
    exact (Category.assoc _ _ _).trans hy
  obtain ⟨l, ⟨-, hl⟩, -⟩ := GlobalTheory.existsUnique_lift_of_etale_of_henselian (𝒰.f i) π
    IsLocalRing.residue_surjective (y ≫ h) X.isoSpec.inv hy'
  have hmem : S (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have := S.downward_closed hmem (X.isoSpec.hom ≫ l)
  have e : (X.isoSpec.hom ≫ l) ≫ 𝒰.f i = 𝟙 X := by rw [Category.assoc, hl, Iso.hom_inv_id]
  rwa [e] at this

end LateralTheory.E.LeafSHSievePf
end
end

