module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_gen_of_local_on_base {X Y S : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ S) (e : S ⟶ Y) (he : e ≫ p = 𝟙 S)
    (hp : ∀ V : S.Opens, Function.Surjective (pullback.snd p V.ι).appTop.hom)
    (h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U), ∏ k, h (e ≫ φ k) ^ ε k = 1)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb L (fun k => (p ⁻¹ᵁ U).ι ≫ φ k) ε), t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen := by
  have loc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : LB.Gen (LB.LinComb L (fun i => (p ⁻¹ᵁ U).ι ≫ φ i) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U).toScheme) (b : Z ⟶ S) (z : Z) (J), Good L z J →
        r ≫ (p ⁻¹ᵁ U).ι = b ≫ e → val t r z J = 1 := by
    intro s
    obtain ⟨U, hs, t, ht⟩ := h s
    obtain ⟨n, n₁⟩ : ∃ n : (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme,
        n ≫ (p ⁻¹ᵁ U).ι = (p ⁻¹ᵁ U).ι ≫ p ≫ e :=
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ U).ι ((p ⁻¹ᵁ U).ι ≫ p ≫ e) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q (p y.1)) he
        exact (congrArg (· ∈ U) e').mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := fun i => (p ⁻¹ᵁ U).ι ≫ φ i) (ε' := ε)
      (fun V _ k => by
        have q := h0 V (fun χ => k ((p ⁻¹ᵁ U).ι ≫ p ≫ χ))
        refine Eq.trans (DVR.prod_sum₂ (K := K) (K' := K) (U := V) _
          (c := ∏ i, k ((p ⁻¹ᵁ U).ι ≫ φ i) ^ ε i) rfl
          (DVR.prod_neg _ _ ((Finset.prod_congr rfl fun i _ => by
            show k (n ≫ _ ≫ _) ^ _ = _
            rw [← Category.assoc n, n₁]; simp only [Category.assoc]).trans q))) ?_
        simp)
      (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
    refine ⟨U, hs, t', ht', fun Z r b z J hJ hr => ?_⟩
    have : r ≫ n = r := by
      rw [← cancel_mono (p ⁻¹ᵁ U).ι, Category.assoc, n₁, ← Category.assoc, hr, Category.assoc,
        ← Category.assoc e, he, Category.id_comp]
    rw [hv Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]
  choose U hU t ht hn using loc
  have agree : ∀ (s s' : S) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ U s).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ U s').toScheme) (z : Z) (J), Good L z J →
      r ≫ (p ⁻¹ᵁ U s).ι = r' ≫ (p ⁻¹ᵁ U s').ι → val (t s) r z J = val (t s') r' z J := by
    intro s s' Z r r' z J hJ hr
    let V : S.Opens := U s ⊓ U s'
    have mk : ∀ W : S.Opens, V ≤ W → ∃ m : pullback p V.ι ⟶ (p ⁻¹ᵁ W).toScheme,
        m ≫ (p ⁻¹ᵁ W).ι = pullback.fst p V.ι := fun W hW =>
      ⟨IsOpenImmersion.lift (p ⁻¹ᵁ W).ι (pullback.fst p V.ι) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have e' := congrArg (fun q => q y) (pullback.condition (f := p) (g := V.ι))
        exact (congrArg (· ∈ W) e').mpr (hW (pullback.snd p V.ι y).2)), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨m, hm⟩ := mk (U s) inf_le_left
    obtain ⟨m', hm'⟩ := mk (U s') inf_le_right
    let e' : V.toScheme ⟶ pullback p V.ι := pullback.lift (V.ι ≫ e) (𝟙 _) (by simp [he])
    have he' : e' ≫ pullback.fst p V.ι = V.ι ≫ e := pullback.lift_fst _ _ _
    obtain ⟨v, hv⟩ : ∃ v : Z ⟶ V.toScheme, v ≫ V.ι = (r ≫ (p ⁻¹ᵁ U s).ι) ≫ p :=
      ⟨IsOpenImmersion.lift V.ι ((r ≫ (p ⁻¹ᵁ U s).ι) ≫ p) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact ⟨(r y).2, (congrArg (fun q => p (q y) ∈ U s') hr).mpr (r' y).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
    let ρ : Z ⟶ pullback p V.ι := pullback.lift (r ≫ (p ⁻¹ᵁ U s).ι) v hv.symm
    have hρ : ρ ≫ pullback.fst p V.ι = r ≫ (p ⁻¹ᵁ U s).ι := pullback.lift_fst _ _ _
    have r₁ : ρ ≫ m = r := by rw [← cancel_mono (p ⁻¹ᵁ U s).ι, Category.assoc, hm, hρ]
    have r₂ : ρ ≫ m' = r' := by rw [← cancel_mono (p ⁻¹ᵁ U s').ι, Category.assoc, hm', hρ, hr]
    have key := gen_unique' hL (φ := fun i => m ≫ (p ⁻¹ᵁ U s).ι ≫ φ i) (ε := ε)
      (φ' := fun i => m' ≫ (p ⁻¹ᵁ U s').ι ≫ φ i) (ε' := ε)
      (fun W _ k => Finset.prod_congr rfl fun i _ => by
        show k (m' ≫ _ ≫ _) ^ _ = k (m ≫ _ ≫ _) ^ _
        rw [← Category.assoc, ← Category.assoc m, hm, hm'])
      (pullback.snd p V.ι) e' (pullback.lift_snd _ _ _) (hp V) (DVR.pullGen_isGen _ _ _ _ (ht s) m)
      (DVR.pullGen_isGen _ _ _ _ (ht s') m') (fun y I hI => by
        rw [val_pull hI, val_pull hI, hn s _ _ V.ι y I hI (by rw [Category.assoc, hm, he']),
          hn s' _ _ V.ι y I hI (by rw [Category.assoc, hm', he'])]) Z ρ z J hJ
    rwa [val_pull hJ, val_pull hJ, r₁, r₂] at key
  obtain ⟨u, hu, -⟩ := glue_gen hL φ ε (fun s => p ⁻¹ᵁ U s) (fun y => ⟨p y, hU _⟩) t ht agree
  exact ⟨u, hu⟩

theorem exists_gen_zsmul {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (k : ℤ) :
    ∃ u : LB.Gen (LB.LinComb L φ (fun i => k * ε i)), u.IsGen := by
  refine ⟨⟨fun j => t.s j ^ k⟩, fun i j => ?_⟩
  have h := congrArg (· ^ k) (ht i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  refine (Finset.prod_zpow _ _ _).symm.trans (Finset.prod_congr rfl fun a _ => ?_)
  exact (zpow_mul _ _ _).symm.trans (congrArg _ (mul_comm _ _))

theorem exists_gen_neg_of_sym (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (hs : Out.Sym A L) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] ![1, -1]), u.IsGen := by
  refine exists_gen_of_local_on_base hL _ _ A.hom η[A].left (Over.w η[A]) (fun V => surj_snd hG hA (Over.mk V.ι))
    (fun U _ h => ?_) (fun s => ?_)
  · have e : η[A].left ≫ (GrpObj.inv : A ⟶ A).left = η[A].left :=
      congrArg (fun q => q.left) (show η[A] ≫ (GrpObj.inv : A ⟶ A) = η[A] from GrpObj.one_inv)
    rw [Fin.prod_univ_two]
    show h (η[A].left ≫ (GrpObj.inv : A ⟶ A).left) ^ (1 : ℤ) * h (η[A].left ≫ 𝟙 _) ^ (-1 : ℤ) = 1
    rw [e, Category.comp_id]; simp
  · obtain ⟨U, hU, t, ht⟩ := hs s
    obtain ⟨t', ht', -⟩ := exists_gen hL
      (φ' := fun k => (A.hom ⁻¹ᵁ U).ι ≫ (![(GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) k) (ε' := ![1, -1])
      (fun V _ h => by simp [Fin.prod_univ_two]) t ht
    exact ⟨U, hU, t', ht'⟩

theorem exists_gen_negLB : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S),
    ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen := by
  intro hG S P k T
  obtain ⟨u, hu⟩ := exists_gen_neg_of_sym hG P.isAb P.isLB P.sym
  obtain ⟨w, hw⟩ := exists_gen_zsmul _ (DVR.pullGen_isGen _ _ _ _ hu (snd T P.A).left) (-k)
  obtain ⟨t, ht, -⟩ := exists_gen P.isLB (K' := Fin 2)
    (φ' := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) (ε' := ![k, -k])
    (fun V _ h => by simp [Fin.prod_univ_two, mul_comm]) w hw
  exact ⟨t, ht⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

universe u

section Descent

set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in
theorem _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine ⟨fun {A X Y Z fst snd f g} h hf hfst => ?_⟩
  obtain ⟨⟨hs, -⟩, hqc⟩ := hf
  have hsnd : Surjective snd := MorphismProperty.of_isPullback h hs
  have : QuasiCompact f := hqc
  have : QuasiCompact fst := hfst
  show QuasiCompact g
  rw [quasiCompact_iff]
  intro U hU hc
  have h1 : IsCompact (fst ⁻¹' (f ⁻¹' U)) :=
    (quasiCompact_iff fst).1 ‹_› _ (hU.preimage f.continuous) ((quasiCompact_iff f).1 ‹_› U hU hc)
  have hcond : ∀ z, f (fst z) = g (snd z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  have : g ⁻¹' U = snd '' (fst ⁻¹' (f ⁻¹' U)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := hsnd.surj y
      exact ⟨z, by simpa [Set.mem_preimage, hcond] using hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [Set.mem_preimage, ← hcond] using hz
  rw [this]
  exact h1.image snd.continuous


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in
theorem _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@QuasiSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : IsZariskiLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_
  · rintro X Y f ⟨hl, hs⟩
    exact ⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩
  · intro R S Y φ g hφ hfst
    obtain ⟨hs, -⟩ := hφ
    have : QuasiSeparated (pullback.fst (Spec.map φ) g) := hfst
    have : QuasiSeparatedSpace ↥(Limits.pullback (Spec.map φ) g) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (Spec.map φ) g)
    have hsnd : Surjective (pullback.snd (Spec.map φ) g) :=
      MorphismProperty.pullback_snd _ _ hs
    have : QuasiCompact (pullback.snd (Spec.map φ) g) :=
      MorphismProperty.pullback_snd _ _ (inferInstanceAs (QuasiCompact (Spec.map φ)))
    show QuasiSeparated g
    rw [quasiSeparated_iff_quasiSeparatedSpace]
    refine ⟨fun U V hU hUc hV hVc => ?_⟩
    set s := pullback.snd (Spec.map φ) g
    have hpre : ∀ W : Set Y, IsOpen W → IsCompact W → IsCompact (s ⁻¹' W) :=
      fun W hW hWc => (quasiCompact_iff s).1 ‹_› W hW hWc
    have : U ∩ V = s '' (s ⁻¹' U ∩ s ⁻¹' V) := by
      rw [← Set.preimage_inter, Set.image_preimage_eq _ hsnd.surj]
    rw [this]
    exact (QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage s.continuous) (hpre U hU hUc)
      (hV.preimage s.continuous) (hpre V hV hVc)).image s.continuous


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in
theorem _root_.GlobalTheory.isAffine_of_isPullback_of_flat_surjective {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X}
    {p : X ⟶ S} {q : Y ⟶ T} (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat f]
    [Surjective f] [IsAffine Y] : IsAffine X := by
  have hQf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f :=
    ⟨⟨‹Surjective f›, ‹Flat f›⟩, inferInstance⟩
  have : QuasiCompact p :=
    @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
      _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiCompact q))
  have : QuasiSeparated p :=
    @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
      _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc H.flip hQf (inferInstanceAs (QuasiSeparated q))
  have hSpec : IsPullback (Spec.map g.appTop) (Spec.map q.appTop) (Spec.map p.appTop)
      (Spec.map f.appTop) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (_root_.GlobalTheory.ProperFunctions.isPushout_appTop H)
  have hfsq : IsPullback (inv T.toSpecΓ) (Spec.map f.appTop) f (inv S.toSpecΓ) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, Scheme.toSpecΓ_naturality]⟩
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map g.appTop) :=
    MorphismProperty.of_isPullback hSpec.flip (MorphismProperty.of_isPullback hfsq hQf)
  have hiso : IsPullback T.toSpecΓ f (Spec.map f.appTop) S.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality f).symm⟩
  have hbig : IsPullback (Y.toSpecΓ ≫ Spec.map q.appTop) g (Spec.map f.appTop)
      (X.toSpecΓ ≫ Spec.map p.appTop) := by
    rw [← Scheme.toSpecΓ_naturality, ← Scheme.toSpecΓ_naturality]
    exact H.flip.paste_horiz hiso
  have htop : IsPullback Y.toSpecΓ g (Spec.map g.appTop) X.toSpecΓ :=
    IsPullback.of_right hbig (Scheme.toSpecΓ_naturality g).symm hSpec.flip
  have : MorphismProperty.isomorphisms Scheme.{u} X.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong htop hQ'
      (MorphismProperty.isomorphisms.infer_property _)
  exact ⟨this⟩


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency.types false in
theorem _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ (@Surjective ⊓ @Flat) ?_ ?_
  · rintro X Y f ⟨hl, hs⟩
    exact ⟨hs, IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ f hl⟩
  · intro R S Y φ g hφ hfst
    obtain ⟨hs, hfl⟩ := hφ
    have : Surjective (Spec.map φ) := hs
    have : Flat (Spec.map φ) := hfl
    have : IsAffineHom (pullback.fst (Spec.map φ) g) := hfst
    have : IsAffine (Limits.pullback (Spec.map φ) g) :=
      isAffine_of_isAffineHom (pullback.fst (Spec.map φ) g)
    have : IsAffine Y :=
      _root_.GlobalTheory.isAffine_of_isPullback_of_flat_surjective (IsPullback.of_hasPullback (Spec.map φ) g).flip
    show IsAffineHom g
    infer_instance

end Descent


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel :
    ∀ (S : Scheme.{0}) (G B T : Over S) [GrpObj G] [GrpObj B] [GrpObj T] (q : G ⟶ B) (i : T ⟶ G),
      IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left →
      IsPullback i (toUnit _) q (η[B]) → IsAffineHom T.hom → IsAffineHom q.left := by
  intro S G B T _ _ _ q i hq hi hfl hs hqc hker hT
  have hiq : i ≫ q = 1 := by rw [hker.w, Hom.one_def]
  have hw : fst G T ≫ q = (fst G T * (snd G T ≫ i)) ≫ q := by
    rw [mul_comp, Category.assoc, hiq, comp_one, _root_.mul_one]
  have hpb : IsPullback (fst G T) (fst G T * (snd G T ≫ i)) q q := by
    refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
      (fun s => lift s.fst (hker.lift (s.fst⁻¹ * s.snd) (toUnit _) (by
        rw [mul_comp, GrpObj.inv_comp, s.condition, inv_mul_cancel, Hom.one_def])))
      (fun s => lift_fst _ _) (fun s => ?_) (fun s m h1 h2 => ?_)⟩⟩
    · rw [comp_mul, lift_fst, ← Category.assoc, lift_snd, hker.lift_fst, mul_inv_cancel_left]
    · refine hom_ext _ _ (by rw [h1, lift_fst]) ?_
      rw [lift_snd]
      refine hker.hom_ext ?_ (toUnit_unique _ _)
      rw [hker.lift_fst, ← h1, ← h2, comp_mul, Category.assoc, inv_mul_cancel_left]
  have hfst : IsAffineHom (fst G T).left := by
    show IsAffineHom (pullback.fst G.hom T.hom)
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom T.hom).flip hT
  exact @MorphismProperty.of_isPullback_of_descendsAlong _ _ _ _ _ _ _ _ _ _ _ _
    _root_.GlobalTheory.isAffineHom_descendsAlong_fpqc (hpb.map (Over.forget S)) ⟨⟨hs, hfl⟩, hqc⟩ hfst

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrimCocycle

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

abbrev lamφ (B : Over S) [GrpObj B] : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
  fun I => (psum B (x2 B) I.down).left

abbrev lamε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem prod_lam {T : Over S} (x y : T ⟶ B) {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ I, h ((lift x y).left ≫ lamφ B I) ^ lamε I =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ B).left := by
  have e : ∀ I, (lift x y).left ≫ lamφ B I = (psum B ![x, y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I.down).trans
      (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum B ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ lamε I) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum B ![x, y] ∅ = 1 := rfl
  have p₁ : psum B ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum B ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum B ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem exists_normalised {L : LB B.left} (hL : L.IsLB) (t : LB.Gen (LB.LinComb L (lamφ B) lamε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (lamφ B) lamε), u.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good L z J → val₂ u z J (1 : T ⟶ B) 1 = 1 := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := lamφ B) (ε' := lamε)
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
        (c := ∏ i, k (lamφ B i) ^ lamε i) rfl
        (DVR.prod_neg _ _ (prod_lam (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B) k))) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (lift (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, fun T z J hJ => ?_⟩
  have : (lift (1 : T ⟶ B) (1 : T ⟶ B)).left ≫ (lift (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B)).left =
      (lift (1 : T ⟶ B) (1 : T ⟶ B)).left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
  rw [val₂, hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]

theorem val_mul_eq (hG : GlobalFnsSt) (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB)
    (u : LB.Gen (LB.LinComb L (lamφ B) lamε)) (hu : u.IsGen)
    (e : 𝟙_ (Over S) ⟶ G3 B) (a b c d a' b' c' d' : G3 B ⟶ B)
    (hF : ∀ (V : Type) [CommGroup V] (k : (G3 B ⟶ B) → V),
      (k (a' * b') * (k a')⁻¹ * (k b')⁻¹ * k 1) * (k (c' * d') * (k c')⁻¹ * (k d')⁻¹ * k 1) =
      (k (a * b) * (k a)⁻¹ * (k b)⁻¹ * k 1) * (k (c * d) * (k c)⁻¹ * (k d)⁻¹ * k 1))
    (ha : e ≫ a = 1) (hb : e ≫ b = 1) (hc : e ≫ c = 1) (hd : e ≫ d = 1)
    (ha' : e ≫ a' = 1) (hb' : e ≫ b' = 1) (hc' : e ≫ c' = 1) (hd' : e ≫ d' = 1)
    {T : Over S} (ρ : T ⟶ G3 B) {z : T.left} {J} (hJ : Good L z J) :
    val₂ u z J (ρ ≫ a) (ρ ≫ b) * val₂ u z J (ρ ≫ c) (ρ ≫ d) =
      val₂ u z J (ρ ≫ a') (ρ ≫ b') * val₂ u z J (ρ ≫ c') (ρ ≫ d') := by
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good L z J → ∀ a b : T ⟶ B,
      val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := fun ρ z J hJ a b => by
    rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
  have sj : Function.Surjective ((snd B (B ⊗ B)).left ≫ (snd B B).left ≫ B.hom).appTop.hom :=
    surj_comp (surj_snd hG hB _) (surj_comp (surj_snd hG hB _) (hG _ _ hB).2)
  have he : e.left ≫ (snd B (B ⊗ B)).left ≫ (snd B B).left ≫ B.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 B) {z : T'.left} {J}, Good L z J → ∀ a b c d : G3 B ⟶ B,
      val (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ u (lift a b).left) (LB.pullGen L _ _ u (lift c d).left))
        σ.left z J = val₂ u z J (σ ≫ a) (σ ≫ b) * val₂ u z J (σ ≫ c) (σ ≫ d) := fun σ z J hJ a b c d =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))
  refine (ev ρ hJ a b c d).symm.trans (Eq.trans (gen_unique' hL (fun V _ k => ?_) _ e.left he sj
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
    (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ a' b' c' d'))
  · exact (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
      (prod_lam a' b' k) (prod_lam c' d' k)).trans ((hF V fun q => k q.left).trans
      (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
        (prod_lam a b k) (prod_lam c d k)).symm)
  · refine (ev e hI a b c d).trans (Eq.trans ?_ (ev e hI a' b' c' d').symm)
    rw [ha, hb, hc, hd, ha', hb', hc', hd']

theorem primitive_cocycle : GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (O : RigLB B), (∃ t : LB.Gen (abelian₂ B O.L), t.IsGen) → ∃ t : LB.Gen (abelian₂ B O.L), t.IsGen ∧ ∀ (Z : Over S) (z : Z.left) (J : (Z.left ⟶ B.left) → O.L.ι), Geo.Tor.Good O.L z J → let v : (Z ⟶ B) → (Z ⟶ B) → (Z.left.presheaf.stalk z)ˣ := fun x y => Geo.Tor.val (L := O.L) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (ε := fun I => (-1) ^ (2 - I.down.card)) t (lift x y).left z J; (∀ x, v x 1 = 1) ∧ (∀ x y, v x y = v y x) ∧ ∀ x y w, v (x * y) w * v x y = v x (y * w) * v y w := by
  rintro hG S B _ _ hB O ⟨t, ht⟩
  obtain ⟨u, hu, h₀⟩ := exists_normalised O.isLB t ht
  refine ⟨u, hu, fun Z z J hJ => ?_⟩
  show (∀ x, val₂ u z J x 1 = 1) ∧ (∀ x y, val₂ u z J x y = val₂ u z J y x) ∧
    ∀ x y w, val₂ u z J (x * y) w * val₂ u z J x y = val₂ u z J x (y * w) * val₂ u z J y w
  let p₀ := x3 B 0
  let p₁ := x3 B 1
  let p₂ := x3 B 2
  let e : 𝟙_ (Over S) ⟶ G3 B := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have o : e ≫ (1 : G3 B ⟶ B) = 1 := MonObj.comp_one _
  have r₀ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₀ = x := fun x y w => by simp [p₀, x3]
  have r₁ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₁ = y := fun x y w => by simp [p₁, x3]
  have r₂ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₂ = w := fun x y w => by simp [p₂, x3]
  refine ⟨fun x => ?_, fun x y => ?_, fun x y w => ?_⟩
  · have := val_mul_eq hG hB O.isLB u hu e p₀ 1 1 1 1 1 1 1 (fun V _ k => by simp) e₀ o o o o o o o
      (lift x (lift x x)) hJ
    rw [r₀, MonObj.comp_one, h₀ Z z J hJ] at this
    simpa using this
  · have := val_mul_eq hG hB O.isLB u hu e p₀ p₁ 1 1 p₁ p₀ 1 1 (fun V _ k => by
      rw [mul_comm p₁ p₀, mul_right_comm (k (p₀ * p₁))]) e₀ e₁ o o e₁ e₀ o o (lift x (lift y x)) hJ
    rw [r₀, r₁] at this
    exact mul_right_cancel this
  · have := val_mul_eq hG hB O.isLB u hu e (p₀ * p₁) p₂ p₀ p₁ p₀ (p₁ * p₂) p₁ p₂ (fun V _ k => by
      rw [_root_.mul_assoc p₀ p₁ p₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) ((MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])) e₂ e₀ e₁ e₀
      ((MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])) e₁ e₂ (lift x (lift y w)) hJ
    rwa [MonObj.comp_mul, MonObj.comp_mul, r₀, r₁, r₂] at this

end GlobalTheory.PrimCocycle
end
end

