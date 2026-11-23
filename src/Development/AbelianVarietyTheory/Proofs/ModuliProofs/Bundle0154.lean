module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SegreCoordinates
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MonoOfGeomPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FibreEmbed

theorem mono_of_geom_points {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h₁ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y')
    (h₂ : ∀ (k : Type) [Field k] [IsAlgClosed k] (w : Sp (DualNumber k) ⟶ X),
      w ≫ f = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w ≫ f →
        w = TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w) : Mono f := by
  have hu : FormallyUnramified f := TangentCrit.formallyUnramified_of_tangent f h₂
  have hs : Surjective (pullback.diagonal f) := by
    refine ((tfae_universallyInjective f).out 2 4).1 fun (k : Type) [Field k] y y' e => ?_
    let x : Sp (AlgebraicClosure k) ⟶ Sp k := spMap (algebraMap k (AlgebraicClosure k))
    have : Surjective x :=
      ⟨fun z => ⟨(default : PrimeSpectrum (AlgebraicClosure k)), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
    have : Epi x := Flat.epi_of_flat_of_surjective x
    refine (cancel_epi x).1 (h₁ _ _ _ ?_)
    rw [Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]; rfl

theorem sp_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem projRep_of_fibres : ∀ (R σ : Type) [CommRing R] [Finite σ] (X : Scheme.{0}) (s : X ⟶ Sp R) (M : LB X) (th : σ → M.Sec), M.IsLB → IsProper s → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K), ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (s' : X' ⟶ Sp K) (M' : LB X') (th' : σ → M'.Sec) (I : Ideal (MvPolynomial σ K)), IsPullback π s' s (spMap x) ∧ ProjRep I s' M' th' ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X') (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ π) w) → ProjRep (idealOf s M th (𝟙 X)) s M th := by
  intro R σ _ _ X s M th hM hs H
  obtain ⟨P, sP, MP, thP, -, hP, -⟩ := _root_.GlobalTheory.ProjFlat.exists_projRep_flat R σ ⊥ 0 (by
    intro F hF e
    rw [Ideal.mem_bot] at hF
    simp [hF])
  have hPp : IsProper sP := (_root_.GlobalTheory.ZM.projRep_projective_ample R σ ⊥ (Over.mk sP) MP thP hP).2.1
  obtain ⟨f, hf, -, hfc, -⟩ := GlobalTheory.T.exists_scheme_map_of_projective_coordinates R σ ⊥ P X sP s MP M thP th hP hM (by
    intro R' _ β y v hy hv
    refine ⟨?_, fun F hF => by rw [Ideal.mem_bot] at hF; simp [hF]⟩
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    letI := Ideal.Quotient.field m
    let K := AlgebraicClosure (R' ⧸ m)
    let φ : R' →+* K := (algebraMap (R' ⧸ m) K).comp (Ideal.Quotient.mk m)
    obtain ⟨X', π, s', M', th', I, hpb, hrep, hc⟩ := H K (φ.comp β)
    have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ hM hv).1 K φ
    have e : (spMap φ ≫ y) ≫ s = 𝟙 _ ≫ spMap (φ.comp β) := by
      rw [Category.assoc, hy, sp_comp, Category.id_comp]
    have h2 := (hrep.2.1 K (RingHom.id K) (hpb.lift _ _ e) _ (by rw [hpb.lift_snd, sp_id])
      ((hc K _ _).2 (by rw [hpb.lift_fst]; exact h1))).1
    have h3 : Ideal.span (Set.range fun i => φ (v i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      have : Ideal.Quotient.mk m (v i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.subset_span ⟨i, rfl⟩))
      simp [φ, this]
    exact bot_ne_top (h3.symm.trans h2))
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (T : Type) [CommRing T] [IsLocalRing T] (c : K →+* T)
      (x : Sp K ⟶ Sp R) (y y' : Sp T ⟶ X), y ≫ s = spMap c ≫ x → y ≫ f = y' ≫ f → y = y' := by
    intro K _ _ T _ _ c x y y' hy e
    obtain ⟨x, rfl⟩ : ∃ g : R →+* K, spMap g = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
    have hy' : y' ≫ s = spMap c ≫ spMap x := by
      rw [← hy, ← hf, ← Category.assoc, ← e, Category.assoc]
    obtain ⟨X', π, s', M', th', I, hpb, hrep, hc⟩ := H K x
    obtain ⟨v, hv⟩ := (_root_.GlobalTheory.ZM.LocalCoord.secCoord_local X M σ th hM).1 T y
    have hv' : SecCoord M th y' v := (hfc T y' v).2 (e ▸ (hfc T y v).1 hv)
    have a1 : SecCoord M' th' (hpb.lift _ _ hy) v := (hc T _ _).2 (by rw [hpb.lift_fst]; exact hv)
    have a2 : SecCoord M' th' (hpb.lift _ _ hy') v := (hc T _ _).2 (by rw [hpb.lift_fst]; exact hv')
    obtain ⟨u1, u2⟩ := hrep.2.1 T c _ v (hpb.lift_snd _ _ hy) a1
    have := (hrep.2.2 T c v u1 u2).unique ⟨hpb.lift_snd _ _ hy, a1⟩ ⟨hpb.lift_snd _ _ hy', a2⟩
    rw [← hpb.lift_fst _ _ hy, this, hpb.lift_fst]
  have : IsProper (f ≫ sP) := hf ▸ hs
  have : IsProper f := IsProper.of_comp f sP
  have hm : Mono f := by
    refine mono_of_geom_points f (fun k _ _ y y' e => key k k (RingHom.id k) (y ≫ s) y y' ?_ e)
      fun k _ _ w hw => key k (DualNumber k) (algebraMap _ _) (TangentCrit.dualPt k ≫ w ≫ s) _ _ ?_ ?_
    · rw [sp_id, Category.id_comp]
    · have := congrArg (· ≫ sP) hw
      simpa only [Category.assoc, hf] using this
    · simpa only [Category.assoc] using hw
  have hci : IsClosedImmersion f := (IsClosedImmersion.iff_isProper_and_mono f).2 ⟨‹_›, hm⟩
  have := _root_.GlobalTheory.ZM.ClosedCoord.projRep_closed R σ ⊥ P X sP MP thP f M th hP hci hM hfc
  rwa [hf] at this

end GlobalTheory.FibreEmbed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaCoordinateSchemeData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem reduced_flat_of_charts {Z S : Scheme.{0}} (s : Z ⟶ S) (U : Z.Opens) {κ : Type} (Y : κ → Scheme.{0})
    (x : ∀ i, Y i ⟶ Z) (hx : ∀ i, IsOpenImmersion (x i)) (hr : ∀ i, IsReduced (Y i)) (hf : ∀ i, Flat (x i ≫ s))
    (hc : ∀ z ∈ U, ∃ i, z ∈ Set.range (x i)) : IsReduced U.toScheme ∧ Flat (U.ι ≫ s) := by
  let 𝒰 : U.toScheme.OpenCover := Scheme.Cover.mkOfCovers κ (fun i => pullback U.ι (x i)) (fun i => pullback.fst U.ι (x i))
    (fun z => by
      obtain ⟨i, y, hy⟩ := hc z.1 z.2
      have : z ∈ Set.range (pullback.fst U.ι (x i)) := by
        rw [Scheme.Pullback.range_fst]
        exact ⟨y, hy⟩
      exact ⟨i, this⟩) (fun i => inferInstance)
  constructor
  · haveI : ∀ i, IsReduced (𝒰.X i) := fun i =>
      by
      change IsReduced (pullback U.ι (x i) :)
      haveI := hr i
      exact isReduced_of_isOpenImmersion (pullback.snd U.ι (x i))
    exact IsReduced.of_openCover _ 𝒰
  · haveI : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
    refine IsZariskiLocalAtSource.of_openCover (P := @Flat) 𝒰 (fun i => ?_)
    change Flat (pullback.fst U.ι (x i) ≫ U.ι ≫ s)
    rw [← Category.assoc, pullback.condition, Category.assoc]
    haveI := hf i
    haveI := hx i
    exact MorphismProperty.comp_mem @Flat _ _ inferInstance (hf i)

theorem flat_spMap_of_torsionFree {o σ : Type} [CommRing o] [IsDedekindDomain o] (J : Ideal (MvPolynomial σ o))
    (h : ∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ J → F ∈ J) :
    Flat (spMap ((Ideal.Quotient.mk J).comp MvPolynomial.C)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  have : Module.IsTorsionFree o (MvPolynomial σ o ⧸ J) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro c y hy
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [Ideal.Quotient.eq_zero_iff_mem]
      apply h c F hc
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← MvPolynomial.smul_eq_C_mul]
      exact hy
  have hfl : Module.Flat o (MvPolynomial σ o ⧸ J) := inferInstance
  exact (RingHom.flat_algebraMap_iff.2 hfl :)

theorem nonempty_MMPre : ∀ (o : Type) [CommRing o] [IsDedekindDomain o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)), 0 < N' → I.IsRadical → (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (∀ (c : o) F, c ≠ 0 → MvPolynomial.C c * F ∈ I → F ∈ I) → Nonempty (MMPre n N' I) := by
  intro o _ _ g n N' I hN hrad hhom htf
  haveI : NeZero (N' ^ 2) := ⟨by positivity⟩
  obtain ⟨Z, s, M, th, hproj, hrep, hfp, -⟩ := _root_.GlobalTheory.ProjFlat.exists_projRep_flat o (Ix g (N' ^ 2)) I 0 hhom
  obtain ⟨N, j, hj, hjs⟩ := hproj ⟨0⟩
  haveI := hfp (IsNoetherian.noetherian I)
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  let U : Z.Opens := ⟨⋂ a, ⋃ c, (Out.nonzeroLocus (th (a + (N' / n) • c)) : Set Z),
    isOpen_iInter_of_finite fun a => isOpen_iUnion fun c => (Out.nonzeroLocus _).2⟩
  have hU : ∀ z : Z, z ∈ U ↔ ∀ a, ∃ c, z ∈ Out.nonzeroLocus (th (a + (N' / n) • c)) := fun z => by
    change z ∈ ⋂ a, ⋃ c, (Out.nonzeroLocus (th (a + (N' / n) • c)) : Set Z) ↔ _
    simp only [Set.mem_iInter, Set.mem_iUnion, SetLike.mem_coe]
  choose x hxo hxr hxs _ using fun i => _root_.GlobalTheory.ZM.CoordChart.exists_chart o _ I Z s M th i hrep
  obtain ⟨hred, hflat⟩ := reduced_flat_of_charts s U _ x hxo
    (fun i => by
      haveI : _root_.IsReduced (MvPolynomial (Ix g (N' ^ 2)) o ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) :=
        (Ideal.isRadical_iff_quotient_reduced _).1 ((_root_.GlobalTheory.dehomogenisation_isRadical_and_torsionFree o _ I i hhom).1 hrad)
      infer_instance)
    (fun i => by
      rw [hxs i]
      exact flat_spMap_of_torsionFree _ ((_root_.GlobalTheory.dehomogenisation_isRadical_and_torsionFree o _ I i hhom).2 htf))
    (fun z hz => by
      obtain ⟨c, hc⟩ := (hU z).1 hz 0
      exact ⟨_, by rw [hxr]; exact hc⟩)
  obtain ⟨hpull, -, hnz⟩ := _root_.GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus Z M _ th hrep.1
  obtain ⟨th', hth'⟩ := hpull U.toScheme U.ι
  refine ⟨{ MM := U.toScheme, s := U.ι ≫ s, qproj := ⟨N, U.ι ≫ j, inferInstance, inferInstance, by rw [Category.assoc, hjs]⟩
            flat := hflat, reduced := hred, de := M.pull U.ι, isLB := pull_isLB hrep.1 _, th := th', loc := ?_, pts := ?_ }⟩
  · intro R _ β y v hy hv
    rw [hth'] at hv
    refine ⟨(hrep.2.1 R β (y ≫ U.ι) v (by rw [Category.assoc, hy]) hv).2, fun q hq a => ?_⟩
    let p : Sp R := (⟨q, hq⟩ : PrimeSpectrum R)
    obtain ⟨c, hc⟩ := (hU ((y ≫ U.ι) p)).1 (by rw [Scheme.Hom.comp_apply]; exact (y p).2) a
    exact ⟨c, (hnz R _ v _ p hv).1 hc⟩
  · intro R _ β v hv
    have hspan : Ideal.span (Set.range v) = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨c, hc⟩ := hv.2 m hm.isPrime 0
      exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))
    obtain ⟨y, ⟨hys, hyv⟩, huniq⟩ := hrep.2.2 R β v hspan hv.1
    have hrange : Set.range y ⊆ Set.range U.ι := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine (hU _).2 fun a => ?_
      obtain ⟨c, hc⟩ := hv.2 p.asIdeal p.isPrime a
      exact ⟨c, (hnz R y v _ p hyv).2 hc⟩
    have hl := IsOpenImmersion.lift_fac U.ι y hrange
    refine ⟨IsOpenImmersion.lift U.ι y hrange, ⟨by rw [← Category.assoc, hl, hys], by rw [hth', hl]; exact hyv⟩, ?_⟩
    rintro y' ⟨h1, h2⟩
    rw [hth'] at h2
    rw [← cancel_mono U.ι, hl]
    exact huniq _ ⟨by rw [Category.assoc, h1], h2⟩

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjRepGraphSegreCoordinatesFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GraphSegre

theorem idealOf_eq_graphIdeal {K σ₁ σ₂ : Type} [CommRing K] {Y X₁ X₂ : Scheme.{0}} (s : Y ⟶ Sp K)
    (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂)
    (N : LB Y) (ty : σ₁ × σ₂ → N.Sec) (h₁ : M₁.IsLB) (h₂ : M₂.IsLB) (hN : N.IsLB)
    (H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2)) :
    idealOf s N ty (𝟙 Y) = graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ := by
  ext F
  simp only [idealOf, graphIdeal, Ideal.mem_iInf, RingHom.mem_ker, Category.comp_id]
  constructor
  · intro hF T _ β y v₁ v₂ h
    exact hF T _ β y _ ⟨h.1, H T y v₁ v₂ h.2.1 h.2.2⟩
  · intro hF T _ β y v h
    refine eq_zero_of_localization _ fun J hJ => ?_
    set φ := algebraMap T (Localization.AtPrime J) with hφ
    obtain ⟨v₁, hv₁⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₁ M₁ σ₁ th₁ h₁).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₁)
    obtain ⟨v₂, hv₂⟩ := (GlobalTheory.ZM.LocalCoord.secCoord_local X₂ M₂ σ₂ th₂ h₂).1 (Localization.AtPrime J) ((spMap φ ≫ y) ≫ a₂)
    have hv := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty T y v hN h.2).1 _ φ
    obtain ⟨u, hu⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N _ ty _ _ _ hN (H _ _ v₁ v₂ hv₁ hv₂)).2.2 _ hv
    have hv₁' := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique X₁ M₁ _ th₁ _ _ _ h₁ hv₁).2.1 u
    have hs : (spMap φ ≫ y) ≫ s = spMap (φ.comp β) := by
      rw [Category.assoc, h.1]
      exact (Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom φ)).symm
    have key := hF _ _ (φ.comp β) (spMap φ ≫ y) _ v₂ ⟨hs, hv₁', hv₂⟩
    rw [MvPolynomial.map_eval₂Hom, ← key]
    congr 2
    funext i
    rw [hu i, _root_.mul_assoc]

theorem projRep_graph : ∀ (R K σ₁ σ₂ : Type) [CommRing R] [CommRing K] [Finite σ₁] [Finite σ₂] (x : R →+* K) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (Z₁ Z₂ : Over (Sp R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (Y : Scheme.{0}) (s : Y ⟶ Sp K) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsPullback a₁ s Z₁.hom (spMap x) → a₂ ≫ Z₂.hom = s ≫ spMap x → ∃ (N : LB Y) (ty : σ₁ × σ₂ → N.Sec), ProjRep (graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂) s N ty ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ → SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2) := by
  intro R K σ₁ σ₂ _ _ _ _ x I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ Y s a₁ a₂ r₁ r₂ hp ha₂
  obtain ⟨I₃, M₃, th₃, r₃, hseg⟩ := GlobalTheory.ZM.SegreCoord.segre_coordinates R σ₁ σ₂ I₁ I₂ Z₁ Z₂ M₁ M₂ th₁ th₂ r₁ r₂
  have hprop : IsProper Z₂.hom := (GlobalTheory.ZM.projRep_projective_ample R σ₂ I₂ Z₂ M₂ th₂ r₂).2.1
  have hP : IsPullback (fst Z₁ Z₂).left (snd Z₁ Z₂).left Z₁.hom Z₂.hom := IsPullback.of_hasPullback Z₁.hom Z₂.hom
  have hW := IsPullback.of_hasPullback (Z₁ ⊗ Z₂).hom (spMap x)
  generalize pullback.fst (Z₁ ⊗ Z₂).hom (spMap x) = π at hW
  generalize pullback.snd (Z₁ ⊗ Z₂).hom (spMap x) = s' at hW
  generalize pullback (Z₁ ⊗ Z₂).hom (spMap x) = Wd at π s' hW
  obtain ⟨th', r', hbc⟩ := GlobalTheory.ZM.RepBC.projRep_baseChange R K _ x I₃ _ Wd _ s' π M₃ th₃ r₃ hW
  have hfw : (fst Z₁ Z₂).left ≫ Z₁.hom = (Z₁ ⊗ Z₂).hom := Over.w _
  let a : Y ⟶ (Z₁ ⊗ Z₂).left := hP.lift a₁ a₂ (hp.w.trans ha₂.symm)
  have e₁ : a ≫ (fst Z₁ Z₂).left = a₁ := hP.lift_fst _ _ _
  have e₂ : a ≫ (snd Z₁ Z₂).left = a₂ := hP.lift_snd _ _ _
  let i : Y ⟶ Wd := hW.lift a s (by rw [← hfw, ← Category.assoc, e₁, hp.w])
  have i₁ : i ≫ π = a := hW.lift_fst _ _ _
  have i₂ : i ≫ s' = s := hW.lift_snd _ _ _
  let q : Wd ⟶ Y := hp.lift (π ≫ (fst Z₁ Z₂).left) s' (by rw [Category.assoc, hfw, hW.w])
  have q₁ : q ≫ a₁ = π ≫ (fst Z₁ Z₂).left := hp.lift_fst _ _ _
  have q₂ : q ≫ s = s' := hp.lift_snd _ _ _
  have hq : IsPullback π q (fst Z₁ Z₂).left a₁ := by
    refine IsPullback.of_bot ?_ q₁.symm hp
    rw [q₂, hfw]; exact hW
  have hsf : IsSeparated (fst Z₁ Z₂).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  have hsq : IsSeparated q := MorphismProperty.of_isPullback (P := @IsSeparated) hq hsf
  have hiq : i ≫ q = 𝟙 Y := by
    refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, q₁, ← Category.assoc, i₁, e₁, Category.id_comp]
    · rw [Category.assoc, q₂, i₂, Category.id_comp]
  have hci : IsClosedImmersion i := by
    have : IsClosedImmersion (i ≫ q) := by rw [hiq]; infer_instance
    exact IsClosedImmersion.of_comp i q
  have hN : ((M₃.pull π).pull i).IsLB := pull_isLB r'.1 i
  have hc : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ₁ × σ₂ → T),
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y v ↔
        SecCoord (M₃.pull π) th' (y ≫ i) v := fun T _ y v => GlobalTheory.ZM.RepBC.secCoord_pull _ th' i y v
  have rY := GlobalTheory.ZM.ClosedCoord.projRep_closed K _ _ Wd Y s' _ th' i _ _ r' hci hN hc
  have H : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ →
      SecCoord M₂ th₂ (y ≫ a₂) v₂ →
      SecCoord ((M₃.pull π).pull i) (fun j => GlobalTheory.ZM.RepBC.secPull _ i (th' j)) y (fun i => v₁ i.1 * v₂ i.2) := by
    intro T _ y v₁ v₂ h₁ h₂
    rw [hc, hbc, Category.assoc, i₁]
    refine hseg T _ v₁ v₂ ?_ ?_
    · rwa [Category.assoc, e₁]
    · rwa [Category.assoc, e₂]
  rw [i₂, idealOf_eq_graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂ _ _ r₁.1 r₂.1 hN H] at rY
  exact ⟨_, _, rY, H⟩

end GlobalTheory.ZM.GraphSegre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleDiagonalBiadditiveOfE8Form
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PowerForm

theorem diag_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (h : IsE8 W) (u : Fin 8) : 0 < W u u := by
  have h₁ := h.1.diag_pos (i := u)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_pos] at h₁
  omega

theorem sum_single {G M : Type*} [Group G] [AddCommGroup M] (B : G → G → M)
    (h₁ : ∀ x x' y, B (x * x') y = B x y + B x' y) (h₂ : ∀ x x' y, B y (x * x') = B y x + B y x')
    (W : Matrix (Fin 8) (Fin 8) ℤ) (x : G) :
    ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • B (if uv.1 = 0 then x else 1) (if uv.2 = 0 then x else 1) =
      W 0 0 • B x x := by
  have z₁ : ∀ y, B 1 y = 0 := fun y => by simpa using h₁ 1 1 y
  have z₂ : ∀ y, B y 1 = 0 := fun y => by simpa using h₂ 1 1 y
  rw [Finset.sum_eq_single (0, 0) (fun b _ hb => ?_) (by simp)]
  · simp
  · by_cases a₁ : b.1 = 0
    · have a₂ : b.2 ≠ 0 := fun a₂ => hb (Prod.ext a₁ a₂)
      rw [if_neg a₂, z₂, smul_zero]
    · rw [if_neg a₁, z₁, smul_zero]


#check GlobalTheory.CechPic.cls_linComb_add
#check GlobalTheory.CechPic.cls_linComb_single
#check GlobalTheory.CechPic.cls_pull
#check GlobalTheory.CechPic.pull_id
#check GlobalTheory.CechPic.pull_comp
open GlobalTheory.CechPic in
theorem relAmple_diag : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) [IsLocallyNoetherian S] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.RelAmple G L → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  intro W S _ G A _ _ _ _ pr L P hW hG hA _ hpr hL hP hbi hiso hamp
  obtain ⟨j, hj, -⟩ := hpr A fun v => if v = 0 then 𝟙 A else 1
  have := hG.proper
  have hcl : IsClosedImmersion j.left := GlobalTheory.Retract.isClosedImmersion_section (r := (pr 0).left)
    (by rw [← Over.comp_left, hj, if_pos rfl, Over.id_left]) (Over.w (pr 0))
  have hpos := diag_pos hW 0
  have hn : 0 < (W 0 0).toNat := by omega
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := LB.isLB_pull hP _
  have hfin : IsFinite (𝟙 A : A ⟶ A).left := by rw [Over.id_left]; infer_instance
  have c₁ := (relAmple_finite_pow_iso S A G j L 1 one_pos hA hG hL inferInstance).1 hamp
  refine (relAmple_finite_pow_iso S A A (𝟙 A) _ _ hn hA hA hD hfin).2.1.1
    ((relAmple_finite_pow_iso S A A (𝟙 A) _ 1 one_pos hA hA (LB.isLB_pull hL _) hfin).2.2.2 _
      (LB.isLB_linComb hD _ _) ?_ c₁)
  refine (cls_eq_iff (LB.isLB_pull hL _) (LB.isLB_linComb hD _ _)).1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_linComb hD, Fintype.sum_unique, pull_id, cls_pull hL, (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hiso, cls_linComb hP, map_sum,
    cls_pull hP, Int.toNat_of_nonneg hpos.le]
  refine Eq.trans (Finset.sum_congr rfl fun uv _ => ?_)
    (sum_single (G := A ⟶ A) (fun a b => pull (lift a b).left (cls P hP)) (fun a a' b => ?_) (fun a a' b => ?_)
      W (𝟙 A))
  · rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hj, hj]
  · have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi A a a' b).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi A a a' b).2
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel

end GlobalTheory.PowerForm
end
end

