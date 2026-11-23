module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupport

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GoodReductionAdaptedBasis
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.RedGood

theorem wt_lin {k : Type} [Field k] (Φ : FibPre k) {d : ℕ} {J : Type} [Fintype J]
    {F : J → (Φ.H d).Sec} {a : J → k} {φ : (Φ.H d).Sec} (h : IsLin Φ.G.hom F a φ) (α : Φ.E.X)
    (l : Φ.N₀.ι) : Φ.wt φ α l = ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l := by
  rw [← WtLin.weight_sum Φ F a α l, ← h l]
  rfl

theorem constFn_zero {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) :
    constFn f U 0 = 0 := by
  simp only [constFn, map_zero]

theorem good_of_parts {k : Type} [Field k] (Φ : FibPre k) (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ)
    {J : Type} [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (R : J → Φ.E.X → (Φ.H 1).Sec)
    (pos : Filter.Tendsto q Filter.cofinite Filter.atTop) (short : ∀ i, Short q N (cls i))
    (uniq : ∀ i i', (∃ m, cls i = cls i' + N • m) → cls i = cls i')
    (cover : ∀ α, ∃ i m, α = cls i + N • m)
    (part : ∀ i α, Φ.IsPart α (F i) (R i α))
    (zero : ∀ i α, ¬ (Short q N α ∧ ∃ m, α = cls i + N • m) → ∀ l, Φ.wt (R i α) α l = 0)
    (basis : ∀ i₀ α, Short q N α → (∃ m, α = cls i₀ + N • m) → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ →
      ∃! a : {i // cls i = cls i₀} → k, IsLin Φ.G.hom (fun i : {i // cls i = cls i₀} => R i α) a φ) :
    Φ.Good N q cls F := by
  have hcls : ∀ i₀ i α, (∃ m, α = cls i₀ + N • m) → (∃ m, α = cls i + N • m) → cls i = cls i₀ := by
    rintro i₀ i α ⟨m, hm⟩ ⟨m', hm'⟩
    refine uniq i i₀ ⟨m - m', ?_⟩
    rw [smul_sub, ← add_sub_assoc, ← hm, hm', add_sub_cancel_right]
  have hsum : ∀ (i₀ : J) (α : Φ.E.X) (a : J → k), (∀ i, a i ≠ 0 → cls i = cls i₀) → ∀ l,
      ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l =
        ∑ i : {i // cls i = cls i₀}, constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l := by
    intro i₀ α a ha l
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => cls i = cls i₀) (by simp)
      (fun i => constFn Φ.E.B.hom _ (a i) * Φ.wt (R i α) α l), Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [(part i α).2 l]
    · have : a i = 0 := by
        by_contra h
        exact hi (ha i h)
      rw [this, constFn_zero, zero_mul]
  refine ⟨pos, short, ?_, ?_, ?_⟩
  · rintro i β ⟨l, hl⟩
    by_contra h
    exact hl (((part i β).2 l).symm.trans (zero i β h l))
  · intro α hα φ hφ
    obtain ⟨i₀, hm⟩ := cover α
    obtain ⟨a, ha, -⟩ := basis i₀ α hα hm φ hφ
    have key : ∀ i, (if h : cls i = cls i₀ then a ⟨i, h⟩ else 0) ≠ 0 → cls i = cls i₀ := by
      intro i hi
      by_contra h
      exact hi (dif_neg h)
    refine ⟨fun i => if h : cls i = cls i₀ then a ⟨i, h⟩ else 0, fun i hi => ?_, fun l => ?_⟩
    · rw [key i hi]
      exact hm
    · rw [hsum i₀ α _ key l, wt_lin Φ ha α l]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dite_eq_left i.2]
  · intro α hα a ha h0
    obtain ⟨i₀, hm⟩ := cover α
    have key : ∀ i, a i ≠ 0 → cls i = cls i₀ := fun i hi => hcls i₀ i α hm (ha i hi)
    have hl := (GlobalTheory.SecRatio.ratio_and_lin _ _ (Φ.H_isLB 1)).2 k Φ.G.hom {i // cls i = cls i₀}
      (fun i => R i α)
    obtain ⟨φ, hφ, -⟩ := hl (fun i => a i)
    obtain ⟨φ₀, hφ₀, -⟩ := hl 0
    have hz₀ : ∀ β l, Φ.wt φ₀ β l = 0 := fun β l => by
      rw [wt_lin Φ hφ₀ β l]
      exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, constFn_zero, zero_mul]
    have hz : ∀ β l, Φ.wt φ β l = 0 := fun β l => by
      rw [wt_lin Φ hφ β l]
      by_cases hβ : β = α
      · subst hβ
        rw [← hsum i₀ β a key l, h0 l]
      · refine Finset.sum_eq_zero fun i _ => ?_
        have : Φ.wt (R i α) β l = 0 := by
          by_contra h
          exact hβ ((part i α).1 ⟨l, h⟩)
        rw [this, mul_zero]
    have e : φ = φ₀ := WtPart.sec_ext Φ φ φ₀ fun β l => (hz β l).trans (hz₀ β l).symm
    subst e
    have hu := (basis i₀ α hα hm φ (by rintro β ⟨l, hl⟩; exact absurd (hz β l) hl)).unique hφ hφ₀
    funext i
    by_contra h
    exact h (congrFun hu ⟨i, key i h⟩)

theorem residue_j_eq_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) {a : u.V}
    (ha : a ∈ IsLocalRing.maximalIdeal u.V) : IsLocalRing.residue (OO p) (u.j a) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a) *
      (b : PadicAlgCl p) = 1 := congrArg Subtype.val hb
  have h0 : algebraMap u.V (FractionRing u.V) a ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hb'
    exact zero_ne_one hb'
  have hn : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) a)⁻¹‖ ≤ 1 := by
    rw [map_inv₀, ← eq_inv_of_mul_eq_one_right hb']
    exact (mem_OO_iff _).1 b.2
  obtain ⟨c, hc⟩ := (u.norm_le _).1 hn
  refine ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_))
  rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]

theorem good_reduction : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (N : ℕ) (fb : u.FibOf N), 1 ≤ N → ∀ (J : Type) [Fintype J] (σ : J → (u.H N).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB N α), u.Basis l N σ cls f → ∀ F : J → (fb.Φ.H 1).Sec, (∀ i α, fb.Φ.IsPart (fb.xe.symm α) (F i) (fb.red α (f i α))) → fb.Φ.Good N (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) (fun i => fb.xe.symm (cls i)) F := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l N fb hN J _ σ cls f hB F hF
  have hsh := _root_.GlobalTheory.ZH.Shift.main hL o Ω S ρ p y₀ u l N hN J σ cls f hB
  obtain ⟨hshort, huniq, hcover, -, -, hzero, -⟩ := hB
  have hS : ∀ α : fb.Φ.E.X, Short (l.q.comp fb.xe.toIntLinearEquiv.toLinearMap) N α ↔ Short l.q N (fb.xe α) := by
    intro α
    constructor
    · intro h m
      simpa using h (fb.xe.symm m)
    · intro h m
      simpa using h (fb.xe m)
  have hC : ∀ (α : fb.Φ.E.X) (c : u.D.toPre.X),
      (∃ m, α = fb.xe.symm c + N • m) ↔ ∃ m, fb.xe α = c + N • m := by
    intro α c
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨fb.xe m, by simp⟩
    · rintro ⟨m, hm⟩
      exact ⟨fb.xe.symm m, fb.xe.injective (by simp [hm])⟩
  refine good_of_parts fb.Φ N _ _ F (fun i α => fb.red (fb.xe α) (f i (fb.xe α))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact l.pos.comp fb.xe.injective.tendsto_cofinite
  · intro i
    rw [hS, fb.xe.apply_symm_apply]
    exact hshort i
  · intro i i' h
    rw [hC, fb.xe.apply_symm_apply] at h
    rw [huniq i i' h]
  · intro α
    obtain ⟨i, h⟩ := hcover (fb.xe α)
    exact ⟨i, (hC _ _).2 h⟩
  · intro i α
    have := hF i (fb.xe α)
    rwa [fb.xe.symm_apply_apply] at this
  · intro i α h j
    rw [hS, hC] at h
    by_cases hc : ∃ m, fb.xe α = cls i + N • m
    · obtain ⟨a, β, ha, hβ⟩ := (hsh i _ hc).2 fun hs => h ⟨hs, hc⟩
      have := fb.lin _ Unit (fun _ => β) (fun _ => a) (f i (fb.xe α)) (fun j => by
        rw [hβ j, Fintype.sum_unique])
      rw [wt_lin fb.Φ this α j, Fintype.sum_unique, residue_j_eq_zero u ha, constFn_zero, zero_mul]
    · have := fb.lin _ Empty Empty.elim Empty.elim (f i (fb.xe α)) (fun j => by
        rw [hzero i _ (fun m e => hc ⟨m, e⟩) j, Fintype.sum_empty])
      rw [wt_lin fb.Φ this α j, Fintype.sum_empty]
  · intro i₀ α hα hc φ hφ
    rw [hS] at hα
    rw [hC] at hc
    have hb := fb.basis _ _ _ ((hsh i₀ _ hc).1 hα) φ (by rwa [fb.xe.symm_apply_apply])
    let e : {i // cls i = cls i₀} ≃ {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} :=
      Equiv.subtypeEquivRight fun i => fb.xe.symm.injective.eq_iff.symm
    have hlin : ∀ a : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} → kb p,
        IsLin fb.Φ.G.hom (fun i : {i // fb.xe.symm (cls i) = fb.xe.symm (cls i₀)} =>
          fb.red (fb.xe α) (f i (fb.xe α))) a φ ↔
        IsLin fb.Φ.G.hom (fun i : {i // cls i = cls i₀} => fb.red (fb.xe α) (f i (fb.xe α))) (a ∘ e) φ := by
      intro a
      refine forall_congr' fun j => ?_
      rw [← e.sum_comp]
      rfl
    obtain ⟨a, ha, hu⟩ := hb
    refine ⟨a ∘ e.symm, (hlin _).2 ?_, fun b hb => ?_⟩
    · have : (a ∘ e.symm) ∘ e = a := by
        funext i
        simp
      rw [this]
      exact ha
    · rw [← hu _ ((hlin b).1 hb)]
      funext i
      simp

end GlobalTheory.ZH.RedGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFiniteKerOfSurjPointsSameDimension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private theorem isFinite_pullback_unit_of_surjective_on_points (k : Type) [Field k] [IsAlgClosed k]
    (G G' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ) (hG : _root_.GlobalTheory.SS.SmConn G)
    (hG' : _root_.GlobalTheory.SS.SmConn G') (hgG : SmoothOfRelativeDimension g G.hom)
    (hgG' : SmoothOfRelativeDimension g G'.hom) (i : G ⟶ G') [IsMonHom i]
    (hpts : ∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ i = y) :
    IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  unfold _root_.GlobalTheory.SS.SmConn at hG hG'
  obtain ⟨-, hsm, hsep, hqc, hgc⟩ := hG
  obtain ⟨-, hsm', hsep', hqc', hgc'⟩ := hG'
  have hw : i.left ≫ G'.hom = G.hom := Over.w i
  have : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  have : ConnectedSpace G'.left := GeometricallyConnected.connectedSpace_of_subsingleton G'.hom
  have : IsIntegral G.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G.hom
  have : IsIntegral G'.left := _root_.GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace (K := k) G'.hom
  have : LocallyOfFiniteType (i.left ≫ G'.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType i.left := locallyOfFiniteType_of_comp i.left G'.hom
  have : JacobsonSpace G'.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) G'.hom
  have hcl : closedPoints G'.left ⊆ Set.range i.left := by
    intro y hy
    obtain ⟨x, hx⟩ := hpts (Over.homMk (pointOfClosedPoint (K := k) G'.hom y hy)
      (pointOfClosedPoint_comp _ _ _))
    refine ⟨x.left (IsLocalRing.closedPoint k), ?_⟩
    have h := congrArg (fun φ : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G' => φ.left (IsLocalRing.closedPoint k)) hx
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    exact h.trans (pointOfClosedPoint_apply _ _ _ _)
  have hgen : i.left (genericPoint G.left) = genericPoint G'.left := by
    have hη : closure {genericPoint G.left} = Set.univ := genericPoint_spec G.left
    have h1 : closure (Set.range i.left) = Set.univ :=
      Set.eq_univ_of_univ_subset (closure_closedPoints (X := G'.left) ▸ closure_mono hcl)
    have h2 : Set.range i.left ⊆ closure {i.left (genericPoint G.left)} := by
      rintro _ ⟨x, rfl⟩
      exact map_mem_closure i.left.continuous (hη ▸ Set.mem_univ x) (by simp)
    have h3 : IsGenericPoint (i.left (genericPoint G.left)) Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← h1]
      simpa using closure_mono h2
    exact h3.eq (genericPoint_spec G'.left)
  have hq : i.left.QuasiFiniteAt (genericPoint G.left) := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    have hfib : ∀ a : i.left.fiber (i.left (genericPoint G.left)),
        i.left.fiberι _ a = genericPoint G.left := by
      intro a
      have ha : i.left.fiberι _ a ∈ i.left ⁻¹' {i.left (genericPoint G.left)} := by
        rw [← Scheme.Hom.range_fiberι]; exact Set.mem_range_self a
      refine _root_.GlobalTheory.OntoFinite.eq_genericPoint (K := k) G'.hom i.left g (by rw [hw]; exact hgG)
        hgG' _ ?_
      rw [← hgen]; exact ha
    have : Subsingleton (i.left.fiber (i.left (genericPoint G.left))) :=
      ⟨fun a b => (i.left.fiberι _).isEmbedding.injective ((hfib a).trans (hfib b).symm)⟩
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun b => Subsingleton.elim b _
  have : LocallyQuasiFinite i.left :=
    _root_.GlobalTheory.OntoFinite.locallyQuasiFinite_of_quasiFiniteAt (K := k) i _ hq
  have hpb : IsPullback (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left
      (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left i.left (η[G'] : 𝟙_ _ ⟶ G').left :=
    IsPullback.map (Over.forget _) (IsPullback.of_hasPullback _ _)
  have : LocallyQuasiFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb ‹_›
  have hsec : (η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion ((η[G'] : 𝟙_ _ ⟶ G').left ≫ G'.hom) := by rw [hsec]; infer_instance
  have : IsClosedImmersion (η[G'] : 𝟙_ _ ⟶ G').left := IsClosedImmersion.of_comp _ G'.hom
  have : IsClosedImmersion (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left :=
    MorphismProperty.of_isPullback hpb.flip ‹_›
  have hw2 : (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ 𝟙 _ =
      (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom := by
    exact (Over.w (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G'))).trans
      (Over.w (pullback.fst i (η[G'] : 𝟙_ _ ⟶ G'))).symm
  have : QuasiCompact (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
    have h2 : QuasiCompact ((pullback.fst i (η[G'] : 𝟙_ _ ⟶ G')).left ≫ G.hom) := inferInstance
    rw [← hw2, Category.comp_id] at h2
    exact h2
  have : IsLocallyArtinian (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left :=
    inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of k)))
  exact IsFinite.of_locallyQuasiFinite _


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.isFinite_ker_of_surjective_points_of_dim_eq : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (G G' : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G] [GrpObj G'] (g : ℕ), _root_.GlobalTheory.SS.SmConn G →
    _root_.GlobalTheory.SS.SmConn G' → SmoothOfRelativeDimension g G.hom →
    SmoothOfRelativeDimension g G'.hom → ∀ i : G ⟶ G', IsMonHom i →
    (∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G'), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ i = y) →
    IsFinite (pullback.snd i (η[G'] : 𝟙_ _ ⟶ G')).left := by
  intro k _ _ G G' _ _ g hG hG' hgG hgG' i _ hpts
  exact isFinite_pullback_unit_of_surjective_on_points k G G' g hG hG' hgG hgG' i hpts

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyClosureExtensionAbelianScheme
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClosureLifting

theorem exists_lift {Z Y : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (j : Y ⟶ Z) [IsOpenImmersion j] [Nonempty Y] :
    ∃ x : Sp K ⟶ Y, x ≫ j = gp := by
  have hr : Set.range gp ⊆ Set.range j := by
    rw [hgp, Set.singleton_subset_iff]
    exact (genericPoint_specializes (j (Classical.arbitrary Y))).mem_open
      j.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
  exact ⟨_, IsOpenImmersion.lift_fac j gp hr⟩

theorem flat_of_charZero {Z : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] [CharZero K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (π : Z ⟶ Sp ℤ) : Flat π := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (P := @Flat) Z.affineOpenCover.openCover fun i => ?_
  let R := Z.affineOpenCover.X i
  let j : Spec R ⟶ Z := Z.affineOpenCover.f i
  have : IsOpenImmersion j := Z.affineOpenCover.map_prop i
  change Flat (j ≫ π)
  rcases isEmpty_or_nonempty (Spec R) with h | h
  · infer_instance
  obtain ⟨x, -⟩ := exists_lift gp hgp j
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion j
  have : IsDomain R := (affine_isIntegral_iff R).1 this
  have : CharZero R := (Spec.preimage x).hom.charZero
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Flat)]
  have e : φ.hom = algebraMap ℤ R := RingHom.ext_int _ _
  rw [e, RingHom.flat_algebraMap_iff]
  infer_instance

theorem exists_section_of_local {Z G : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] (gp : Sp K ⟶ Z)
    (hgp : Set.range gp = {genericPoint Z}) (q : G ⟶ Z) [IsSeparated q] (ξ : Sp K ⟶ G)
    (H : ∀ z : Z, ∃ (W : Z.Opens) (h : W.toScheme ⟶ G), z ∈ W ∧ h ≫ q = W.ι ∧
      ∀ x : Sp K ⟶ W.toScheme, x ≫ W.ι = gp → x ≫ h = ξ) :
    ∃ e : Z ⟶ G, e ≫ q = 𝟙 Z ∧ gp ≫ e = ξ := by
  choose W h hz hq hξ using H
  have hd : IsDominant gp := ⟨by
    rw [DenseRange, hgp, dense_iff_closure_eq]
    exact genericPoint_spec Z⟩
  have hx : ∀ z, ∃ x : Sp K ⟶ (W z).toScheme, x ≫ (W z).ι = gp := fun z =>
    have : Nonempty (W z).toScheme := ⟨⟨z, hz z⟩⟩
    exists_lift gp hgp _
  choose x hx using hx
  have hW : TopologicalSpace.IsOpenCover W :=
    top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hz z⟩
  let 𝒰 := Z.openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ h a = pullback.snd (W a).ι (W b).ι ≫ h b := by
    intro a b
    let m : Sp K ⟶ pullback (W a).ι (W b).ι := pullback.lift (x a) (x b) ((hx a).trans (hx b).symm)
    have e : m ≫ pullback.fst _ _ ≫ (W a).ι = gp := by rw [pullback.lift_fst_assoc, hx]
    have : IsDominant (m ≫ pullback.fst _ _ ≫ (W a).ι) := e ▸ hd
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ (W a).ι)
    have : IsReduced (pullback (W a).ι (W b).ι) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine ext_of_isDominant_of_isSeparated q ?_ m ?_
    · rw [Category.assoc, Category.assoc, hq, hq, pullback.condition]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hξ _ _ (hx a), hξ _ _ (hx b)]
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms h hc = h a := fun a => 𝒰.ι_glueMorphisms h hc a
  refine ⟨𝒰.glueMorphisms h hc, 𝒰.hom_ext _ _ fun (a : Z) => ?_, ?_⟩
  · change (W a).ι ≫ _ = (W a).ι ≫ _
    rw [← Category.assoc, he, hq, Category.comp_id]
  · rw [← hx (genericPoint Z), Category.assoc, he, hξ _ _ (hx _)]

theorem eSec_fst {B B' : Scheme.{0}} (u : B' ⟶ B) (A : Over B) [GrpObj A] :
    eSec ((Over.pullback u).obj A) ≫ pullback.fst A.hom u = u ≫ eSec A := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem proj_zero_of_eq_bot {T : AddSubgroup S.Gam} (h : T = ⊥) : S.proj T 0 = 1 := by
  subst h
  unfold ThetaSys.proj
  rw [finsum_unique, S.ρ_one _ (by rw [AddSubgroup.mem_bot.1 (Subtype.prop _), smul_zero])]
  simp

theorem exists_crd_ne_zero [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (ρ : S.Real) {K : Type} [Field K]
    (y : Sp K ⟶ ρ.P.A.left) : ∃ v i, ρ.Crd y v ∧ v i ≠ 0 := by
  let y' : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    pullback.lift (f := (baseOver (Sp S.R)).hom) (g := ρ.P.A.hom) (y ≫ ρ.P.A.hom) y (Category.comp_id _)
  have hM : (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).IsLB := LB.isLB_linComb ρ.P.isLB _ _
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists hM ρ.s y'
  have hm : y' (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (ρ.s i) := by
    rw [(ThetaSys.Real.immBy_basis hL o Ω S ρ).1]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, -, hi⟩ := hm
  exact ⟨v, i, ⟨y', pullback.lift_snd _ _ _, hv⟩,
    ((CrdCalc.crd_isUnit_iff i hv).2 ((CrdCalc.top_le_iff y' _).2 hi)).ne_zero⟩

variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem range_subset [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) :
    Set.range Q.a₀ ⊆ Set.range Q.G.ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨K, _, x, rfl⟩ : ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ pullback ρ.P.A.hom Q.u₀),
      x (IsLocalRing.closedPoint K) = w :=
    ⟨_, inferInstance, Scheme.fromSpecResidueField _ w, Scheme.fromSpecResidueField_apply w _⟩
  obtain ⟨v, i, hv, hi⟩ := exists_crd_ne_zero hL ρ (x ≫ pullback.fst _ _)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((x ≫ Q.a₀) ≫ Q.P.hom ≫ M.s)
  have hz : ∀ s, ((x ≫ Q.a₀) ≫ Q.P.hom) s ∈ U₀ := fun s => by
    rw [Category.assoc, Q.cart.w, ← Category.assoc]
    exact ((x ≫ pullback.snd _ _) s).2
  have key := (OpenPart.le_preimage_G_iff o Ω S ρ M U₀ EE hB Q K (x ≫ Q.a₀) _ ψ.hom v
    Set.range_unique (Or.inr (hz _)) hψ.symm (Q.crd K x v hv)).2 ⟨i, by
      rw [proj_zero_of_eq_bot (hB.gen _ (hz _)),
        Finset.sum_eq_single i (fun j _ hj => by rw [Matrix.one_apply_ne hj, map_zero, zero_mul]) (by simp)]
      simpa using hi⟩
  exact key (Set.mem_univ (IsLocalRing.closedPoint K))

theorem nonempty_ext : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), Nonempty Q.Ext := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q
  have := ArithBase.char (o := o) (Ω := Ω)
  have := M.sep
  have := M.lft
  have := M.qc
  have := Q.proper
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 (ArithBase.ft (o := o) (Ω := Ω)))
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have h1 : (ρ.pt 0).left = eSec ρ.P.A := by
    have e : toUnit (baseOver (Sp S.R)) = 𝟙 (𝟙_ (Over (Sp S.R))) := toUnit_unique _ _
    rw [h0, Hom.one_def, e]
    exact congrArg CommaMorphism.left (Category.id_comp _)
  let a : pullback ρ.P.A.hom Q.u₀ ⟶ Q.G.toScheme := IsOpenImmersion.lift Q.G.ι Q.a₀ (range_subset hL hB Q)
  have ha : a ≫ Q.G.ι = Q.a₀ := IsOpenImmersion.lift_fac _ _ _
  let ε : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ := eSec ((Over.pullback Q.u₀).obj ρ.P.A)
  have hε₁ : ε ≫ pullback.fst _ _ = Q.u₀ ≫ eSec ρ.P.A := eSec_fst Q.u₀ ρ.P.A
  have hε₂ : ε ≫ pullback.snd _ _ = 𝟙 _ := Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]
  have : Nonempty U₀.toScheme := hB.ov.ne.to_subtype
  obtain ⟨t, ht⟩ := exists_lift M.pt M.gen U₀.ι
  obtain ⟨e, he, he'⟩ := exists_section_of_local M.pt M.gen (Q.G.ι ≫ Q.P.hom) (t ≫ ε ≫ a) fun z => by
    obtain ⟨W, h, hz, hh, H⟩ := _root_.GlobalTheory.ZH.TorsionSection.exists_section hL o Ω S ρ M U₀ EE hB Q z 0 (zero_mem _)
    refine ⟨W, h, hz, hh, fun x hx => ?_⟩
    rw [← cancel_mono Q.G.ι, Category.assoc, H Ω x (t ≫ ε) ?_ ?_]
    · simp only [Category.assoc, ha]
    · rw [Category.assoc, reassoc_of% hε₂, hx, ht]
    · rw [Category.assoc, Category.assoc, reassoc_of% hε₂, hε₁, h1]
  have : IsDominant (t ≫ U₀.ι) := ht ▸ M.isDominant_pt
  have : IsDominant t := .of_comp_of_isOpenImmersion t U₀.ι
  refine ⟨{
    π := M.s ≫ spMap (algebraMap ℤ o)
    flat := flat_of_charZero M.pt M.gen _
    lft := inferInstance
    qc := inferInstance
    sep := inferInstance
    normal := hB.ov.normal
    ne := hB.ov.ne
    ab := TLinPf.isAb_pullback _ _ ρ.P.isAb
    dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      (ρ.g_eq ▸ ρ.P.smoothDim)
    a := a
    a_eq := ha
    e := e
    e_sec := he
    e_zero := ?_ }⟩
  change U₀.ι ≫ e = ε ≫ a
  refine ext_of_isDominant_of_isSeparated (Q.G.ι ≫ Q.P.hom) ?_ t ?_
  · rw [Category.assoc, he, Category.assoc, reassoc_of% ha, Q.cart.w, reassoc_of% hε₂, Category.comp_id]
  · rw [← Category.assoc, ht, he']

end GlobalTheory.ZH.ClosureLifting
end
end

