module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleFramesIff
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FrameCompare
open GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections (PowSec)

variable {S : Scheme.{0}} (G : Over S)

variable [GrpObj G] [IsCommMonObj G] (L : RigLB G) (N : ℕ)


omit [GrpObj G] [IsCommMonObj G] in
theorem relAmple_iff {O : Type} [CommRing O] (b : S ⟶ Sp O) {A : LB S} (hA : A.IsLB) :
    (Out.RelAmple (Over.mk b) A →
      ∀ z : S, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ z ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s)) ∧
    (IsProper b → (∀ z : S, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ z ∈ Out.nonzeroLocus s ∧
      IsAffineOpen (Out.nonzeroLocus s)) → Out.RelAmple (Over.mk b) A) := by
  constructor
  · intro h z
    obtain ⟨n, hn, s, hs⟩ := (isAmpleLB_of_relAmple_of_isAffine (Over.mk b) hA h).exists_affine z
    obtain ⟨s', e, -⟩ := exists_sec_oneTerm A (K' := Fin 1) (e' := (n : ℤ)) rfl s
    exact ⟨n, s', hn, by rw [← e] at hs; exact hs⟩
  · intro hb h
    have : IsProper (Over.mk b).hom := hb
    have hc : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace b
    have ha : IsAmpleLB A := ⟨hA, hc, fun z => by
      obtain ⟨n, s, hn, hs⟩ := h z
      obtain ⟨s', e, -⟩ := exists_sec_oneTerm A (K' := PUnit) (e' := (n : ℤ)) rfl s
      exact ⟨n, hn, s', by rw [← e] at hs; exact hs⟩⟩
    refine relAmple_of_isAmpleLB (Over.mk b) hA fun U hU => ?_
    have : CompactSpace (b ⁻¹ᵁ U).toScheme :=
      isCompact_iff_compactSpace.1 (QuasiCompact.isCompact_preimage (f := b) _ U.isOpen hU.isCompact)
    exact ha.pull_of_isOpenImmersion (b ⁻¹ᵁ U).ι

end GlobalTheory.FrameCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsDominantPullbackFstOfFlatOfInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isDominant_pullback_fst_of_flat_of_injective {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (hβ : Function.Injective β) {X : Scheme.{0}} (s : X ⟶ Sp O) [Flat s] :
    IsDominant (pullback.fst s (spMap β)) := by
  constructor
  intro x
  have hη : (spMap β) (IsLocalRing.closedPoint F) ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := O)
      (PrimeSpectrum.comap β (IsLocalRing.closedPoint F)) (s x)).mp ?_
    intro a ha
    have ha' : β a ∈ IsLocalRing.maximalIdeal F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha'
    have : a = 0 := hβ (by rw [ha', map_zero])
    rw [this]; exact Ideal.zero_mem _
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap s hη
  refine closure_mono (Set.singleton_subset_iff.mpr ?_) hy.mem_closure
  rw [Scheme.Pullback.range_fst]
  exact ⟨_, hy'.symm⟩

theorem isPrimitiveRoot_map_of_isUnit {O k : Type} [CommRing O] [IsDomain O] [Field k] (ψ : O →+* k)
    {z : O} {A : ℕ} (hA : 0 < A) (hz : IsPrimitiveRoot z A) (hu : IsUnit (A : O)) :
    IsPrimitiveRoot (ψ z) A := by
  have : NeZero (A : k) := ⟨by simpa using (hu.map ψ).ne_zero⟩
  rw [← (Polynomial.isRoot_cyclotomic_iff (R := k) (n := A)), ← Polynomial.map_cyclotomic A ψ]
  exact Polynomial.IsRoot.map ψ (hz.isRoot_cyclotomic hA)

theorem galoisPart_eq_refl_of_fixes_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (S : ℕ) (β : RZ H S l.A →+* KA l) (C : Cpt Xo.s Xo.univ.t β) (r : Xo.X ≅ Xo.X) (ρ : C.X ≅ C.X) (σ : KA l ≃+* KA l), IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → 0 < S → (∃ e, l.A ∣ S ^ e) → C.j ≫ ρ.hom = r.hom ≫ C.j → σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ Xo.s = Xo.s ≫ spMap σ.toRingHom → ∀ (k : Type) [Field k] (x : Sp k ⟶ C.X), x ≫ ρ.hom = x → σ = RingEquiv.refl _ := by
  intro E _ _ _ H D l Xo S β C r ρ σ hinc hS ⟨e, he⟩ hj hρ hr k _ x hx
  have hA := l.A_pos
  have : NeZero l.A := ⟨hA.ne'⟩
  have hβ : Function.Injective β := fun a b h => Subtype.ext (by
    have h1 := hinc a
    rw [h, hinc b] at h1
    exact h1.symm)
  let z : RZ H S l.A := ⟨zeta l.A, Subring.subset_closure (by simp)⟩
  let t : RZ H S l.A := ⟨(S : ℂ)⁻¹, Subring.subset_closure (by simp)⟩
  have hβz : β z = (baseKA l).ζ := Subtype.ext (hinc z)
  have hζ : IsPrimitiveRoot (baseKA l).ζ l.A := (baseKA l).ζ_prim
  have hz : IsPrimitiveRoot z l.A := IsPrimitiveRoot.of_map_of_injective (hβz ▸ hζ) hβ
  have hSu : IsUnit (S : RZ H S l.A) := IsUnit.of_mul_eq_one t (Subtype.ext (by
    have : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
    simp [t, this]))
  have hAu : IsUnit (l.A : RZ H S l.A) := by
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast he) ?_
    rw [Nat.cast_pow]
    exact hSu.pow e
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ (baseKA l).ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have := C.flat
  have hd₁ := isDominant_pullback_fst_of_flat_of_injective β hβ C.s
  have hd₂ : IsDominant C.jQ := ⟨C.jQ_dense⟩
  have hd : IsDominant C.j := by unfold Cpt.j; infer_instance
  have hred : IsReduced C.X := by
    have := fun y => (C.normal y).1
    exact isReduced_of_isReduced_stalk _
  have hjs : C.j ≫ C.s = Xo.s ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  let ev : RZ H S l.A → (Polynomial ℤ →+* RZ H S l.A) := fun y => (Polynomial.aeval y).toRingHom
  have hev : σ.toRingHom.comp (β.comp (ev z)) = β.comp (ev (z ^ a)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [ev, hβz, ha]
  have key : ρ.hom ≫ C.s ≫ spMap (ev z) = C.s ≫ spMap (ev (z ^ a)) := by
    refine ext_of_isDominant C.j ?_
    rw [reassoc_of% hj, reassoc_of% hjs, reassoc_of% hjs, reassoc_of% hr]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← hev]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ C.s)
  have key₂ : CommRingCat.ofHom (ev z) ≫ ψ = CommRingCat.ofHom (ev (z ^ a)) ≫ ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hψ, Category.assoc, Category.assoc, ← key, reassoc_of% hx]
  have key₃ : ψ.hom z = ψ.hom z ^ a := by
    have := congrArg (fun f => f.hom Polynomial.X) key₂
    simpa [ev] using this
  have hp : IsPrimitiveRoot (ψ.hom z) l.A := isPrimitiveRoot_map_of_isUnit ψ.hom hA hz hAu
  have hmod : a ≡ 1 [MOD l.A] := by
    have hfin : IsOfFinOrder (ψ.hom z) := hp.isOfFinOrder hA.ne'
    rw [hp.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one]
    exact key₃.symm
  have hσζ : σ (baseKA l).ζ = (baseKA l).ζ := by
    rw [← ha]
    have hfin : IsOfFinOrder (baseKA l).ζ := hζ.isOfFinOrder hA.ne'
    rw [hζ.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one] at hmod
    exact hmod
  have hfinal : σ.toRingHom.toRatAlgHom = AlgHom.id ℚ (KA l) := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := KA l) (s := {H.rt0, zeta l.A}) rfl ?_
    rintro y (rfl | rfl)
    · exact hρ
    · exact hσζ
  ext1 y
  exact DFunLike.congr_fun hfinal y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOfFinOrderOfQuadratic
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CMSpreadCompare

open GlobalTheory.PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Unif

theorem exists_pointEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {s : T.left ⟶ S} (hs : s = T.hom ≫ f) :
    ∃ p : (T ⟶ G') ≃* (Over.mk s ⟶ G), ∀ x, (p x).left = x.left ≫ φ := by
  subst hs
  exact ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun _ _ e => eq_of_comp_eq h.1 (congrArg (fun z => z.left) e), fun p =>
    ⟨Over.homMk (h.1.lift p.left T.hom (Over.w p)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩, fun _ => rfl⟩

theorem isHolTo_postcomp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  rw [show (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) from
    funext fun b => (valAt'_comp _ φ U s).symm]
  exact h (φ ⁻¹ᵁ U) _

variable {k : Type} [Field k] {κ : k →+* ℂ} {A : Over (Sp k)} [GrpObj A] {PC : Out.PolAV (Sp ℂ)}
  {ψ : PC.A.left ⟶ A.left} (hψ : IsGrpPullback PC.A A (spMap κ) ψ) (u : HolUnif PC.A PC.L PC.g)

include hψ

end Unif

section Quadratic

end Quadratic

section Transport

variable {D : Datum H} {R : Type} [CommRing R] {t : SAB H (Sp R)} {B B' : Over (Sp R)} [GrpObj B] [GrpObj B']
  {M : LB B.left} {M' : LB B'.left} {L : Submodule (𝓞 E) D.La} {ρ : R} {S S' : Set L} {φ : L → (B ⟶ t.G)}

end Transport

section Multiplication

end Multiplication

end GlobalTheory.CMSpreadCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverFiniteGroupQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isProjOver_of_isProper_of_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [IsProper s]
    {L : LB X} (hL : L.IsLB) {n : ℕ} (σ : Fin n → LB.Sec L) (ha : ∀ i, IsAffineOpen (Out.nonzeroLocus (σ i)))
    (hc : ⨆ i, Out.nonzeroLocus (σ i) = ⊤) : IsProjOver s := by
  have hA : IsAmpleLB L := by
    refine ⟨hL, ⟨?_⟩, ?_⟩
    · have hu : (Set.univ : Set X) = ⋃ i, (Out.nonzeroLocus (σ i) : Set X) := by
        rw [← TopologicalSpace.Opens.coe_iSup, hc]
        rfl
      rw [hu]
      exact isCompact_iUnion fun i => (ha i).isCompact
    · intro x
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hc] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      refine ⟨1, le_rfl, secToPow (σ i) 1, ?_, ?_⟩
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact hi
      · rw [nonzeroLocus_secToPow (σ i) le_rfl]
        exact ha i
  exact hA.isProjOver s

theorem isProjOver_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (s' : X' ⟶ Sp R), IsProjOver (π ≫ s') → IsProjOver s' := by
  intro Γ _ _ X X' ρ π hq R _ _ s' hX
  have hQ : IsAffineQuotient ρ π :=
    ⟨hq.2.1, hq.1, fun W => (hq.2.2 W).1, fun W f hf => (hq.2.2 W).2 f (by
      unfold IsInvariantSection at hf
      exact fun g _ => (hf g).2)⟩
  have hP : IsProper (π ≫ s') := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hX).1
  have hs' : IsProper s' := hQ.isProper s'
  have hXs : X.IsSeparated := by
    constructor
    rw [show terminal.from X = (π ≫ s') ≫ terminal.from (Sp R) from terminal.hom_ext _ _]
    infer_instance
  obtain ⟨L, n, σ, hL, ha, ho⟩ := exists_sections_orbit_subset_nonzeroLocus Γ R X (π ≫ s') ρ hX
  obtain ⟨L', n', σ', hL', ha', hc'⟩ :=
    QuotientNorm.exists_affine_cover_of_quotient Γ X X' ρ π hq hXs L n σ hL ha ho
  exact isProjOver_of_isProper_of_affine_cover s' hL' σ' ha' hc'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RelAmpleQProj

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out TopologicalSpace

variable {Y : Scheme.{0}} {L M G : LB Y}

def secPwOne (σ : G.Sec) : (pw G 1).Sec where
  f := σ.f
  compat i j := by
    have h := σ.compat i j
    rw [← zpow_one (G.g i j)] at h
    exact h

theorem exists_sec_tw_locus [CompactSpace Y] [QuasiSeparatedSpace Y] (hM : M.IsLB) (hG : G.IsLB) (σ : G.Sec)
    (V : Y.Opens) (hV : V = nonzeroLocus σ) (r : (M.pull V.ι).Sec) :
    ∃ (k : ℕ) (u : (tw M G (k : ℤ)).Sec), V.ι ⁻¹ᵁ nonzeroLocus u = nonzeroLocus r := by
  obtain ⟨s, ⟨hs, hr⟩, -⟩ := existsUnique_secOn_of_pull M V r
  obtain ⟨k, H⟩ := exists_tw_extend_pow_mul Y G M 1 (secPwOne σ) V 0 hG hM hV inferInstance inferInstance
    (SecOn.twZeroEquiv hM hG V (GlobalTheory.LB.mkSec s hs))
  rw [show (0 : ℤ) + k * 1 = k by ring] at H
  obtain ⟨a, ha⟩ := H
  let w : (tw M G (k : ℤ)).Sec := ⟨fun i => resG Y (le_inf le_top le_rfl) (GlobalTheory.LB.coord a i), fun i j => by
    change resG Y _ (resG Y _ _) = _ * resG Y _ (resG Y _ _)
    rw [resG_resG, resG_resG, GlobalTheory.LB.coord_rel a i j (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl, rs_self]⟩
  refine ⟨k, w, ?_⟩
  ext z
  obtain ⟨p, hp⟩ := exists_chart hM (V.ι z)
  obtain ⟨l, hl⟩ := exists_chart hG (V.ι z)
  have hzV : V.ι z ∈ V := z.2
  have hz : V.ι z ∈ V ⊓ (M.U p ⊓ G.U l) := ⟨hzV, hp, hl⟩
  have hz' : V.ι z ∈ M.U p ⊓ G.U l := ⟨hp, hl⟩
  have hzp : z ∈ (M.pull V.ι).U (fun _ => p) := mem_pull.2 hp
  have e := congrArg (gs V.ι z _) (ha p l)
  rw [SecOn.twCoord_twZeroEquiv, gs_res _ z _ hz, gs_mul _ z _ hz, gs_pow _ z _ hz, gs_res _ z _ hz] at e
  have e₁ : gs V.ι z _ ((w).f (p, l)) = gs V.ι z _ (SecOn.twCoord a p l) :=
    gs_res V.ι z _ hz' _
  have e₂ : gs (𝟙 _) z _ (r.f fun _ => p) = gs V.ι z _ (s p) := by
    rw [← hr, gs_appLE V.ι _ _ _ (𝟙 _) z hzp, Category.id_comp]
  have hσ : IsUnit (gs V.ι z (V ⊓ (M.U p ⊓ G.U l)) (rs Y (inf_le_right.trans inf_le_right) (σ.f l))) := by
    rw [gs_res _ z _ hz]
    exact (mem_nonzeroLocus_iff_pull σ V.ι z hl).1 (hV.le hzV)
  refine (mem_nonzeroLocus_iff_pull (w) V.ι z (k := (p, l)) hz').trans
    (Iff.trans ?_ (mem_nonzeroLocus_iff_isUnit r hzp).symm)
  rw [e₂]
  refine (iff_of_eq (congrArg IsUnit (e₁.trans e))).trans ?_
  rw [IsUnit.mul_iff]
  exact and_iff_right (hσ.pow k)

theorem exists_sec_pow_tw {m k c e : ℕ} (he : 1 ≤ e) (h : c * m = k + e) (u : (tw (lbPow L m) G (k : ℤ)).Sec)
    (σ : G.Sec) : ∃ w : (lbPow (tw L G (c : ℤ)) m).Sec, nonzeroLocus w = nonzeroLocus u ⊓ nonzeroLocus σ := by
  have le : ∀ J : PUnit → L.ι × G.ι, powChart (tw L G (c : ℤ)) J ≤
      powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2 := fun J y hy =>
    ⟨mem_powChart.2 (mem_powChart.1 hy).1, (mem_powChart.1 hy).2⟩
  let F : ∀ J : PUnit → L.ι × G.ι, Γ(Y, powChart (tw L G (c : ℤ)) J) := fun J =>
    resG Y (le J) (show Γ(Y, powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2) from
      u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
      resG Y ((le J).trans inf_le_right) (σ.f (J PUnit.unit).2) ^ e
  have hF : ∀ (y : Y) (J : PUnit → L.ι × G.ι), y ∈ powChart (tw L G (c : ℤ)) J → gs (𝟙 Y) y _ (F J) =
      gs (𝟙 Y) y _ (u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
        gs (𝟙 Y) y _ (σ.f (J PUnit.unit).2) ^ e := fun y J hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨powSecOfGerm (L := tw L G (c : ℤ)) m F fun y J J' hJ hJ' => ?_, ?_⟩
  · have e₁ := gs_compat u (𝟙 Y) y (j := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
      (j' := (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2)) (le J hJ) (le J' hJ')
    have e₂ := TwistGen.gm_tw_g (lbPow L m) G k y (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2) (le J hJ) (le J' hJ')
    have e₃ := gm_lbPow_g (L := L) m (𝟙 Y) y (fun _ => (J PUnit.unit).1) (fun _ => (J' PUnit.unit).1)
      (le J hJ).1 (le J' hJ').1
    have e₄ := TwistGen.gm_tw_g L G c y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.1 hJ) (mem_powChart.1 hJ')
    have e₅ := gs_compat σ (𝟙 Y) y (le J hJ).2 (le J' hJ').2
    dsimp only at e₂
    rw [e₃] at e₂
    refine (hF y J hJ).trans (Eq.trans ?_ (congrArg₂ (fun a b => a ^ m * b) e₄ (hF y J' hJ')).symm)
    rw [e₅]
    refine (congrArg (· * _) (e₁.trans (congrArg (· * _) e₂))).trans ?_
    simp only [Units.val_pow_eq_pow_val]
    rw [mul_pow, mul_pow, ← pow_mul, h]
    ring
  · refine nonzeroLocus_pow_eq_of _ _ (fun y hy => ?_) fun y J hJ => ?_
    · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
      exact ⟨fun _ => (p.1 PUnit.unit, p.2), mem_powChart.2 ⟨mem_powChart.1 hp.1, hp.2⟩⟩
    · refine (iff_of_eq (congrArg IsUnit (hF y J hJ))).trans ?_
      rw [IsUnit.mul_iff, isUnit_pow_iff (by omega)]
      exact and_congr (mem_nonzeroLocus_iff_isUnit u (k := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
        (le J hJ)).symm (mem_nonzeroLocus_iff_isUnit σ (le J hJ).2).symm

theorem exists_isAmpleLB_tw [CompactSpace Y] [QuasiSeparatedSpace Y] (hL : L.IsLB) (hG : G.IsLB)
    (h : ∀ y : Y, ∃ (σ : G.Sec) (V : Y.Opens), V = nonzeroLocus σ ∧ y ∈ V ∧ IsAmpleLB (L.pull V.ι)) :
    ∃ c : ℕ, IsAmpleLB (tw L G (c : ℤ)) := by
  have loc : ∀ y : Y, ∃ (m k : ℕ) (u : (tw (lbPow L m) G (k : ℤ)).Sec) (σ : G.Sec), 1 ≤ m ∧
      y ∈ nonzeroLocus u ⊓ nonzeroLocus σ ∧ IsAffineOpen (nonzeroLocus u ⊓ nonzeroLocus σ) := fun y => by
    obtain ⟨σ, V, hV, hy, hA⟩ := h y
    obtain ⟨m, hm, τ, hτ, ha⟩ := hA.exists_affine ⟨y, hy⟩
    obtain ⟨r, hr⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL m) V.ι)
      (isLB_lbPow hA.isLB m) (lbIso_lbPow_pull hL V.ι m).symm τ
    obtain ⟨k, u, hu⟩ := exists_sec_tw_locus (isLB_lbPow hL m) hG σ V hV r
    have e := hu.trans hr
    refine ⟨m, k, u, σ, hm, ⟨e.ge hτ, hV.le hy⟩, ?_⟩
    have h₁ := ha.image_of_isOpenImmersion V.ι
    rwa [← e, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm, hV] at h₁
  choose m k u σ hm hy ha using loc
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top (fun y => nonzeroLocus (u y) ⊓ nonzeroLocus (σ y)) hy
  refine ⟨T.sup k + 1, isLB_tw hL hG _, inferInstance, fun x => ?_⟩
  obtain ⟨y, hx⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ x))
  have h₁ : k y ≤ T.sup k := Finset.le_sup y.2
  have h₂ : T.sup k + 1 ≤ (T.sup k + 1) * m y := Nat.le_mul_of_pos_right _ (hm y)
  obtain ⟨w, hw⟩ := exists_sec_pow_tw (c := T.sup k + 1) (e := (T.sup k + 1) * m y - k y) (by omega) (by omega)
    (u y) (σ y)
  exact ⟨m y, hm y, w, hw.ge hx, hw ▸ ha y⟩

theorem isProper_morphismRestrict {S : Scheme.{0}} (A : Over S) {B : LB A.left} (h : RelAmple A B) {U : S.Opens}
    (hU : IsAffineOpen U) : IsProper (A.hom ∣_ U) := by
  obtain ⟨N, -, K, s, H⟩ := h U hU
  have h₁ := isProper_of_veryAmpleBy
    ((ProjSpace.veryAmpleBy_comp_iff (R := Γ(S, U)) (A.hom ∣_ U) hU.isoSpec.hom s).2 H)
  exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).1 h₁

theorem isProper_and_exists_isAmpleLB {S : Scheme.{0}} (A : Over S) {B : LB A.left} (hB : B.IsLB)
    (h : RelAmple A B) {H : LB S} (hH : IsAmpleLB H) : IsProper A.hom ∧ ∃ N : LB A.left, IsAmpleLB N := by
  obtain ⟨n, -, c, s, hs, ha⟩ := hH.exists_cover
  have hp : IsProper A.hom := IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) _ hs
    fun i => isProper_morphismRestrict A h (ha i)
  have := hH.compactSpace
  have := hH.quasiSeparatedSpace
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  obtain ⟨d, hd⟩ := exists_isAmpleLB_tw hB (LB.isLB_pull (isLB_lbPow hH.isLB n) A.hom) fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ (A.hom y)))
    exact ⟨secPull (s i) A.hom, _, (nonzeroLocus_secPull _ _).symm, hi, isAmpleLB_of_relAmple A hB h _ (ha i)⟩
  exact ⟨hp, _, hd⟩

theorem isQProjOver_of_relAmple : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  rintro K _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem isQProjOver_comp_of_isFinite_general {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    {s : Y ⟶ Sp R} (h : IsQProjOver s) : IsQProjOver (f ≫ s) := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have hO : IsAmpleLB (ProjSpace.O1 R N) := isAmple_projective_O_one R N
  have hY : IsAmpleLB ((ProjSpace.O1 R N).pull i) := hO.pull_of_isImmersion i
  have hX : IsAmpleLB (((ProjSpace.O1 R N).pull i).pull f) := hY.pull_of_isFinite f
  have := isProper_str R N
  have : LocallyOfFiniteType (f ≫ i ≫ PSpace.str R N) := inferInstance
  exact hX.isQProjOver _

theorem isQProjOver_comp_of_isFinite_noetherian :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) (s : Y ⟶ Sp R),
      IsFinite f → IsQProjOver s → IsQProjOver (f ≫ s) := by
  intro R _ _ X Y f s hf h
  exact isQProjOver_comp_of_isFinite_general f h

end GlobalTheory
end

