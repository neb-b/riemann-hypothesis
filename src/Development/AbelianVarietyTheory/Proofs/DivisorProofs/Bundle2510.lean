module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalisationProjectiveQuasiFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegMin

theorem finite_of_finite_closedPoints {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    (h : (closedPoints T).Finite) : Finite T := by
  have hc : IsClosed (closedPoints T) := by
    rw [← Set.biUnion_of_singleton (closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx
  have e := JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := T))
  rw [Set.univ_inter, hc.closure_eq] at e
  rw [← Set.finite_univ_iff, ← e]
  exact h

theorem exists_embedding_closedPoint_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f.fiber y) (hz : IsClosed ({z} : Set (f.fiber y))) :
    ∃ σ : (f.fiber y).residueField z ⟶ CommRingCat.of (AlgebraicClosure (Y.residueField y)),
      Spec.map σ ≫ (f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
          (AlgebraicClosure (Y.residueField y)))) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    show LocallyOfFiniteType (pullback.snd _ _); infer_instance
  have := isClosed_singleton_iff_isClosedImmersion.mp hz
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective
    ((f.fiber y).fromSpecResidueField z ≫ f.fiberToSpecResidueField y)
  have h1 : LocallyOfFiniteType (Spec.map ψ) := hψ ▸ inferInstance
  have h2 : IsFinite (Spec.map ψ) := isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr h1
  rw [IsFinite.SpecMap_iff] at h2
  letI := ψ.hom.toAlgebra
  haveI : Module.Finite (Y.residueField y) ((f.fiber y).residueField z) := h2
  let σ : (f.fiber y).residueField z →ₐ[Y.residueField y] AlgebraicClosure (Y.residueField y) :=
    IsAlgClosed.lift
  refine ⟨CommRingCat.ofHom σ.toRingHom, ?_⟩
  rw [← hψ]
  refine (Spec.map_comp _ _).symm.trans ?_
  congr 1
  ext a
  exact σ.commutes a

theorem finite_preimage_singleton_of_qFin {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hf : QFin f) (y : Y) : (f ⁻¹' {y}).Finite := by
  let K := AlgebraicClosure (Y.residueField y)
  choose σ hσ using exists_embedding_closedPoint_fiber f y
  let Φ : closedPoints (f.fiber y) → (Sp K ⟶ X) := fun z ↦
    Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y
  have hΦf (z) : Φ z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
      Y.fromSpecResidueField y := by
    simp only [Φ, Category.assoc, Scheme.Hom.fiber_fac]
    rw [← hσ z.1 z.2]
    simp only [Category.assoc]
  have hΦpt (z) : Φ z (IsLocalRing.closedPoint K : Sp K) = f.fiberι y z.1 := by
    have hm : (f.fiber y).fromSpecResidueField z.1 (Spec.map (σ z.1 z.2)
        (IsLocalRing.closedPoint K : Sp K)) ∈ Set.range ((f.fiber y).fromSpecResidueField z.1) :=
      ⟨_, rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hm
    show (Spec.map (σ z.1 z.2) ≫ (f.fiber y).fromSpecResidueField z.1 ≫ f.fiberι y)
      (IsLocalRing.closedPoint K : Sp K) = _
    exact congrArg (f.fiberι y) (Set.mem_singleton_iff.mp hm)
  have hΦinj : Function.Injective Φ := by
    intro z z' h
    have := hΦpt z
    rw [h, hΦpt z'] at this
    exact Subtype.ext ((f.fiberι y).isEmbedding.injective this).symm
  have hcp : (closedPoints (f.fiber y)).Finite := by
    rcases (closedPoints (f.fiber y)).eq_empty_or_nonempty with he | ⟨z₀, hz₀⟩
    · rw [he]; exact Set.finite_empty
    · have hS := hf K (Φ ⟨z₀, hz₀⟩)
      haveI := hS.to_subtype
      have : Finite (closedPoints (f.fiber y)) :=
        Finite.of_injective (β := {w : Sp K ⟶ X | w ≫ f = Φ ⟨z₀, hz₀⟩ ≫ f})
          (fun z ↦ ⟨Φ z, by simp only [Set.mem_setOf_eq, hΦf]⟩)
          (fun a b h ↦ hΦinj (congrArg Subtype.val h))
      exact Set.toFinite _
  haveI := finite_of_finite_closedPoints hcp
  exact Set.finite_coe_iff.mp ((f.fiberHomeo y).finite_iff.mp inferInstance)

theorem exists_finite_openImmersion_of_qFin : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra.FiniteType ℤ o] (N : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp o) (f : X ⟶ PSpace o N), IsIntegral X → Geo.Tor.IsNormalScheme X → LocallyOfFiniteType s → QuasiCompact s → IsSeparated s → f ≫ PSpace.str o N = s → QFin f → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o N) (i : X ⟶ Z), IsFinite p ∧ IsOpenImmersion i ∧ i ≫ p = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧ Dense (Set.range i) := by
  intro o _ _ _ N X s f hX hN _ _ _ hfs hq
  subst hfs
  haveI := isProper_str o N
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (PSpace.str o N)
  haveI : QuasiCompact f := QuasiCompact.of_comp f (PSpace.str o N)
  haveI : IsSeparated f := IsSeparated.of_comp f (PSpace.str o N)
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (finite_preimage_singleton_of_qFin f hq)
  exact GlobalTheory.ZMain.exists_finite_openImmersion_pSpace o N X f hX hN inferInstance inferInstance
    inferInstance inferInstance

end GlobalTheory.SiegMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeCrystallineThickeningOneElementLevel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.FreeThick

theorem ringHom_eq_of_basis {B C : Type} [CommRing B] [CommRing C] (Q : PDPoly B) {f g : Q.P →+* C}
    (h1 : ∀ b, f (algebraMap B Q.P b) = g (algebraMap B Q.P b)) (h2 : ∀ k, f (Q.e k) = g (Q.e k)) : f = g := by
  ext p
  have hp : p ∈ Submodule.span B (Set.range Q.e) := Q.e.mem_span p
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h2 k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul b x _ hx => rw [Algebra.smul_def, map_mul, map_mul, hx, h1]

end GlobalTheory.PDForm.FreeThick

namespace GlobalTheory.PDForm


open GlobalTheory.PDForm.FreeThick in
theorem exists_isFree_one_qAt : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (n : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) → ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Unit → F.B),
      IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  intro R _ I κ X t n T hT
  obtain ⟨Q⟩ := GlobalTheory.exists_pdPoly T.B
  obtain ⟨η, hη⟩ := _root_.GlobalTheory.PDA.PDPoly.exists_isStd T.B T.J T.δ Q
  obtain ⟨hlift, ε, hε⟩ := GlobalTheory.PDA.PDPoly.exists_lift_and_aug T.B Q
  have hfil := GlobalTheory.PDA.fil_properties Q.P (Q.ext T.J) η
  obtain ⟨K, hK⟩ : ∃ K : Ideal Q.P, K = fil η (n + 1) := ⟨_, rfl⟩
  have hsub : η.IsSubDPIdeal K := by rw [hK]; exact GlobalTheory.PDA.fil_isSubDPIdeal Q.P (Q.ext T.J) η (n + 1) (by omega)
  obtain ⟨δ', hδ', huniv⟩ := (GlobalTheory.DPQuot.quotient_subDPIdeal Q.P (Q.ext T.J) η).1 K hsub
  have hKle : K ≤ Q.ext T.J := by rw [hK]; exact (hfil.2.2.1 1 (n + 1) (by omega)).trans hfil.2.1.le
  letI : Algebra R Q.P := ((algebraMap T.B Q.P).comp (algebraMap R T.B)).toAlgebra
  haveI : IsScalarTower R T.B Q.P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hε1 : ∀ b, ε (algebraMap T.B Q.P b) = b := fun b ↦ by simp
  have hεJ : ∀ p : Q.P, ε p ∈ T.J ↔ p ∈ Q.ext T.J := by
    intro p
    constructor
    · intro hp
      have : p = algebraMap T.B Q.P (ε p) + (p - algebraMap T.B Q.P (ε p)) := by ring
      rw [this]
      refine add_mem (Q.algebraMap_mem_ext hp) (Ideal.mem_sup_right ((hε _).2 ?_))
      rw [map_sub, hε1, sub_self]
    · intro hp
      have hle : Q.ext T.J ≤ T.J.comap (ε : Q.P →+* T.B) := by
        refine sup_le (Ideal.map_le_iff_le_comap.2 fun b hb ↦ ?_) fun q hq ↦ ?_
        · rw [Ideal.mem_comap]; change ε (algebraMap T.B Q.P b) ∈ T.J; rw [hε1]; exact hb
        · rw [Ideal.mem_comap]; change ε q ∈ T.J; rw [(hε q).1 hq]; exact T.J.zero_mem
      exact hle hp
  let π₀ : Q.P →+* T.B₀ := T.π.comp (ε : Q.P →+* T.B)
  have hπ₀ : ∀ p, π₀ p = 0 ↔ p ∈ Q.ext T.J := fun p ↦ (T.ker _).trans (hεJ p)
  let πF : Q.P ⧸ K →+* T.B₀ := Ideal.Quotient.lift K π₀ fun p hp ↦ (hπ₀ p).2 (hKle hp)
  have hπF : ∀ p, πF (Ideal.Quotient.mk K p) = T.π (ε p) := fun p ↦ rfl
  have hlev : IsLev δ' (n + 1) := by
    have h := _root_.GlobalTheory.PDA.fil_le_map_fil Q.P (Q.ext T.J) η (Q.P ⧸ K) _ δ' (Ideal.Quotient.mk K) hδ' rfl (n + 1)
    rw [← hK, Ideal.map_quotient_self] at h
    exact le_bot_iff.1 h
  have halg : algebraMap R (Q.P ⧸ K) = (Ideal.Quotient.mk K).comp ((algebraMap T.B Q.P).comp (algebraMap R T.B)) :=
    rfl
  let F : Thick κ t :=
    { B := Q.P ⧸ K
      J := (Q.ext T.J).map (Ideal.Quotient.mk K)
      δ := δ'
      nil := (isDPNilpotent_iff_exists_isLevel δ').2 ⟨_, hlev⟩
      dp := by rw [halg]; exact IsDPMorphism.comp _ hδ' (IsDPMorphism.comp _ hη.dp T.dp)
      B₀ := T.B₀
      π := πF
      surj := fun b₀ ↦ by
        obtain ⟨b, rfl⟩ := T.surj b₀
        exact ⟨Ideal.Quotient.mk K (algebraMap T.B Q.P b), by rw [hπF, hε1]⟩
      ker := fun y ↦ by
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [Ideal.mem_quotient_iff_mem hKle]
        exact hπ₀ p
      x := T.x
      w := by
        rw [T.w]
        congr 1
        refine RingHom.ext fun r ↦ ?_
        change T.π (algebraMap R T.B r) = T.π (ε (algebraMap T.B Q.P (algebraMap R T.B r)))
        rw [hε1] }
  let φ : T.B →ₐ[R] F.B :=
    { (Ideal.Quotient.mk K).comp (algebraMap T.B Q.P) with commutes' := fun _ ↦ rfl }
  let u : T ⟶ F :=
    ⟨φ, RingHom.id T.B₀, fun b ↦ by
      change T.π b = T.π (ε (algebraMap T.B Q.P b)); rw [hε1],
     IsDPMorphism.comp _ hδ' hη.dp, by rw [spMap_id, Category.id_comp]⟩
  refine ⟨F, u, fun _ ↦ Ideal.Quotient.mk K (Q.e 1), ⟨hlev, fun _ ↦ Ideal.mem_map_of_mem _ (Q.e_one_mem_ext T.J), ?_⟩, ?_⟩
  · intro S hS a c hc
    have hS' : fil S.δ (n + 1) = ⊥ := hS
    obtain ⟨G, hG1, hG2⟩ := hlift S.B (a.φ : T.B →+* S.B) (fun k ↦ S.δ.dpow k (c ())) (S.δ.dpow_zero (hc ()))
      fun m k ↦ S.δ.mul_dpow (hc ())
    have hGa : G.comp (algebraMap T.B Q.P) = (a.φ : T.B →+* S.B) := RingHom.ext hG1
    have hGdp : IsDPMorphism η S.δ G :=
      GlobalTheory.PDA.PDPoly.isDPMorphism_of_isStd T.B T.J T.δ Q η hη S.B S.J S.δ G (c ()) (hc ()) (by rw [hGa]; exact a.dp)
        hG2
    have hGK : ∀ p ∈ K, G p = 0 := fun p hp ↦ by
      have h := hfil.2.2.2.2.2.2 S.B S.J S.δ G hGdp (n + 1)
      rw [hS', ← hK] at h
      exact (Ideal.mem_bot).1 (h (Ideal.mem_map_of_mem G hp))
    let Gb : Q.P ⧸ K →+* S.B := Ideal.Quotient.lift K G hGK
    have hGb : ∀ p, Gb (Ideal.Quotient.mk K p) = G p := fun p ↦ rfl
    let gφ : F.B →ₐ[R] S.B :=
      { Gb with
        commutes' := fun r ↦ by
          change G (algebraMap T.B Q.P (algebraMap R T.B r)) = _
          rw [hG1]; exact a.φ.commutes r }
    have hgdp : IsDPMorphism F.δ S.δ (gφ : F.B →+* S.B) := by
      refine huniv S.B S.J S.δ Gb ?_
      have : Gb.comp (Ideal.Quotient.mk K) = G := RingHom.ext hGb
      rw [this]; exact hGdp
    let g : F ⟶ S :=
      ⟨gφ, a.φ₀, fun b' ↦ by
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b'
        change a.φ₀ (T.π (ε p)) = S.π (G p)
        rw [a.comm, show a.φ (ε p) = G (algebraMap T.B Q.P (ε p)) from (hG1 _).symm]
        have hm : p - algebraMap T.B Q.P (ε p) ∈ Q.ext T.J :=
          Ideal.mem_sup_right ((hε _).2 (by rw [map_sub, hε1, sub_self]))
        have h2 := hGdp.1 (Ideal.mem_map_of_mem G hm)
        rw [← S.ker, map_sub, map_sub, sub_eq_zero] at h2
        exact h2.symm,
       hgdp, a.pt⟩
    refine ⟨g, ⟨Thick.Hom.ext' (AlgHom.ext fun b ↦ hG1 b), fun _ ↦ ?_⟩, ?_⟩
    · change G (Q.e 1) = c ()
      rw [hG2 1, S.δ.dpow_one (hc ())]
    · rintro g' ⟨h1, h2⟩
      refine Thick.Hom.ext' (AlgHom.ext fun b' ↦ ?_)
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b'
      change ((g'.φ : F.B →+* S.B).comp (Ideal.Quotient.mk K)) p = G p
      have hHdp : IsDPMorphism η S.δ ((g'.φ : F.B →+* S.B).comp (Ideal.Quotient.mk K)) :=
        IsDPMorphism.comp _ g'.dp hδ'
      refine congrArg (fun f : Q.P →+* S.B ↦ f p) (ringHom_eq_of_basis Q (fun b ↦ ?_) fun k ↦ ?_)
      · change (u ≫ g').φ b = G (algebraMap T.B Q.P b)
        rw [h1]; exact (hG1 b).symm
      · rw [hG2 k, ← hη.var k, hHdp.map_dpow (Q.e_one_mem_ext T.J)]
        change S.δ.dpow k (g'.φ (Ideal.Quotient.mk K (Q.e 1))) = _
        rw [show g'.φ (Ideal.Quotient.mk K (Q.e 1)) = c () from h2 ()]
  · have hsemi : SemiHom (RingHom.id R) (Ideal.Quotient.mk K) := fun r p ↦ map_smul (Ideal.Quotient.mkₐ R K) r p
    exact _root_.GlobalTheory.PDForm.rq_truncPoly R T.B T.J T.δ Q η (Q.P ⧸ K) F.J δ' (Ideal.Quotient.mk K) n hη hT hsemi hδ'
      Ideal.Quotient.mk_surjective rfl (fun b ↦ by rw [Ideal.Quotient.eq_zero_iff_mem, hK]) φ
      (SemiHom.of_algHom u.φ) u.dp fun _ ↦ rfl

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratedTwistSectionNonvanishingFiniteSet
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistMove

theorem exists_generating_secs_tens_lbPow {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F)
    (H : LB X) (N : ℕ) (s : Fin (N + 1) → H.Sec) (hH : H.IsLB) (hs : AbLaw.VeryAmpleBy p H s)
    (M : LB X) (hM : M.IsLB) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (n : ℕ) (u : Fin n → (CechPic.tens M (lbPow H m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated F X p H N s hH hs M hM
  refine ⟨t₀.toNat, fun m hm => ?_⟩
  obtain ⟨n, u, hu⟩ := ht m (by omega)
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens M (lbPow H m)).IsLB := isLB_tens hM hP
  have e : cls (AbLaw.tw M H m) (AbLaw.isLB_tw hM hH _) =
      cls M hM - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hM (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hM hH _)
  have e' : cls (AbLaw.tw M H m) (AbLaw.isLB_tw hM hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hM hP, cls_lbPow hH, neg_zsmul, natCast_zsmul,
      sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨_, v, hv⟩

theorem exists_twist_generated_sec_nonzero : ∀ (F : Type) [Field F] [Infinite F] (X : Scheme.{0}) (p : X ⟶ Sp F), IsProjOver p → ∀ (B : LB X), B.IsLB → ∀ S : Set X, S.Finite → ∃ (A : LB X) (_ : A.IsLB) (a : A.Sec), (∃ (n : ℕ) (u : Fin n → A.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ (∃ (n : ℕ) (u : Fin n → (CechPic.tens B A).Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ ∀ z ∈ S, z ∈ nonzeroLocus a := by
  intro F _ _ X p hp B hB S hS
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨N, ι, hι, e⟩ := hp
  haveI := hι
  have hs := ProjSpace.veryAmpleBy_secPull_coord ι
  rw [e] at hs
  have hH : ((ProjSpace.O1 F N).pull ι).IsLB := pull_isLB (ProjSpace.O1_isLB F N) _
  obtain ⟨H, hH, s, hs⟩ : ∃ H : LB X, H.IsLB ∧ ∃ s : Fin (N + 1) → H.Sec, AbLaw.VeryAmpleBy p H s :=
    ⟨_, hH, _, hs⟩
  obtain ⟨m₁, h₁⟩ := exists_generating_secs_tens_lbPow p H N s hH hs B hB
  obtain ⟨m₂, h₂⟩ := exists_generating_secs_tens_lbPow p H N s hH hs (LB.triv X) (LB.isLB_triv X)
  obtain ⟨n₁, u₁, hu₁⟩ := h₁ (max m₁ m₂) (le_max_left _ _)
  obtain ⟨n₂, u₂, hu₂⟩ := h₂ (max m₁ m₂) (le_max_right _ _)
  have hP : (lbPow H (max m₁ m₂)).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens (LB.triv X) (lbPow H (max m₁ m₂))).IsLB := isLB_tens (LB.isLB_triv X) hP
  have e₂ : cls _ hT = cls _ hP := by rw [cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hP e₂ _ u₂ hu₂
  obtain ⟨a, ha⟩ := exists_sec_nonzero_on_finite_of_generated F X p _ hP _ v hv S hS
  exact ⟨_, hP, a, ⟨_, v, hv⟩, ⟨_, u₁, hu₁⟩, ha⟩

end GlobalTheory.TwistMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToCoverSide
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem exists_gen_up : ∀ {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT} (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG} (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen) (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) [IsIso f] (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y') (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ) (u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k])) (hu' : u'.IsGen), ∃ u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt, Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt → val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt * (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  intro XA XP XG XT Y Y' LA LP LG LT hA hP hG hT α β c wA hwA ℓ hℓ w hw f _ sA mA sT mT e' h₁ h₂ h₃ k u' hu'
  obtain ⟨t1, ht1, v1⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff w).1 hw) hG hT (φ' := ![sT, mT])
    (ε := ![k, -k]) u' hu'
  obtain ⟨t2, ht2, v2⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff ℓ).1 hℓ) hP hG
    (φ' := fun i => ![sT, mT] i ≫ c) (ε := ![k, -k]) t1 ht1
  have ht3 := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen LP _ _ t2 ht2 (inv f)
  have hfe : ∀ i, inv f ≫ (![sT, mT] i ≫ c) ≫ β = ![sA, mA] i ≫ α := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Category.assoc, ← h₁, IsIso.inv_hom_id_assoc]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc]
      rw [← h₂, Category.assoc, ← h₁, reassoc_of% h₃, IsIso.inv_hom_id_assoc]
  obtain ⟨t4, ht4, v4⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hP (φ' := fun i => ![sA, mA] i ≫ α) (ε' := ![k, -k])
    (fun U _ h => by simp only [hfe]) _ ht3
  obtain ⟨u, hu, v5⟩ := GlobalTheory.ArcPull.exists_down_om hwA hP hA (φ' := ![sA, mA]) (φ := fun i => ![sA, mA] i ≫ α)
    (𝟙 Y) (fun i => (Category.id_comp _).symm) t4 ht4
  refine ⟨u, hu, fun Z q z JP JA JG Jt gP gA gG gT => ?_⟩
  have e5 := v5 Z (q ≫ f) z JP JA gP gA
  have e4 := v4 Z ((q ≫ f) ≫ 𝟙 Y) z JP gP
  have e3 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull gP t2 (inv f) ((q ≫ f) ≫ 𝟙 Y)
  have hq : ((q ≫ f) ≫ 𝟙 Y) ≫ inv f = q := by simp
  rw [hq] at e3
  have e2 : val t2 q z JP = pw ℓ (fun i => ![sT, mT] i ≫ c) ![k, -k] q z _ _ * val t1 q z JG :=
    v2 Z q z _ _ (gP.mem _ q) (gG.mem _ q)
  have e1 : val t1 q z JG = pw w ![sT, mT] ![k, -k] q z _ _ * val u' q z Jt := v1 Z q z _ _ (gG.mem _ q) (gT.mem _ q)
  have h₄ : f ≫ mA ≫ α = mT ≫ c ≫ β := by rw [← reassoc_of% h₃, h₁, reassoc_of% h₂]
  simp only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, GlobalTheory.ArcPull.om, tf, Category.assoc, Category.comp_id] at e1 e2 e3 e4 e5 ⊢
  have p₁ : q ≫ f ≫ sA ≫ α = q ≫ sT ≫ c ≫ β := by rw [h₁]
  have p₄ : q ≫ f ≫ mA ≫ α = q ≫ mT ≫ c ≫ β := by rw [h₄]
  have p₃ : q ≫ e' ≫ f ≫ sA = q ≫ f ≫ mA := by rw [h₃]
  have p₂ : q ≫ e' ≫ sT = q ≫ mT := by rw [h₂]
  have p₂' : q ≫ e' ≫ sT ≫ c = q ≫ mT ≫ c := by rw [reassoc_of% h₂]
  have p₂'' : q ≫ e' ≫ sT ≫ c ≫ β = q ≫ mT ≫ c ≫ β := by rw [reassoc_of% h₂]
  rw [e4, e3, e2, e1, p₁, p₄] at e5
  rw [p₃, p₂'', p₂', p₂]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e5
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToTraitSide
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem exists_down_three {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT}
    (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG}
    (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen)
    (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y')
    (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ)
    (u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k]), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt,
      Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt →
      val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt *
        (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  have hm : f ≫ mA ≫ α = mT ≫ c ≫ β := by
    rw [← h₂, Category.assoc, ← h₁, ← Category.assoc f mA, ← h₃]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up ((isGen_iff wA).1 hwA) hP hA (φ' := ![sA, mA]) (ε := ![k, -k]) u hu
  obtain ⟨t₂, ht₂, v₂⟩ := GlobalTheory.ArcPull.exists_down_om hℓ hP hG (φ' := ![sT ≫ c, mT ≫ c]) f (fun i => by
      fin_cases i
      · simpa using h₁.symm
      · simpa using hm.symm) t₁ ht₁
  obtain ⟨u', hu', v₃⟩ := GlobalTheory.ArcPull.exists_down_om hw hG hT (φ' := ![sT, mT]) (φ := ![sT ≫ c, mT ≫ c]) (𝟙 Y')
    (fun i => by fin_cases i <;> simp) t₂ ht₂
  refine ⟨u', hu', fun Z q z JP JA JG Jt hP' hA' hG' hT' => ?_⟩
  have e₁ : val t₁ (q ≫ f) z JP = pw wA ![sA, mA] ![k, -k] (q ≫ f) z (fun i => JP ((q ≫ f) ≫ ![sA, mA] i ≫ α))
      (fun i => JA ((q ≫ f) ≫ ![sA, mA] i)) * val u (q ≫ f) z JA :=
    v₁ Z (q ≫ f) z _ _ (hP'.mem _ _) (hA'.mem _ _)
  have e₂ := v₂ Z q z JP JG hP' hG'
  have e₃ := v₃ Z q z JG Jt hG' hT'
  rw [Category.comp_id] at e₃
  rw [e₂, e₃] at e₁
  simp only [pw, GlobalTheory.ArcPull.om, tf, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Category.assoc] at e₁ ⊢
  simp only [reassoc_of% h₁, reassoc_of% hm, reassoc_of% h₂, reassoc_of% h₃, h₁, hm, h₂, h₃] at e₁ ⊢
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e₁
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPoint_rescale_same_torsionPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k k' d : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ k → 1 ≤ d → k' = d * k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → ∃ pk' : QkPt u.D.toPre (PadicAlgCl p) k', pk'.y = d • pk.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) k' pk' x := by
  first | exact @GlobalTheory.QLevelRescale.exists_qkPt_rescale | exact GlobalTheory.QLevelRescale.exists_qkPt_rescale | (intros; apply GlobalTheory.QLevelRescale.exists_qkPt_rescale <;> assumption)
end

