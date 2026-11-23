module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinSec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.locFinSec_of :
    CoverOne → LocFinGeo → LocFinSec := by
  intro hC hG R _ F G f V U r _ b hb
  obtain ⟨W, π, a, hE, hS, ha⟩ := hC R f V b hb
  haveI := hE
  haveI := hS
  refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ (hG π r) ?_
  rintro U' g ⟨s, hs⟩ V' k r' hk
  refine ⟨Sec.res (pullback.lift k r' hk ≫ s) a, ?_⟩
  rw [map_res, ha, res_res]
  congr 1
  rw [Category.assoc, hs, pullback.lift_fst]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultBC
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma length_self_eq {R R' : Type} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Module.length R R = Module.length R' R' := by
  have h : ((Module.length R R : ℕ∞) : WithBot ℕ∞) = (Module.length R' R' : ℕ∞) := by
    rw [Module.coe_length, Module.coe_length]
    exact Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm
  exact_mod_cast h

private lemma length_stalk_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (hy : f x = y) :
    Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  subst hy
  exact length_self_eq (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.multBC_of :
    MultBC := by
  intro Z' S' Z S v p' p g h
  funext Ω _ _ z
  have hw : (z ≫ p') ≫ g = (z ≫ v) ≫ p := by
    simp only [Category.assoc, h.w]
  have hP : IsPullback (pullback.fst p' (z ≫ p') ≫ v) (pullback.snd p' (z ≫ p')) p ((z ≫ v) ≫ p) := by
    rw [← hw]
    exact (IsPullback.of_hasPullback p' (z ≫ p')).paste_horiz h
  have hl : (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p')) ≫ hP.isoPullback.hom =
      pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm := by
    apply pullback.hom_ext
    · rw [Category.assoc, hP.isoPullback_hom_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc, hP.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]
  have hpt : hP.isoPullback.hom (pt (pullback.lift z (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p' (z ≫ p'))) =
      pt (pullback.lift (z ≫ v) (𝟙 _) (Category.id_comp _).symm : gp Ω ⟶ pullback p ((z ≫ v) ≫ p)) := by
    rw [← pt_comp, hl]
  simp only [Wt.comap, mult]
  rw [length_stalk_eq hP.isoPullback.hom _ _ hpt]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultBasic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multBasic_of :
    MultBC → MultOpen → MultEt → MultBasic := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultEt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isOpenImmersion_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (s : Y ⟶ X) [Etale f] (h : s ≫ f = 𝟙 Y) :
    IsOpenImmersion s := by
  have hpb := pullback_lift_diagonal_isPullback s f
  have hgr := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb
    (inferInstance : IsOpenImmersion (pullback.diagonal f))
  have hsnd : IsOpenImmersion (pullback.snd (s ≫ f) f) := by
    have : IsIso (s ≫ f) := by rw [h]; infer_instance
    infer_instance
  have hs : s = pullback.lift (𝟙 Y) s (by simp [h]) ≫ pullback.snd (s ≫ f) f :=
    (pullback.lift_snd _ _ _).symm
  rw [hs]
  exact IsOpenImmersion.comp _ _

private theorem length_self_of_isField (R : Type) [CommRing R] (h : IsField R) : Module.length R R = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_self_iff_isUnit]
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  refine ⟨⟨a, b, hab⟩, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
  exact ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩

private theorem length_stalk_pt {V : Scheme.{0}} {Ω : Type} [Field Ω] (s : gp Ω ⟶ V) [IsOpenImmersion s] :
    Module.length (V.presheaf.stalk (pt s)) (V.presheaf.stalk (pt s)) = 1 := by
  have hK : IsField ((Spec (CommRingCat.of Ω)).presheaf.stalk (IsLocalRing.closedPoint Ω)) := by
    have e : (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω)) = genericPoint _ :=
      Subsingleton.elim _ _
    rw [e]
    exact (inferInstance : Field (Spec (CommRingCat.of Ω)).functionField).toIsField
  haveI := (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion s›).2 (IsLocalRing.closedPoint Ω)
  have hV : IsField (V.presheaf.stalk (pt s)) :=
    MulEquiv.isField hK (asIso (s.stalkMap (IsLocalRing.closedPoint Ω))).commRingCatIsoToRingEquiv.toMulEquiv
  exact length_self_of_isField _ hV

theorem UpperTheory.Gal.TranscendenceTraces.multEt_of :
    MultEt := by
  intro Z S p _
  funext Ω _ _ z
  change mult p Ω z = (1 : ℤ)
  have hσ : IsOpenImmersion (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p)) :=
    isOpenImmersion_of_section (pullback.snd p (z ≫ p)) _ (pullback.lift_snd _ _ _)
  have hl := length_stalk_pt (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p))
  simp only [mult]
  rw [hl]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultPt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem exists_fac {Ω : Type} [Field Ω] {S : Scheme.{0}} (x : gp Ω ⟶ S) (s : S) (h : pt x = s) :
    ∃ a : gp Ω ⟶ Spec (S.residueField s), a ≫ S.fromSpecResidueField s = x := by
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective x
  have hx : (Scheme.SpecToEquivOfField Ω S).symm ⟨t, a⟩ = Spec.map a ≫ S.fromSpecResidueField t := by
    simp [Scheme.SpecToEquivOfField]
  rw [hx] at h ⊢
  have hs : s ∈ Set.range (S.fromSpecResidueField t) := ⟨pt (Spec.map a), by rw [← pt_comp, h]⟩
  rw [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at hs
  subst hs
  exact ⟨Spec.map a, rfl⟩

theorem UpperTheory.Gal.TranscendenceTraces.multPt_of :
    WtFlat → WtPt → MultBC → MultPt := by
  intro hflat hpt hbc Z S p _ Ω Ω' _ _ _ _ z z' hzz
  obtain ⟨s, hs⟩ : ∃ s, p (pt z) = s := ⟨_, rfl⟩
  have hpb := IsPullback.of_hasPullback p (S.fromSpecResidueField s)
  have hw := hpt (pullback.snd p (S.fromSpecResidueField s))
    (mult (pullback.snd p (S.fromSpecResidueField s))) (hflat _)
  have hm := hbc _ _ _ _ hpb
  obtain ⟨a, ha⟩ := exists_fac (z ≫ p) s (by rw [pt_comp, hs])
  obtain ⟨a', ha'⟩ := exists_fac (z' ≫ p) s (by rw [pt_comp, ← hzz, hs])
  obtain ⟨z1, e1⟩ : ∃ z1 : gp Ω ⟶ pullback p (S.fromSpecResidueField s),
      z1 ≫ pullback.fst _ _ = z := ⟨pullback.lift z a ha.symm, pullback.lift_fst _ _ _⟩
  obtain ⟨z1', e1'⟩ : ∃ z1' : gp Ω' ⟶ pullback p (S.fromSpecResidueField s),
      z1' ≫ pullback.fst _ _ = z' := ⟨pullback.lift z' a' ha'.symm, pullback.lift_fst _ _ _⟩
  have hp1 : pt z1 = pt z1' := by
    apply (IsPreimmersion.isEmbedding (pullback.fst p (S.fromSpecResidueField s))).injective
    rw [← pt_comp z1, ← pt_comp z1', e1, e1']
    exact hzz
  have key := hw Ω Ω' z1 z1' hp1
  rw [hm] at key
  simpa [Wt.comap, e1, e1'] using key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a b => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

private theorem length_stalk_eq_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (h : f x = y) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) = Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) := by
  subst h
  have : IsIso (f.stalkMap x) := inferInstance
  exact (length_self_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm

theorem UpperTheory.Gal.TranscendenceTraces.multSec_of :
    MultSec := by
  intro V Ω _ _ r z hz
  haveI : IsIso (z ≫ r) := by rw [hz]; infer_instance
  haveI : IsIso (pullback.fst r (z ≫ r)) := inferInstance
  unfold mult
  rw [length_stalk_eq_of_isIso (pullback.fst r (z ≫ r)) _ (pt z)
    (by rw [← pt_comp, pullback.lift_fst])]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multSum_of :
    MultSumPt → MultBC → MultSum := by
  intro hPt hBC Z S p _ _ Ω _ _ x
  have hpb : IsPullback (pullback.fst p x) (pullback.snd p x) p x := IsPullback.of_hasPullback p x
  have hfin := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb (IsLocalRing.closedPoint Ω)
  have h1 := hPt Ω (pullback.snd p x)
  rw [hBC _ _ _ _ hpb] at h1
  rw [show pt x = x (IsLocalRing.closedPoint Ω) from rfl, ← hfin, ← h1]
  simp only [Wt.push, Wt.comap]
  have hb := fib_bijOn hpb (Ω := Ω) (𝟙 _)
  rw [Category.id_comp] at hb
  exact (finsum_mem_eq_of_bijOn _ hb (fun _ _ => rfl)).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSumPt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.multSumPt_of :
    StalkSum → MultSec → PtLift → PtOne → FibFin → MultSumPt := by
  intro hS hM hL hO hF V Ω _ _ r _
  have hI : IsIntegralHom r := inferInstance
  have hbij : Set.BijOn (fun z : gp Ω ⟶ V => pt z) (fib r (𝟙 (gp Ω))) Set.univ := by
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · intro z hz z' hz' h
      exact hO Ω r Ω (𝟙 (gp Ω)) z z' hz hz' h
    · intro v _
      have hv : r v = pt (𝟙 (gp Ω)) := by
        have h1 := pt_eq (𝟙 (gp Ω)) (r v)
        simpa using h1
      obtain ⟨z, hz, hzv⟩ := hL r Ω (𝟙 (gp Ω)) v hv
      exact ⟨z, hz, hzv⟩
  have hfin : Finite V := by
    have hu : (Set.univ : Set V).Finite := by
      rw [← hbij.image_eq]
      exact (hF r Ω (𝟙 (gp Ω))).image _
    exact Set.finite_univ_iff.mp hu
  show (∑ᶠ (z : gp Ω ⟶ V) (_ : z ∈ fib r (𝟙 (gp Ω))), mult r Ω z) = _
  rw [finsum_mem_eq_of_bijOn (fun z : gp Ω ⟶ V => pt z) hbij
    (g := fun v : V => ((Module.length (V.presheaf.stalk v) (V.presheaf.stalk v)).toNat : ℤ))
    (fun z hz => hM Ω r z hz), finsum_mem_univ, ← Nat.cast_finsum, hS Ω r]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlInt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem normal_affineOpen_integrallyClosed (S : Scheme.{0}) (hN : Nml S) (U : S.Opens) (hU : IsAffineOpen U)
    [IsDomain Γ(S, U)] : IsIntegrallyClosed Γ(S, U) := by
  refine IsIntegrallyClosed.of_localization_maximal ?_
  intro p _ _
  let y : PrimeSpectrum Γ(S, U) := ⟨p, inferInstance⟩
  have hmem : hU.fromSpec y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hU.fromSpec y, hmem⟩
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hU.fromSpec y)) p := hU.isLocalization_stalk' y hmem
  obtain ⟨_, hint⟩ := hN (hU.fromSpec y)
  haveI := hint
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.nmlInt_of :
    NmlInt := by
  intro S _ hN s
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨s, hs⟩⟩
  haveI : IsDomain Γ(S, U) := IsIntegral.component_integral U
  exact ⟨U, hU, hs, inferInstance, normal_affineOpen_integrallyClosed S hN U hU⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlLoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nmlLoc_of :
    NmlInt → NmlNoeth → NmlLoc := by
  intro hI hN S hS h
  rcases h with h | h
  · haveI := h
    exact hI S hS
  · haveI := h
    exact hN S hS
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlNoeth
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem exists_open_irreducible_nhds_of_generizations {Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
    [TopologicalSpace.NoetherianSpace Y] (y : Y) (hG : IsIrreducible {z | z ⤳ y}) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ IsIrreducible U := by
  have key : ∀ W ∈ irreducibleComponents Y, y ∈ W → W = closure {z | z ⤳ y} := by
    intro W hW hyW
    have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
    have hgen := hW.1.isGenericPoint_genericPoint_closure
    rw [hWc.closure_eq] at hgen
    have hcl : closure {hW.1.genericPoint} = W := hgen
    have hsub : W ⊆ closure {z | z ⤳ y} := by
      rw [← hcl]
      exact closure_mono (Set.singleton_subset_iff.mpr (hgen.specializes hyW))
    exact le_antisymm hsub (hW.2 hG.closure hsub)
  let C := irreducibleComponent y
  refine ⟨(⋃₀ (irreducibleComponents Y \ {C}))ᶜ, ?_, ?_, ?_⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  · simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_diff, Set.mem_singleton_iff,
      not_exists, not_and, and_imp]
    intro W hW hne hyW
    exact hne ((key W hW hyW).trans (key C (irreducibleComponent_mem_irreducibleComponents y)
      mem_irreducibleComponent).symm)
  · apply isIrreducible_iff_closure.mp
    rw [closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _
      (irreducibleComponent_mem_irreducibleComponents y)]
    exact isIrreducible_irreducibleComponent

private theorem isIntegrallyClosed_affine_of_stalks {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
  let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  haveI : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hy
  change IsIntegrallyClosed (Localization.AtPrime y.asIdeal)
  exact (h _).of_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl
    (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime y.asIdeal)).toRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.nmlNoeth_of :
    NmlNoeth := by
  intro S _ hN x
  haveI : ∀ z : S, IsDomain (S.presheaf.stalk z) := fun z => (hN z).1
  obtain ⟨_, ⟨V : S.Opens, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV.isCompact
  haveI : IsNoetherian V.toScheme := {}
  have hns : TopologicalSpace.NoetherianSpace V.toScheme := inferInstance
  have hqs : QuasiSober V.toScheme := inferInstance
  have hG : IsIrreducible {z | z ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    haveI : IrreducibleSpace (Spec (S.presheaf.stalk x)) := PrimeSpectrum.irreducibleSpace
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (S.fromSpecStalk x).continuous.continuousOn
  have hGV : {z | z ⤳ x} ⊆ (V : Set S) := fun z hz => hz.mem_open V.isOpen hxV
  have hG' : IsIrreducible {z : V | z ⤳ ⟨x, hxV⟩} := by
    have he : {z : V | z ⤳ ⟨x, hxV⟩} =
        Set.range (fun z : {z | z ⤳ x} => (⟨z.1, hGV z.2⟩ : V)) := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨z.1, (Topology.IsInducing.subtypeVal.specializes_iff).mpr hz⟩, rfl⟩
      · rintro ⟨w, rfl⟩
        exact (Topology.IsInducing.subtypeVal.specializes_iff).mp w.2
    rw [he, ← Set.image_univ]
    haveI : IrreducibleSpace {z | z ⤳ x} := isIrreducible_iff_irreducibleSpace.mp hG
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (by fun_prop : Continuous _).continuousOn
  obtain ⟨W, hWo, hxW, hWi⟩ := @exists_open_irreducible_nhds_of_generizations V.toScheme _ hqs hns ⟨x, hxV⟩ hG'
  have hW'o : IsOpen (Subtype.val '' W : Set S) := V.isOpen.isOpenMap_subtype_val W hWo
  obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hxU, hUW⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (⟨_, hxW, rfl⟩ : x ∈ Subtype.val '' W) hW'o
  have hUi : IsIrreducible (U : Set S) :=
    ⟨⟨x, hxU⟩, (hWi.image _ continuous_subtype_val.continuousOn).2.open_subset U.isOpen hUW⟩
  haveI : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hUi
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  haveI : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨x, hxU⟩, trivial⟩⟩
  haveI : IsDomain Γ(S, U) :=
    MulEquiv.isDomain Γ(U.toScheme, ⊤) (U.topIso).commRingCatIsoToRingEquiv.symm.toMulEquiv
  exact ⟨U, hU, hxU, inferInstance, isIntegrallyClosed_affine_of_stalks hU fun z => (hN z).2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormAff
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.normAff_of :
    Chart → NormSpec → NormAff := by
  intro hC hN Z S p _ U hU hD hI
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC p Γ(S, U) hU.fromSpec
  obtain ⟨w, hw⟩ := hN Γ(S, U) B
  exact ⟨⟨_, _, hU.fromSpec, v, _, hpb⟩, w, inferInstance, hU.range_fromSpec, hw⟩
end

