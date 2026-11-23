module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocus
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

noncomputable section
namespace GlobalTheory.ZH.CombLocus

def secComb {X : Scheme.{0}} {H : LB X} {J : Type} [Fintype J] (a : J → Γ(X, ⊤)) (s : J → H.Sec) : H.Sec where
  f l := ∑ k, resG X le_top (a k) * (s k).f l
  compat i j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ∀ (U V : X.Opens) (h : V ≤ U),
        (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) (a k)) = resG X (le_top : V ≤ ⊤) (a k) := by
      intro U V h
      change (X.presheaf.map (homOfLE _).op ≫ X.presheaf.map (homOfLE h).op).hom (a k) = _
      rw [← Functor.map_comp]
      rfl
    rw [map_mul, map_mul, (s k).compat i j, e, e, mul_left_comm]

theorem exists_crd_secComb {X Y : Scheme.{0}} (h : X ⟶ Y) {H : LB Y} {J : Type} [Fintype J] (σ : J → H.Sec)
    (hcov : ⨆ k, nonzeroLocus (σ k) = ⊤) (a : J → Γ(X, ⊤)) {K : Type} [Field K] (y : Sp K ⟶ X) :
    ∃ w, Crd H σ (y ≫ h) w ∧ (⊤ ≤ y ⁻¹ᵁ nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) ↔
      ∑ k, valR y ⊤ (a k) * w k ≠ 0) := by
  have h₀ : (y ≫ h) (IsLocalRing.closedPoint K) ∈ ⨆ k, nonzeroLocus (σ k) := by rw [hcov]; trivial
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 h₀
  obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hk₀
  have h₁ : ⊤ ≤ (y ≫ h) ⁻¹ᵁ H.U l := (CrdCalc.top_le_iff _ _).2 hl
  have h₂ : ⊤ ≤ y ⁻¹ᵁ (H.pull h).U (fun _ => l) := fun p hp => Set.mem_iInter.2 fun _ => h₁ hp
  refine ⟨fun k => valR (y ≫ h) (H.U l) ((σ k).f l), ⟨l, 1, h₁, fun k => by simp⟩, ?_⟩
  have h₃ : Crd (H.pull h) (fun _ : Unit => secComb a fun k => GlobalTheory.secPull (σ k) h) y
      (fun _ => ∑ k, valR y ⊤ (a k) * valR (y ≫ h) (H.U l) ((σ k).f l)) := by
    refine ⟨fun _ => l, 1, h₂, fun _ => ?_⟩
    rw [Units.val_one, one_mul, CrdCalc.valR_eq y _ h₂]
    refine Eq.symm ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_))
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res y _ h₂]
    exact congrArg _ (GlobalTheory.Points.valR_appLE y h _ h₂ _)
  exact (CrdCalc.crd_isUnit_iff () h₃).symm.trans isUnit_iff_ne_zero

theorem opens_eq_of_field_points {X : Scheme.{0}} {U V : X.Opens}
    (h : ∀ (K : Type) [Field K] (y : Sp K ⟶ X), ⊤ ≤ y ⁻¹ᵁ U ↔ ⊤ ≤ y ⁻¹ᵁ V) : U = V := by
  have e : ∀ (p : X) (O : X.Opens), ⊤ ≤ X.fromSpecResidueField p ⁻¹ᵁ O ↔ p ∈ O := fun p O =>
    ⟨fun H => by
      have := H (Set.mem_univ (IsLocalRing.closedPoint (X.residueField p)))
      have h' : X.fromSpecResidueField p (IsLocalRing.closedPoint (X.residueField p)) ∈ O := this
      exact (Scheme.fromSpecResidueField_apply p (IsLocalRing.closedPoint (X.residueField p))) ▸ h',
    fun H s _ => by
      change X.fromSpecResidueField p s ∈ O
      rwa [Scheme.fromSpecResidueField_apply]⟩
  ext p
  exact (e p U).symm.trans ((h _ (X.fromSpecResidueField p)).trans (e p V))

theorem isAffineHom_homOfLE {P Z : Scheme.{0}} (π : P ⟶ Z) {V W : Z.Opens} (e : V ≤ W) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) : IsAffineHom (P.homOfLE (π.preimage_mono e)) := by
  have : IsAffine V := hV
  have : IsAffine W := hW
  have sq : IsPullback (P.homOfLE (π.preimage_mono e)) (π ∣_ V) (π ∣_ W) (Z.homOfLE e) := by
    refine IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ W).ι) (h₂₂ := W.ι) (v₁₃ := π) ?_ ?_ (isPullback_morphismRestrict π W).flip
    · rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
      exact (isPullback_morphismRestrict π V).flip
    · rw [← cancel_mono W.ι]
      simp
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip (inferInstance : IsAffineHom (Z.homOfLE e))

theorem isAffineOpen_of_comb : ∀ (P Z : Scheme.{0}) (π : P ⟶ Z) [IsProper π] (J : Type) [Fintype J] (D : P.Opens) (W : Z.Opens), IsAffineOpen W → D ≤ π ⁻¹ᵁ W → (∀ z ∈ W, ∃ (W' : Z.Opens) (H : LB (π ⁻¹ᵁ W').toScheme) (σ : J → H.Sec) (m : J → Γ(Z, W ⊓ W')), z ∈ W' ∧ IsAffineOpen W' ∧ ⨆ k, nonzeroLocus (σ k) = ⊤ ∧ (∀ k, IsAffineOpen (nonzeroLocus (σ k))) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ W').toScheme) (w : J → K), ⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι ≫ π) ⁻¹ᵁ W → Crd H σ y w → (⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι) ⁻¹ᵁ D ↔ ∑ k, valR (y ≫ (π ⁻¹ᵁ W').ι ≫ π) (W ⊓ W') (m k) * w k ≠ 0)) → IsAffineOpen D := by
  intro P Z π _ J _ D W hW hD H
  have : IsAffine W := hW
  have : IsAffineHom (π.resLE W D hD) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun z => ?_
    obtain ⟨W', H, σ, m, hz, hW', hcov, haff, hiff⟩ := H z.1 z.2
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := z.1) (U := W ⊓ W') ⟨z.2, hz⟩
    have hle' : V ≤ W ⊓ W' := hle
    have : IsAffine V := hV
    refine ⟨W.ι ⁻¹ᵁ V, hzV, hV.preimage_of_isOpenImmersion _ (by simpa using hle'.trans inf_le_left), ?_⟩
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
      ← D.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    have e : V ≤ W' := hle'.trans inf_le_right
    have := isAffineHom_homOfLE π e hV hW'
    set h := P.homOfLE (π.preimage_mono e) with hh
    have hι : h ≫ (π ⁻¹ᵁ W').ι = (π ⁻¹ᵁ V).ι := Scheme.homOfLE_ι _ _
    have ha : ⊤ ≤ ((π ⁻¹ᵁ V).ι ≫ π) ⁻¹ᵁ (W ⊓ W') := fun p _ => hle' p.2
    let a : J → Γ((π ⁻¹ᵁ V).toScheme, ⊤) := fun k => (((π ⁻¹ᵁ V).ι ≫ π).appLE (W ⊓ W') ⊤ ha).hom (m k)
    have ht := isAffineOpen_nonzeroLocus_of_universallyClosed (π ∣_ V) (fun k => GlobalTheory.secPull (σ k) h)
      (by simp only [GlobalTheory.nonzeroLocus_secPull]; rw [← Scheme.Hom.preimage_iSup, hcov]; rfl)
      (fun k => by rw [GlobalTheory.nonzeroLocus_secPull]; exact (haff k).preimage h)
      (secComb a fun k => GlobalTheory.secPull (σ k) h)
    have hE : nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) = (π ⁻¹ᵁ V).ι ⁻¹ᵁ D := by
      have key : ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ V).toScheme),
          ⊤ ≤ y ⁻¹ᵁ nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) ↔ ⊤ ≤ y ⁻¹ᵁ ((π ⁻¹ᵁ V).ι ⁻¹ᵁ D) := by
        intro K _ y
        obtain ⟨w, hw, hiff'⟩ := exists_crd_secComb h σ hcov a y
        have e₁ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι = y ≫ (π ⁻¹ᵁ V).ι := by rw [Category.assoc, hι]
        have e₂ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι ≫ π = y ≫ (π ⁻¹ᵁ V).ι ≫ π := by
          rw [← Category.assoc, e₁, Category.assoc]
        have h₄ := hiff K (y ≫ h) w (by rw [e₂]; exact fun p _ => (hle' (y p).2).1) hw
        rw [e₁, e₂] at h₄
        refine hiff'.trans (Iff.trans ?_ h₄.symm)
        have e₃ : ∀ k, valR y ⊤ (a k) = valR (y ≫ (π ⁻¹ᵁ V).ι ≫ π) (W ⊓ W') (m k) := fun k =>
          GlobalTheory.Points.valR_appLE y _ ha le_top _
        simp only [e₃]
      exact opens_eq_of_field_points key
    rw [hE] at ht
    have h₆ := ht.image_of_isOpenImmersion (π ⁻¹ᵁ V).ι
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm] at h₆
  exact isAffine_of_isAffineHom (π.resLE W D hD)

end GlobalTheory.ZH.CombLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionTestSpecialFibreOpenPart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FibreImm

theorem le_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] {U V : X.Opens}
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  intro z hz
  by_contra hV
  obtain ⟨y, ⟨hy, hy'⟩, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set X) ∩ (V : Set X)ᶜ) ⟨z, hz, hV⟩
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed)
  have e := pointOfClosedPoint_apply π y hc (IsLocalRing.closedPoint k)
  have h1 := (CrdCalc.top_le_iff _ _).1 (h _ (pointOfClosedPoint_comp π y hc)
    ((CrdCalc.top_le_iff _ _).2 (e.symm ▸ hy)))
  exact hy' (e ▸ h1)

theorem eq_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] {U : X.Opens} {f g : Γ(X, U)}
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = GlobalTheory.ZH.valR x U g) : f = g := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  refine le_of_points π fun x hx hb => ?_
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le _))
  refine absurd ?_ ((CrdCalc.isUnit_valR_iff _ U hU _).2 hb).ne_zero
  rw [CrdCalc.valR_eq x U hU, map_sub, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, h x hx hU, sub_self]

theorem isClosedImmersion_of_surjective {V U : Scheme.{0}} [IsAffine V] [U.IsSeparated] (f : V ⟶ U)
    (hf : Function.Surjective f.appTop) : IsClosedImmersion f := by
  have : IsClosedImmersion (f ≫ U.toSpecΓ) := by
    refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact hf.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2
  exact IsClosedImmersion.of_comp f U.toSpecΓ

theorem isClosedImmersion_of_crd {k : Type} [Field k] [IsAlgClosed k] {X T : Scheme.{0}} [IsReduced X]
    (pX : X ⟶ Sp k) (pT : T ⟶ Sp k) [LocallyOfFiniteType pX] [IsSeparated pT] (h : X ⟶ T) (hp : h ≫ pT = pX)
    {HX : LB X} {HT : LB T} (hX : HX.IsLB) (hT : HT.IsLB) {J : Type} (F : J → HX.Sec) (s : J → HT.Sec)
    (J₀ : Set J) (imm : ImmBy pX HX F J₀) (cov : ⨆ i : J₀, Out.nonzeroLocus (s i) = ⊤)
    (crd : ∀ (x : Sp k ⟶ X) (v : J → k), x ≫ pX = 𝟙 _ → Crd HX F x v → Crd HT s (x ≫ h) v) :
    IsClosedImmersion h := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _ cov fun i => ?_
  obtain ⟨haff, r, hr, hgen⟩ := imm.2 i i.2
  have hV : h ⁻¹ᵁ Out.nonzeroLocus (s i) = Out.nonzeroLocus (F i) := by
    refine le_antisymm (le_of_points pX fun x hx hU => ?_) (le_of_points pX fun x hx hU => ?_)
    · obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      exact (CrdCalc.crd_isUnit_iff _ hv).1 ((CrdCalc.crd_isUnit_iff _ (crd x v hx hv)).2 hU)
    · obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      exact (CrdCalc.crd_isUnit_iff _ (crd x v hx hv)).1 ((CrdCalc.crd_isUnit_iff _ hv).2 hU)
  have hsurj : Function.Surjective (h.appLE _ _ hV.ge).hom := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hgen, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨constFn pT _ a, eq_of_points pX fun x hx hU => ?_⟩
      rw [GlobalTheory.Points.valR_appLE x h hV.ge hU, GlobalTheory.Points.valR_constFn_of_section pX x hx _ hU,
        GlobalTheory.Points.valR_constFn_of_section pT (x ≫ h) (by rw [Category.assoc, hp, hx])
          (Out.nonzeroLocus (s i)) (hU.trans (x.preimage_mono hV.ge))]
    · obtain ⟨r', hr', -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hT (s j) (s i) _ le_rfl
      refine ⟨r', eq_of_points pX fun x hx hU => ?_⟩
      obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      have h1 := CrdCalc.crd_ratio hv (hr j) hU
      have h2 := CrdCalc.crd_ratio (crd x v hx hv) hr' (hU.trans (x.preimage_mono hV.ge))
      rw [GlobalTheory.Points.valR_appLE x h hV.ge hU]
      exact ((CrdCalc.crd_isUnit_iff _ hv).2 hU).mul_right_cancel (h2.symm.trans h1)
  have hsurj' : Function.Surjective (h.app (Out.nonzeroLocus (s i))).hom := by
    revert hsurj
    generalize Out.nonzeroLocus (F i) = V at hV
    subst hV
    rw [Scheme.Hom.appLE_eq_app]
    exact id
  have : IsAffine (h ⁻¹ᵁ Out.nonzeroLocus (s i)).toScheme := by rw [hV]; exact haff
  have : T.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from pT]; infer_instance
  have : (Out.nonzeroLocus (s i)).toScheme.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (Out.nonzeroLocus (s i)).ι]; infer_instance
  refine isClosedImmersion_of_surjective _ ?_
  rw [morphismRestrict_appTop]
  have h₁ : Function.Surjective (h.app ((Out.nonzeroLocus (s i)).ι ''ᵁ ⊤)).hom := by
    rw [Scheme.Opens.ι_image_top]
    exact hsurj'
  exact (ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom _).op)).2.comp h₁

abbrev pullLB {X Y : Scheme.{0}} (f : Y ⟶ X) (L : LB X) : LB Y :=
  ⟨L.ι, fun l => f ⁻¹ᵁ L.U l, fun l l' => pullU f (L.U l ⊓ L.U l') (L.g l l')⟩

def pullSection {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} (s : L.Sec) : (pullLB f L).Sec where
  f l := (f.app (L.U l)).hom (s.f l)
  compat i j := by
    have e := congrArg (f.app (L.U i ⊓ L.U j)).hom (s.compat i j)
    rw [map_mul] at e
    have e₁ := congrArg (fun φ => φ.hom (s.f i)) (f.naturality (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op)
    have e₂ := congrArg (fun φ => φ.hom (s.f j)) (f.naturality (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op)
    exact e₁.symm.trans (e.trans (congrArg (_ * ·) e₂))

theorem crd_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} {J : Type} (s : J → L.Sec) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y) (v : J → R) : Crd (pullLB f L) (fun j => pullSection f (s j)) x v ↔ Crd L s (x ≫ f) v := by
  refine exists_congr fun l => exists_congr fun c => and_congr Iff.rfl (forall_congr' fun j => ?_)
  rw [GlobalTheory.Points.valR_comp x f]
  rfl

theorem crd_lin {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X} {I J : Type} [Fintype J]
    {s : J → H.Sec} {s' : I → H.Sec} {n : Matrix I J k} (hn : ∀ i, IsLin p s (n i) (s' i)) {x : Sp k ⟶ X}
    (hx : x ≫ p = 𝟙 _) {v : J → k} (hv : Crd H s x v) : Crd H s' x (n.mulVec v) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  refine ⟨l, c, hl, fun i => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hn i l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, GlobalTheory.Points.valR_constFn_of_section p x hx _ hl, hv,
    mul_left_comm]

theorem isClosedImmersion_special_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (f' : t.u.G.left ⟶ Q.G.toScheme), f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι → ∀ h : pullback t.u.G.hom (rPt p ≫ spMap t.u.j) ⟶ pullback (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y), h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f' → h ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion h := by
  intro L o Ω _ _ _ _ S ρ M U₀ EE hbf Q p _ y y₀ t c tm hBig f' hf' h h1 h2
  have : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hB : Big S.g S.N (S.r * S.N) := ⟨(utest_dim_and_split L o Ω S ρ p y₀ t.u).2.2.2.1, hBig.1, hBig.2.1⟩
  have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  have hs : Smooth t.u.G.hom := t.mod.smooth.smooth
  have : Smooth t.mod.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  have : IsReduced t.mod.Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced t.mod.Φ.G.hom
  have := Q.proper
  suffices IsClosedImmersion (pb.isoPullback.hom ≫ h) from
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).1 this
  have hrange : Set.range (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι) ⊆
      Set.range (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have e : (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι ≫ Q.P.hom) z =
        (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ rPt p ≫ y) z := by rw [pullback.condition]
    have e₂ : rPt p (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) z) = cPt p := by
      rw [Subsingleton.elim (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) z) (IsLocalRing.closedPoint (kb p))]
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    change (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι ≫ Q.P.hom) z ∈ Q.W tm.l
    rw [e]
    exact (congrArg (fun w => y w ∈ Q.W tm.l) e₂).mpr tm.mem
  let e := IsOpenImmersion.lift (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι _ hrange
  have he : e ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ Q.G.ι := IsOpenImmersion.lift_fac _ _ _
  let ψ : t.u.V →+* kb p := (IsLocalRing.residue (OO p)).comp t.u.j
  have hψ : rPt p ≫ spMap t.u.j = spMap ψ := (Spec.map_comp _ _).symm
  have hm : IsUnit (tm.m.map ψ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact tm.unit.map ψ
  have hH : (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι).IsLB := DVR.linComb_isLB _ Q.isLB _ _
  have hT := pullChart_isLB e hH
  choose s hs using fun i => (GlobalTheory.SecRatio.existsUnique_isLin (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y))
    (fun j => pullSection e (Q.σ tm.l j)) ((tm.m.map ψ)⁻¹ i)).exists
  have hsnd : (pb.isoPullback.hom ≫ h) ≫ pullback.snd _ _ = t.mod.Φ.G.hom := by
    rw [Category.assoc, h2, IsPullback.isoPullback_hom_snd]
  have hhe : (pb.isoPullback.hom ≫ h) ≫ e = t.mod.r ≫ tm.f := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι, Category.assoc, he, Category.assoc, Category.assoc,
      reassoc_of% h1, hf', IsPullback.isoPullback_hom_fst_assoc]
  refine isClosedImmersion_of_crd t.mod.Φ.G.hom (pullback.snd _ _) _ hsnd (t.mod.Φ.H_isLB 1) hT t.mod.F s _
    (_root_.GlobalTheory.ZH.ClosedImm.immBy_weight_zero L.1 L.2.1 (kb p) t.mod.Φ S.g S.N _ _ S.J _ t.mod.F t.mod.pol hB t.mod.good t.mod.dim) ?_ ?_
  · refine top_le_iff.1 (le_of_points (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y)) fun x hx _ => ?_)
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists hH (Q.σ tm.l) (x ≫ e)
    have hw := crd_lin hs hx ((crd_pull e _ x v).2 hv)
    have hv' : v = (tm.m.map ψ).mulVec ((tm.m.map ψ)⁻¹.mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm, Matrix.one_mulVec]
    rw [hv'] at hv
    obtain ⟨i, hi, hne⟩ := (_root_.GlobalTheory.ZH.TestCrit.le_preimage_G_iff_test o Ω S ρ M U₀ EE hbf Q p y y₀ t c tm hBig (x ≫ e) _ (by
      rw [Category.assoc, reassoc_of% he, pullback.condition, reassoc_of% hx]) hv).1 (by
      rw [Category.assoc, he, ← Category.assoc, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
      exact le_rfl)
    exact ((CrdCalc.crd_isUnit_iff i hw).1 hne.isUnit).trans (x.preimage_mono
      (le_iSup (fun i : {i | t.mod.xe.symm (t.cls i) = 0} => Out.nonzeroLocus (s i))
        ⟨i, t.mod.xe.symm.map_eq_zero_iff.2 hi⟩))
  · intro x v hx hv
    have h₁ := t.mod.red (Over.homMk x hx) v hv
    have h₂ := tm.crd (kb p) ψ (x ≫ t.mod.r) v (by rw [Category.assoc, pb.w, reassoc_of% hx, hψ]) h₁
    rw [Category.assoc, ← hhe, ← Category.assoc] at h₂
    have h₃ := crd_lin hs (by rw [Category.assoc, hsnd, hx]) ((crd_pull e _ _ _).2 h₂)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec] at h₃

end GlobalTheory.ZH.FibreImm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemTorusExtensionConeIffSmallDegreeForms
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.FibCone

theorem hilb_eq_finrank_quotPiece {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (quotPiece (MvPolynomial.vanishingIdeal k C) (d : ℤ)) := by
  rw [quotPiece_natCast]
  let ev : MvPolynomial J k →ₐ[k] (C → k) :=
    AlgHom.pi fun v : C => MvPolynomial.aeval v.1
  have hker : ∀ a ∈ MvPolynomial.vanishingIdeal k C, ev a = 0 := fun a ha =>
    funext fun v => ha v.1 v.2
  let φ := Ideal.Quotient.liftₐ (MvPolynomial.vanishingIdeal k C) ev hker
  have hφ : Function.Injective φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 fun v hv => congrFun (show ev x = 0 from hx) ⟨v, hv⟩
  rw [(Submodule.equivMapOfInjective _ hφ _).finrank_eq, ← Submodule.map_comp]
  rfl

theorem eval_eq_zero_of_hilb_le : (∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J] (C : Set (J → k)) (g N : ℕ), (MvPolynomial.vanishingIdeal k C).IsPrime → (MvPolynomial.vanishingIdeal k C).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) → (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k C) → ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k C) = (g + 1 : ℕ) → (∀ d, 1 ≤ d → hilb C d ≤ (N * d) ^ g) → ∀ v : J → k, (∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → Pf ∈ MvPolynomial.vanishingIdeal k C → MvPolynomial.eval v Pf = 0) → ∀ Pf ∈ MvPolynomial.vanishingIdeal k C, MvPolynomial.eval v Pf = 0) := by
  intro k _ _ J _ C g N hP hPh hne hdim hb v hv Pf hPf
  by_contra h0
  obtain ⟨d, hd, f, hf, hfd, hfv⟩ :=
    exists_form_degree_le_hilbertDegree_eval_ne_zero hPh hne v ⟨Pf, hPf, h0⟩
  refine hfv (hv d f (hd.trans ?_) hfd hf)
  have hH := isHilbertPoly_idealHilbertPoly hPh
  have hg : (idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).natDegree = g := by
    rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hPh hne] at hdim
    have := Nat.cast_injective hdim
    omega
  have h1 : 0 ≤ (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g -
      idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).coeff g := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le (Polynomial.degree_C_mul_X_pow_le _ _) ?_)
      exact Polynomial.degree_le_of_natDegree_le hg.le
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        Filter.eventually_ge_atTop 1] with n hn h1n
      have := hb n h1n
      rw [hilb_eq_finrank_quotPiece, mul_pow] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
        ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, _root_.mul_one,
    sub_nonneg] at h1
  have h2 := cast_hilbertDegree hPh
  rw [Polynomial.leadingCoeff, hg] at h2
  have h3 : (hilbertDegree (MvPolynomial.vanishingIdeal k C) : ℚ) ≤ (N : ℚ) ^ g * g.factorial := by
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  exact_mod_cast h3

theorem isIntegral_G {k : Type} [Field k] (Φ : FibPre k) : IsIntegral Φ.G.left := by
  have h : IsSemiAbelian Φ.G := GlobalTheory.isSemiAbelian_of_isGt _ Φ.E Φ.G ⟨Φ.D⟩
  have := h.smooth
  have := h.geomConnected
  have : GeometricallyIntegral Φ.G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ Φ.G
  exact GeometricallyIntegral.isIntegral_of_subsingleton Φ.G.hom

theorem exists_ne_zero_of_mem_cone {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type}
    (s : J → H.Sec) (J₀ : Set J) (hH : H.IsLB) (hc : ⨆ i ∈ J₀, Out.nonzeroLocus (s i) = ⊤) (v : J → k)
    (hv : v ∈ cone p H s) : ∃ i ∈ J₀, v i ≠ 0 := by
  obtain ⟨x, -, hx⟩ := hv
  let pt : Sp k := IsLocalRing.closedPoint k
  have hm : x pt ∈ (⨆ i ∈ J₀, Out.nonzeroLocus (s i)) := by rw [hc]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, hi, hm⟩ := hm
  refine ⟨i, hi, ?_⟩
  have hu := (((GlobalTheory.ZH.CrdCalc.crd_calculus X H J s hH).1 k x).2.2 v i hx).2 (by
    intro y _
    have : y = pt := Subsingleton.elim (α := PrimeSpectrum k) _ _
    subst this
    exact hm)
  exact hu.ne_zero

theorem mem_cone_iff : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → SmoothOfRelativeDimension g Φ.G.hom → (∀ d, 1 ≤ d → hilb (cone Φ.G.hom (Φ.H 1) F) d ≤ (N * d) ^ g) → ∀ v : J → k, v ∈ cone Φ.G.hom (Φ.H 1) F ↔ ((∃ i, cls i = 0 ∧ v i ≠ 0) ∧ ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ w, Crd (Φ.H 1) F x.left w ∧ MvPolynomial.eval w Pf = 0) → MvPolynomial.eval v Pf = 0)) := by
  intro hL hL2 k _ _ Φ g N N' q J _ cls F π hB hG hg hN hsm hh v
  have hH := Φ.H_isLB 1
  have himm := _root_.GlobalTheory.ZH.ClosedImm.immBy_weight_zero hL hL2 k Φ g N N' q J cls F π hB hG hg
  constructor
  · intro hv
    exact ⟨exists_ne_zero_of_mem_cone _ _ F _ hH himm.1 v hv, fun d Pf hd hP ht =>
      _root_.GlobalTheory.ZH.TorsionVanish.form_vanishes_of_torsion hL hL2 k Φ g N N' q J cls F π hB hG hg hN d Pf hd hP ht v hv⟩
  · rintro ⟨h0, hv⟩
    obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.ZH.ConePrime.isPrime_vanishingIdeal_cone k _ Φ.G.hom (Φ.H 1) J F _ hH himm (isIntegral_G Φ) g hsm
    refine GlobalTheory.ZH.ConeClosed.mem_cone_of_vanishing k _ Φ.G.hom (Φ.H 1) J F _ hH himm v h0 ?_
    refine eval_eq_zero_of_hilb_le k J _ g N h1 h2 h3 h4 hh v fun d Pf hd hP hI => hv d Pf hd hP ?_
    intro x _
    obtain ⟨w, hw⟩ := ((GlobalTheory.ZH.CrdCalc.crd_calculus _ (Φ.H 1) J F hH).1 k x.left).1
    refine ⟨w, hw, ?_⟩
    have := (MvPolynomial.mem_vanishingIdeal_iff.1 hI) w ⟨x.left, Over.w x, hw⟩
    simpa [MvPolynomial.aeval_eq_eval] using this

end GlobalTheory.ZH.FibCone
end

