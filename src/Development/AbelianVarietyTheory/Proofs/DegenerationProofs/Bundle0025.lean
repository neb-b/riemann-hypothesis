module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Lean.Elab.Command

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsOpenImmersionOfSections
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.CompatCrit

theorem section_open {G X V : Scheme.{0}} [IsReduced G] (p : G ⟶ X) [IsSeparated p] (s : V ⟶ G)
    [IsDominant s] [IsOpenImmersion (s ≫ p)] :
    IsOpenImmersion s ∧ ∀ x : G, p x ∈ Set.range (s ≫ p) → x ∈ Set.range s := by
  let t : V ⟶ pullback p (s ≫ p) := pullback.lift s (𝟙 V) (by simp)
  have h1 : t ≫ pullback.fst p (s ≫ p) = s := pullback.lift_fst _ _ _
  have h2 : t ≫ pullback.snd p (s ≫ p) = 𝟙 V := pullback.lift_snd _ _ _
  have : IsClosedImmersion (t ≫ pullback.snd p (s ≫ p)) := by rw [h2]; infer_instance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t (pullback.snd p (s ≫ p))
  have : IsDominant (t ≫ pullback.fst p (s ≫ p)) := by rw [h1]; infer_instance
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t (pullback.fst p (s ≫ p))
  have : Surjective t := surjective_of_isDominant_of_isClosed_range t t.isClosedEmbedding.isClosed_range
  have : IsReduced (pullback p (s ≫ p)) := isReduced_of_isOpenImmersion (pullback.fst p (s ≫ p))
  have : IsIso t := isIso_of_isClosedImmersion_of_surjective t
  refine ⟨by rw [← h1]; infer_instance, fun x hx => ?_⟩
  have hx' : x ∈ Set.range (pullback.fst p (s ≫ p)) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨v, rfl⟩ := t.surjective y
  exact ⟨v, by rw [← Scheme.Hom.comp_apply, h1]⟩

theorem isOpenImmersion_of_sections {G X : Scheme.{0}} [IsReduced G] (p : G ⟶ X) [IsSeparated p]
    (h : ∀ x : G, ∃ (V : Scheme.{0}) (s : V ⟶ G), IsDominant s ∧ IsOpenImmersion (s ≫ p) ∧ x ∈ Set.range s) :
    IsOpenImmersion p := by
  refine IsOpenImmersion.of_forall_source_exists p (fun x y hxy => ?_) (fun x => ?_)
  · obtain ⟨V, s, _, _, u, rfl⟩ := h x
    obtain ⟨v, rfl⟩ := (section_open p s).2 y ⟨u, by rw [← hxy, Scheme.Hom.comp_apply]⟩
    have : u = v := (s ≫ p).isOpenEmbedding.injective (by simpa using hxy)
    rw [this]
  · obtain ⟨V, s, _, _, hx⟩ := h x
    exact ⟨V, s, (section_open p s).1, hx, inferInstance⟩

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : IsPullback M.e.inv.left A.hom (pullback.snd M.Y.hom (spMap (algebraMap R K))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w M.e.inv⟩
  simpa [Model.j] using h.paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))

theorem exists_model (M : Model R A) {G : Scheme.{0}} (p : G ⟶ M.Y.left) [IsOpenImmersion p]
    [QuasiCompact p] (i : A.left ⟶ G) (hi : i ≫ p = M.j) :
    ∃ e : (Over.pullback (spMap (algebraMap R K))).obj (Over.mk (p ≫ M.Y.hom)) ≅ A,
      e.inv.left ≫ pullback.fst (p ≫ M.Y.hom) (spMap (algebraMap R K)) = i := by
  have h : IsPullback i (𝟙 _) p M.j := IsPullback.of_vert_isIso_mono ⟨by simp [hi]⟩
  have h' := h.paste_vert (isPullback_j M)
  rw [Category.id_comp] at h'
  exact ⟨(Over.isoMk h'.isoPullback (by simp)).symm, by simp⟩

theorem mem_range_j [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A)
    (y : M.Y.left) (hy : y ∉ M.sp) : y ∈ Set.range M.j := by
  have h1 : (M.Y.hom y : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R K)) := by
    rw [PrimeSpectrum.localization_comap_range K (nonZeroDivisors R)]
    have hb : (M.Y.hom y : PrimeSpectrum R).asIdeal = ⊥ := by
      by_contra hb
      exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        ((M.Y.hom y : PrimeSpectrum R).isPrime.isMaximal hb)))
    show Disjoint _ _
    rw [hb, Set.disjoint_left]
    intro a ha ha'
    exact nonZeroDivisors.ne_zero ha ha'
  obtain ⟨t, ht⟩ := h1
  obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) y t ht.symm
  exact ⟨a, ha⟩

end GlobalTheory.SS.CompatCrit

namespace GlobalTheory.SS
open CompatCrit

theorem compat_of_isoAt_closure : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [IsIntegral A.left] (M N : Model R A) (δ : A.left ⟶ (M.Y ⊗ N.Y).left), δ ≫ (fst M.Y N.Y).left = M.j → δ ≫ (snd M.Y N.Y).left = N.j → (∀ z ∈ closure (Set.range δ), IsClosed {z} → (fst M.Y N.Y).left z ∈ M.sp → IsoAt M N (𝟙 A) ((fst M.Y N.Y).left z)) → Compat M N := by
  intro R K _ _ _ _ _ ⟨hD, _, _, hF⟩ A _ M N δ h₁ h₂ H
  have := M.smooth; have := M.sep; have := M.qc; have := N.smooth; have := N.sep; have := N.qc
  have : IsOpenImmersion (spMap (algebraMap R K)) := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    (schemeDominant_specMap_iff _).2 (IsFractionRing.injective R K)
  have jM : IsOpenImmersion M.j := MorphismProperty.of_isPullback (isPullback_j M).flip ‹_›
  have jN : IsOpenImmersion N.j := MorphismProperty.of_isPullback (isPullback_j N).flip ‹_›
  have qM : QuasiCompact M.j := MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_j M).flip inferInstance
  have dM : IsSchemeTheoreticallyDominant M.j := .of_isPullback (isPullback_j M).flip
  have s₁ : IsSeparated (fst M.Y N.Y).left := inferInstanceAs (IsSeparated (pullback.fst M.Y.hom N.Y.hom))
  have s₂ : IsSeparated (snd M.Y N.Y).left := inferInstanceAs (IsSeparated (pullback.snd M.Y.hom N.Y.hom))
  have c₁ : QuasiCompact (fst M.Y N.Y).left := inferInstanceAs (QuasiCompact (pullback.fst M.Y.hom N.Y.hom))
  have : QuasiCompact (δ ≫ (fst M.Y N.Y).left) := by rw [h₁]; infer_instance
  have qδ : QuasiCompact δ := QuasiCompact.of_comp δ (fst M.Y N.Y).left
  have : IsReduced δ.image := IsSchemeTheoreticallyDominant.isReduced δ.toImage
  let p := δ.imageι ≫ (fst M.Y N.Y).left
  let q := δ.imageι ≫ (snd M.Y N.Y).left
  have hp : δ.toImage ≫ p = M.j := (δ.toImage_imageι_assoc _).trans h₁
  have hq : δ.toImage ≫ q = N.j := (δ.toImage_imageι_assoc _).trans h₂
  have : CompactSpace M.Y.left := QuasiCompact.compactSpace_of_compactSpace M.Y.hom
  have : CompactSpace δ.image := QuasiCompact.compactSpace_of_compactSpace p
  let S : Set δ.image := {x | ∃ (V : Scheme.{0}) (s : V ⟶ δ.image), IsDominant s ∧ IsOpenImmersion (s ≫ p) ∧
    IsOpenImmersion (s ≫ q) ∧ x ∈ Set.range s}
  have hSo : IsOpen S := by
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro x ⟨V, s, a, b, c, hx⟩
    have := (section_open p s).1
    exact ⟨Set.range s, fun y hy => ⟨V, s, a, b, c, hy⟩, s.isOpenEmbedding.isOpen_range, hx⟩
  have hS : ∀ x, x ∈ S := by
    by_contra hne
    obtain ⟨x, hx, hc⟩ := hSo.isClosed_compl.exists_closed_singleton (not_forall.1 hne)
    apply hx
    by_cases hsp : p x ∈ M.sp
    · have hz : δ.imageι x ∈ closure (Set.range δ) := by
        have h := image_closure_subset_closure_image δ.imageι.continuous
          ⟨x, δ.toImage.denseRange x, rfl⟩
        refine closure_mono ?_ h
        rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]⟩
      have hcz : IsClosed {δ.imageι x} := by
        simpa using δ.imageι.isClosedEmbedding.isClosedMap _ hc
      obtain ⟨U, g, hU, ⟨e₁, e₂⟩, hg⟩ := H _ hz hcz hsp
      let t : U.toScheme ⟶ (M.Y ⊗ N.Y).left := pullback.lift U.ι g e₁.symm
      have t₁ : t ≫ (fst M.Y N.Y).left = U.ι := pullback.lift_fst _ _ _
      have t₂ : t ≫ (snd M.Y N.Y).left = g := pullback.lift_snd _ _ _
      have : IsSchemeTheoreticallyDominant (M.j ∣_ U) := .of_isPullback (isPullback_morphismRestrict M.j U).flip
      have hw : (M.j ∣_ U) ≫ t = (M.j ⁻¹ᵁ U).ι ≫ δ := by
        refine pullback.hom_ext ?_ ?_
        · change ((M.j ∣_ U) ≫ t) ≫ (fst M.Y N.Y).left = (_ ≫ δ) ≫ (fst M.Y N.Y).left
          rw [Category.assoc, Category.assoc, t₁, h₁, morphismRestrict_ι]
        · change ((M.j ∣_ U) ≫ t) ≫ (snd M.Y N.Y).left = (_ ≫ δ) ≫ (snd M.Y N.Y).left
          rw [Category.assoc, Category.assoc, t₂, h₂, e₂]; simp
      let s := closureLift δ t (M.j ∣_ U) _ hw
      have sp : s ≫ p = U.ι := (closureLift_imageι_assoc δ t _ _ hw _).trans t₁
      have sq : s ≫ q = g := (closureLift_imageι_assoc δ t _ _ hw _).trans t₂
      have : IsDominant (M.j ⁻¹ᵁ U).ι := ⟨by
        rw [DenseRange, Scheme.Opens.range_ι]
        refine (M.j ⁻¹ᵁ U).isOpen.dense ?_
        obtain ⟨a, ha⟩ := M.j.denseRange.exists_mem_open U.isOpen ⟨_, hU⟩
        exact ⟨a, ha⟩⟩
      have : IsDominant ((M.j ∣_ U) ≫ s) := by
        simp only [s, comp_closureLift]; infer_instance
      have ds : IsDominant s := IsDominant.of_comp (M.j ∣_ U) s
      have op : IsOpenImmersion (s ≫ p) := by rw [sp]; infer_instance
      refine ⟨_, s, ds, op, by rw [sq]; exact hg, (section_open p s).2 x ?_⟩
      rw [sp, Scheme.Opens.range_ι]
      exact hU
    · have op : IsOpenImmersion (δ.toImage ≫ p) := by rw [hp]; exact jM
      refine ⟨_, δ.toImage, inferInstance, op, by rw [hq]; exact jN, (section_open p _).2 x ?_⟩
      rw [hp]
      exact mem_range_j M _ hsp
  have op : IsOpenImmersion p := isOpenImmersion_of_sections p fun x => by
    obtain ⟨V, s, a, b, -, hx⟩ := hS x
    exact ⟨V, s, a, b, hx⟩
  have oq : IsOpenImmersion q := isOpenImmersion_of_sections q fun x => by
    obtain ⟨V, s, a, -, c, hx⟩ := hS x
    exact ⟨V, s, a, c, hx⟩
  obtain ⟨e, he⟩ := exists_model M p δ.toImage hp
  let W : Model R A := ⟨Over.mk (p ≫ M.Y.hom), e, inferInstanceAs (Smooth (p ≫ M.Y.hom)),
    inferInstanceAs (IsSeparated (p ≫ M.Y.hom)), inferInstanceAs (QuasiCompact (p ≫ M.Y.hom))⟩
  have hW : W.j = δ.toImage := he
  let i : W.Y ⟶ M.Y ⊗ N.Y := Over.homMk δ.imageι (by simp [W, p])
  refine ⟨W, i ≫ fst _ _, i ≫ snd _ _, op, oq, ?_, ?_, ?_⟩
  · rw [hW]; exact hp
  · rw [hW]; exact hq
  · rw [lift_comp_fst_snd]
    exact inferInstanceAs (IsClosedImmersion δ.imageι)

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PartVanishesOnTorusTorsionFourier
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorsionFourier

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens}

theorem valF_sum (h : ⊤ ≤ x ⁻¹ᵁ U) {J : Type} (A : Finset J) (a : J → Γ(X, U)) :
    valF x U (∑ j ∈ A, a j) = ∑ j ∈ A, valF x U (a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [valF, dif_pos h, map_sum]

theorem valF_ne_zero_iff_le (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  rw [e3]
  constructor
  · intro hne
    exact (Scheme.basicOpen_of_isUnit _ ((Ne.isUnit hne).map _)).ge
  · intro hle h0
    rw [h0, map_zero, Scheme.basicOpen_zero] at hle
    exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem le_nonzeroLocus_iff {H : LB X} (s : H.Sec) (x : Sp F ⟶ X) :
    ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s ↔ ∃ l, ⊤ ≤ x ⁻¹ᵁ H.U l ∧ valF x (H.U l) (s.f l) ≠ 0 := by
  constructor
  · intro h
    have hp : x (IsLocalRing.closedPoint F) ∈ Out.nonzeroLocus s :=
      h (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    have h1 : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (s.f l) := by
      intro y _
      have : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
      subst this
      exact hl
    have h2 : ⊤ ≤ x ⁻¹ᵁ H.U l := h1.trans (Scheme.Hom.preimage_mono x (X.basicOpen_le _))
    exact ⟨l, h2, (valF_ne_zero_iff_le h2 _).2 h1⟩
  · rintro ⟨l, h2, hne⟩
    exact ((valF_ne_zero_iff_le h2 _).1 hne).trans
      (Scheme.Hom.preimage_mono x (le_iSup (fun k => X.basicOpen (s.f k)) l))

end Val

theorem part_vanishes_on_torsion : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (d n : ℕ), (n : k) ≠ 0 → ∀ φ : (Φ.H d).Sec, (∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + n • w) → α = β) → (∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ α ψ, Φ.IsPart α φ ψ → ∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus ψ) := by
  intro k _ _ Φ d n hn φ hinc hφ α ψ hψ x hx hle
  classical
  obtain ⟨hex, hfin, hext, hsum⟩ := GlobalTheory.ZH.WtPart.weight_parts k Φ d
  obtain ⟨l, hl, hne⟩ := (le_nonzeroLocus_iff (F := k) ψ x.left).1 hle
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have : NeZero (n : k) := ⟨hn⟩
  have : NeZero n := ⟨hn0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n

  have hα : α ∈ Φ.supp φ := by
    by_contra hα
    apply hne
    have h0 : ψ.f l = ∑ β ∈ (∅ : Finset Φ.E.X), ((fun _ => ψ) β).f l := by
      refine hsum ψ ∅ (fun _ => ψ) ?_ (fun β hβ => absurd hβ (Finset.notMem_empty β)) l
      rintro β ⟨l', hl'⟩
      have e : β = α := hψ.1 ⟨l', hl'⟩
      subst e
      exact absurd ⟨l', by rwa [← hψ.2 l']⟩ hα
    refine (congrArg (valF (F := k) x.left _) h0).trans ((valF_sum (F := k) hl _ _).trans ?_)
    exact Finset.sum_empty
  choose p hp using hex φ
  let p' : Φ.E.X → (Φ.H d).Sec := fun β => if β = α then ψ else p β
  have hp' : ∀ β, Φ.IsPart β φ (p' β) := fun β => by
    by_cases h : β = α
    · subst h
      simpa only [p', if_pos rfl] using hψ
    · simpa only [p', if_neg h] using hp β
  let A : Finset Φ.E.X := (hfin φ).toFinset
  have hA : ∀ β, β ∈ A ↔ β ∈ Φ.supp φ := fun β => (hfin φ).mem_toFinset
  let v : Φ.E.X → k := fun β => valF (F := k) x.left ((Φ.H d).U l) ((p' β).f l)
  let c : Φ.E.X →₀ k := Finsupp.indicator A fun β _ => v β
  have hcs : c.support ⊆ A := Finsupp.support_indicator_subset _ _
  have hc : c = 0 := by
    refine GlobalTheory.finsupp_eq_zero_of_sum_torsion_characters_eq_zero k Φ.E.X n ζ (Nat.pos_of_ne_zero hn0) hζ k c
      (fun a ha b hb => hinc a ((hA a).1 (hcs ha)) b ((hA b).1 (hcs hb))) fun t ht => ?_
    obtain ⟨a, -, ha, hat⟩ := GlobalTheory.TorusTranslate.exists_point_translate_pure k Φ t
    have hax : (a * x) ^ n = 1 := by
      rw [mul_pow, ha n ht, hx, _root_.one_mul]
    have hl' := (hat d α ψ hψ.1 x l hl).1
    have h0 : valF (F := k) (a * x).left ((Φ.H d).U l) (φ.f l) = 0 := by
      by_contra h
      exact hφ _ hax ((le_nonzeroLocus_iff (F := k) φ (a * x).left).2 ⟨l, hl', h⟩)
    rw [Finsupp.sum_of_support_subset c hcs _ (fun _ _ => smul_zero _), ← h0]
    have h1 := hsum φ A p' (fun β hβ => (hA β).2 hβ) (fun β _ => hp' β) l
    refine Eq.trans ?_ ((congrArg (valF (F := k) (a * x).left _) h1).trans (valF_sum (F := k) hl' _ _)).symm
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [Finsupp.indicator_of_mem hβ]
    exact (hat d β (p' β) (hp' β).1 x l hl).2.symm
  have h2 : c α = v α := Finsupp.indicator_of_mem ((hA α).2 hα) _
  apply hne
  have h3 : v α = 0 := by rw [← h2, hc]; rfl
  have h4 : p' α = ψ := if_pos rfl
  rw [← h4]
  exact h3

end GlobalTheory.TorsionFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeron
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem isIrreducible_fibre_pullback {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f]
    {k : Type} [Field k] [IsAlgClosed k] (i : Spec (.of k) ⟶ S) [IsClosedImmersion i]
    (hf : IsIrreducible (f ⁻¹' Set.range i)) (hg : IsIrreducible (g ⁻¹' Set.range i)) :
    IsIrreducible ((pullback.fst f g ≫ f) ⁻¹' Set.range i) := by
  have irr : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsIrreducible (f ⁻¹' Set.range i) →
      IrreducibleSpace ↥(pullback f i) := by
    intro X f h
    rw [← Scheme.Pullback.range_fst] at h
    have e := (pullback.fst f i).isClosedEmbedding.isEmbedding
    have := Subtype.irreducibleSpace h
    exact e.toHomeomorph.irreducibleSpace_iff.2 this
  have h1 := irr f hf
  have h2 := irr g hg
  have h3 : GeometricallyIrreducible (pullback.snd f i) := geometricallyIrreducible_of_isAlgClosed _
  have h4 : IrreducibleSpace ↥(pullback (pullback.snd f i) (pullback.snd g i)) := inferInstance
  let m := pullback.map (pullback.snd f i) (pullback.snd g i) f g (pullback.fst f i) (pullback.fst g i) i
    pullback.condition.symm pullback.condition.symm
  have hm : Set.range m = (pullback.fst f g ≫ f) ⁻¹' Set.range i := by
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
    ext z
    have hz : g (pullback.snd f g z) = f (pullback.fst f g z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Scheme.Hom.comp_apply, hz, and_self]
  rw [← hm, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ m.continuous.continuousOn

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem Model.j_comp_of_comm (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map g = f ≫ N.e.inv) :
    M.j ≫ g.left = f.left ≫ N.j := by
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  unfold Model.j
  rw [Category.assoc]
  exact (congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2

theorem Model.prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j :=
  Model.j_comp_of_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])

theorem Model.prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j :=
  Model.j_comp_of_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])

theorem Model.sp_eq_preimage [IsLocalRing R] (M : Model R A) :
    M.sp = M.Y.hom ⁻¹' Set.range (spMap (IsLocalRing.residue R)) := by
  have : Set.range (spMap (IsLocalRing.residue R)) = {IsLocalRing.closedPoint R} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint _)]
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩
  rw [this]; rfl

theorem Model.Irr.prod [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] {M : Model R A} {N : Model R A'}
    (hM : M.Irr) (hN : N.Irr) : (M.prod N).Irr := by
  have := M.smooth
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  unfold Model.Irr at *
  rw [Model.sp_eq_preimage] at *
  exact isIrreducible_fibre_pullback M.Y.hom N.Y.hom (spMap (IsLocalRing.residue R)) hM hN

theorem WeakNeron.prod [IsLocalRing R] {I I' : Type} {M : I → Model R A} {N : I' → Model R A'}
    (hM : WeakNeron M) (hN : WeakNeron N) : WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by
  intro R' K' _ _ _ _ _ _ _ hm a ha
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' hm (a ≫ (fst A A').left) (by
    rw [Category.assoc, ← ha, ← Over.w (fst A A'), Category.assoc])
  obtain ⟨i', c, hc, hc'⟩ := hN R' K' hm (a ≫ (snd A A').left) (by
    rw [Category.assoc, ← ha, ← Over.w (snd A A'), Category.assoc])
  have e1 := Model.prod_j_fst (M i) (N i')
  have e2 := Model.prod_j_snd (M i) (N i')
  refine ⟨(i, i'), pullback.lift (f := (M i).Y.hom) (g := (N i').Y.hom) b c (hb.trans hc.symm), ?_, ?_⟩
  · exact (pullback.lift_fst_assoc _ _ _ _).trans hb
  · refine pullback.hom_ext (f := (M i).Y.hom) (g := (N i').Y.hom) ?_ ?_
    · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
      refine (congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (hb'.trans ?_)
      exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) e1.symm)
    · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
      refine (congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans (hc'.trans ?_)
      exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) e2.symm)

theorem prod_irr_and_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' : Over (Sp K)), (∀ (M : Model R A) (N : Model R A'), M.Irr → N.Irr → (M.prod N).Irr) ∧ ∀ (I I' : Type) (M : I → Model R A) (N : I' → Model R A'), WeakNeron M → WeakNeron N → WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by
  intro R K _ _ _ _ _ h A A'
  have := h.2.2.1
  exact ⟨fun _ _ hM hN => hM.prod hN, fun _ _ _ _ hM hN => hM.prod hN⟩

end GlobalTheory.SS
end

