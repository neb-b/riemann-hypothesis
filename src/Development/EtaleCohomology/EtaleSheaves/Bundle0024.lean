module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0010
public import Development.EtaleCohomology.EtaleSheaves.Bundle0016
public import Development.EtaleCohomology.EtaleSheaves.Bundle0017
public import Development.EtaleCohomology.EtaleSheaves.Bundle0009
public import Development.EtaleCohomology.EtaleSheaves.Bundle0019

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibClosedPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf

namespace LateralTheory.E.FibClosedPf

abbrev fm {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    pullback (c ≫ p) (cpt A) ⟶ pullback p (cpt A) :=
  pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp)

def FibQCQS : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A))
  [QuasiCompact c] [QuasiSeparated c], QuasiCompact (fm c p) ∧ QuasiSeparated (fm c p)

def FibStalk : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  ∀ s : (pullback p (cpt A) : Scheme.{0}),
    Eqv _ (sch.map (pullback.map (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s) (𝟙 _)
      ((pullback p (cpt A)).fromSpecStalk s) (fm c p) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)

theorem FibClosed_of (hZ : ZLG) (h0 : HZero) (hA : AICAcyc) (hQ : FibQCQS) (hS : FibStalk) : FibClosed := by
  intro H q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB
  obtain ⟨_, _⟩ := hQ A c p
  obtain ⟨_, _⟩ := qcqs_of (pullback.snd p (cpt A))
  have hu : IsUnit (q : Γ(pullback p (cpt A), ⊤)) := unit_of hq (pullback.fst p (cpt A) ≫ p)
  exact hZ H q (fm c p) (𝟙 _) hu i (hS H h0 hA q i A hq c p hZs hSs hB)

theorem fm_isPullback {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    IsPullback (fm c p) (pullback.fst (c ≫ p) (cpt A)) (pullback.fst p (cpt A)) c := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p (cpt A)) (h₂₂ := p) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback p (cpt A)).flip
  have e : fm c p ≫ pullback.snd p (cpt A) = pullback.snd (c ≫ p) (cpt A) := by
    unfold fm; rw [pullback.map]; erw [pullback.lift_snd]; simp
  rw [e]
  exact (IsPullback.of_hasPullback (c ≫ p) (cpt A)).flip

theorem fibQCQS : FibQCQS := by
  intro A _ _ Z S c p _ _
  exact ⟨MorphismProperty.of_isPullback (P := @QuasiCompact) (fm_isPullback c p).flip ‹_›,
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (fm_isPullback c p).flip ‹_›⟩

end LateralTheory.E.FibClosedPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibCovPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.FibCovPf

open LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

theorem qaic_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : QAIC q W') : QAIC q W := by
  obtain ⟨B, i1, i2, I, hB, hq, ⟨e'⟩⟩ := h
  exact ⟨B, i1, i2, I, hB, hq, ⟨e ≪≫ e'⟩⟩

theorem qaic_empty (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (hB : AIC B) (hq : IsUnit (q : B))
    {W : Scheme.{0}} [IsEmpty W] : QAIC q W := by
  have : Subsingleton (B ⧸ (⊤ : Ideal B)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have : IsEmpty (Spec (CommRingCat.of (B ⧸ (⊤ : Ideal B)))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum (B ⧸ (⊤ : Ideal B))))
  exact ⟨B, inferInstance, inferInstance, ⊤, hB, hq, ⟨isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty⟩⟩

theorem qaic_good (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) (B0 : Type) [CommRing B0]
    [IsDomain B0] (hB0 : AIC B0) (hq0 : IsUnit (q : B0)) {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A))
    (hw : Good w) : QAIC q (pullback w (cpt A)) := by
  rcases hw with hE | ⟨B, i1, i2, i3, hB, e, he⟩
  · have : IsEmpty ↥(pullback w (cpt A) : Scheme.{0}) := ⟨fun x => hE.elim ((pullback.fst w (cpt A)).base x)⟩
    exact qaic_empty q B0 hB0 hq0
  · subst he
    refine ⟨B, i1, i2, (IsLocalRing.maximalIdeal A).map (algebraMap A B), hB, ?_, ?_⟩
    · simpa using hq.map (algebraMap A B)
    · obtain ⟨e2⟩ := fibre_affine A B
      exact ⟨(pullbackRightPullbackFstIso _ (cpt A) e.hom).symm ≪≫ asIso (pullback.snd e.hom _) ≪≫ e2⟩

theorem exists_absolutely_integrally_closed_domain_with_q_unit (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A)) {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (hZ : AICSch Z) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B), AIC B ∧ IsUnit (q : B) := by
  obtain ⟨hI, hA⟩ := hZ
  obtain ⟨x⟩ : Nonempty Z := hI.nonempty
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : Z.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨Γ(Z, U), inferInstance, IsIntegral.component_integral U, hA U hU ⟨x, hxU⟩, ?_⟩
  have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appLE ⊤ U le_top).hom
  simpa using this

theorem FibCov_of : FibCov := by
  intro q A _ _ hq Z p hZ U V f g _ _ hc hU hV hW
  obtain ⟨B0, _, _, hB0, hq0⟩ := exists_absolutely_integrally_closed_domain_with_q_unit q A hq p hZ
  refine ⟨pullback f (pullback.fst p (cpt A)), pullback g (pullback.fst p (cpt A)),
    pullback.snd f (pullback.fst p (cpt A)), pullback.snd g (pullback.fst p (cpt A)),
    inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, ← Set.preimage_union, hc, Set.preimage_univ]
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) f) (qaic_good q A hq B0 hB0 hq0 _ hU)
  · exact qaic_of_iso (pullbackRightPullbackFstIso p (cpt A) g) (qaic_good q A hq B0 hB0 hq0 _ hV)
  · refine qaic_of_iso ?_ (qaic_good q A hq B0 hB0 hq0 _ hW)
    exact pullbackLeftPullbackSndIso f (pullback.fst p (cpt A)) (pullback.snd g (pullback.fst p (cpt A))) ≪≫
      pullback.congrHom rfl pullback.condition.symm ≪≫
      (pullbackLeftPullbackSndIso f g (pullback.fst g (pullback.fst p (cpt A)))).symm ≪≫
      pullbackRightPullbackFstIso g (pullback.fst p (cpt A)) (pullback.snd f g) ≪≫
      pullback.congrHom pullback.condition.symm rfl ≪≫
      pullbackRightPullbackFstIso p (cpt A) (pullback.fst f g ≫ f) ≪≫
      pullback.congrHom (Category.assoc _ _ _) rfl

end LateralTheory.E.FibCovPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FibMapRange
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FiberCover
open LateralTheory.E.LineOneCut

lemma fibMap_eq {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fibMap p ι = (pullbackRightPullbackFstIso p (cpt A) ι).inv ≫ pullback.snd ι (pullback.fst p (cpt A)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]; exact pullback.lift_fst _ _ _
  · rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
    simp [fibMap]

lemma fibMap_open {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z)
    [IsOpenImmersion ι] : IsOpenImmersion (fibMap p ι) := by
  rw [fibMap_eq]; infer_instance

lemma fibMap_range {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    Set.range (fibMap p ι) = (pullback.fst p (cpt A)) ⁻¹' Set.range ι := by
  rw [fibMap_eq, ← Scheme.Pullback.range_snd]
  ext x; constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(pullbackRightPullbackFstIso p (cpt A) ι).hom y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem FibCover_of : FibCover := by
  intro A _ _ Z U V p ι₁ ι₂ h1 h2 hcov
  refine ⟨fibMap_open p ι₁, fibMap_open p ι₂, ?_⟩
  rw [fibMap_range, fibMap_range, ← Set.preimage_union, hcov, Set.preimage_univ]

end LateralTheory.E.FiberCover
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FiltGenPf
section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.FiltGenPf

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma ofHom_comp_fromSingleMk {X Y : C} {I : CochainComplex C ℤ} (k : ℤ) (h : X ⟶ Y) {q m : ℤ}
    (g : Y ⟶ I.X q) (hq : k + m = q) :
    (Cochain.ofHom ((singleFunctor C k).map h)).comp
      (Cochain.fromSingleMk (p := k) g hq) (zero_add m) = Cochain.fromSingleMk (p := k) (h ≫ g) hq := by
  ext p q' hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  by_cases hp : p = k
  · subst hp
    obtain rfl : q' = q := by lia
    rw [Cochain.fromSingleMk_v, Cochain.fromSingleMk_v]
    change ((HomologicalComplex.single C (ComplexShape.up ℤ) p).map h).f p ≫ _ = _
    simp [HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

lemma smul_fromSingleMk {X : C} {I : CochainComplex C ℤ} (k : ℤ) (ε : ℤˣ) {q m : ℤ}
    (g : X ⟶ I.X q) (hq : k + m = q) :
    ε • Cochain.fromSingleMk (p := k) g hq = Cochain.fromSingleMk (p := k) (ε • g) hq := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h <;> simp

lemma desc_eta {K L I : CochainComplex C ℤ} (φ : K ⟶ L) {m n : ℤ} (hmn : m + 1 = n)
    (c : Cochain (mappingCone φ) I n) :
    c = mappingCone.descCochain φ ((mappingCone.inl φ).comp c (by lia))
      ((Cochain.ofHom (mappingCone.inr φ)).comp c (zero_add n)) hmn := by
  rw [mappingCone.ext_cochain_from_iff φ m n hmn]
  simp

lemma δ_desc_fromSingle {X Y : C} {I : CochainComplex C ℤ} (k : ℤ) (h : X ⟶ Y) {m m' qa qb qc : ℤ}
    (hm : m + 1 = m') (a : X ⟶ I.X qa) (b : Y ⟶ I.X qb) (ha : k + (m - 1) = qa) (hb : k + m = qb)
    (hc : k + m' = qc) :
    δ m m' (mappingCone.descCochain ((singleFunctor C k).map h) (Cochain.fromSingleMk a ha)
      (Cochain.fromSingleMk b hb) (by lia)) =
    mappingCone.descCochain ((singleFunctor C k).map h)
      (Cochain.fromSingleMk (a ≫ I.d qa qb + m'.negOnePow • (h ≫ b)) hb)
      (Cochain.fromSingleMk (b ≫ I.d qb qc) hc) (by lia) := by
  rw [mappingCone.δ_descCochain _ _ _ _ m' hm, Cochain.δ_fromSingleMk _ _ m qb hb,
    Cochain.δ_fromSingleMk _ _ m' qc hc, ofHom_comp_fromSingleMk, smul_fromSingleMk,
    ← Cochain.fromSingleMk_add]
  rfl

lemma level_of {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hk : Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n))
    (f : K.X k ⟶ I.X (k + (n - 1))) (g : L.X k ⟶ I.X (k + n))
    (hg : g ≫ I.d (k + n) (k + (n + 1)) = 0)
    (hf : f ≫ I.d (k + (n - 1)) (k + n) + (n + 1).negOnePow • (φ.f k ≫ g) = 0) :
    ∃ (a : K.X k ⟶ I.X (k + (n - 1 - 1))) (b : L.X k ⟶ I.X (k + (n - 1))),
      f = a ≫ I.d _ _ + n.negOnePow • (φ.f k ≫ b) ∧ g = b ≫ I.d _ _ := by
  have hk' : Subsingleton (CohomologyClass (mappingCone ((singleFunctor C k).map (φ.f k))) I n) := hk
  let w : Cochain (mappingCone ((singleFunctor C k).map (φ.f k))) I n := mappingCone.descCochain ((singleFunctor C k).map (φ.f k))
    (Cochain.fromSingleMk f (show k + (n - 1) = k + (n - 1) from rfl))
    (Cochain.fromSingleMk g (show k + n = k + n from rfl)) (by lia)
  have hw : δ n (n + 1) w = 0 := by
    simp only [w]
    rw [δ_desc_fromSingle k (φ.f k) rfl f g rfl rfl rfl, hf, hg]
    simp [mappingCone.descCochain]
  have h0 := Subsingleton.elim (CohomologyClass.mk (Cocycle.mk w (n + 1) rfl hw)) 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by lia)] at h0
  obtain ⟨c, hc⟩ := h0
  obtain ⟨a, ha⟩ := Cochain.fromSingleMk_surjective
    ((mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp c (show -1 + (n - 1) = n - 1 - 1 by lia)) (k + (n - 1 - 1)) rfl
  obtain ⟨b, hb⟩ := Cochain.fromSingleMk_surjective
    ((Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp c (zero_add (n - 1))) (k + (n - 1)) rfl
  rw [desc_eta ((singleFunctor C k).map (φ.f k)) (show n - 1 - 1 + 1 = n - 1 by lia) c, ← ha, ← hb,
    δ_desc_fromSingle k (φ.f k) (show n - 1 + 1 = n by lia) a b (by lia) rfl rfl] at hc
  refine ⟨a, b, ?_, ?_⟩
  · have := congrArg (fun x => (mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp x (show -1 + n = n - 1 by lia)) hc
    simp only [w, Cocycle.mk_coe, mappingCone.inl_descCochain] at this
    have := congrArg (Cochain.fromSingleEquiv (show k + (n - 1) = k + (n - 1) from rfl)) this
    simpa using this.symm
  · have := congrArg (fun x => (Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp x (zero_add n)) hc
    simp only [w, Cocycle.mk_coe, mappingCone.inr_descCochain] at this
    have := congrArg (Cochain.fromSingleEquiv (show k + n = k + n from rfl)) this
    simpa using this.symm

lemma δ_desc {K L I : CochainComplex C ℤ} (φ : K ⟶ L) {m n n' : ℤ} (h : m + 1 = n) (hn' : n + 1 = n')
    (α : Cochain K I m) (β : Cochain L I n) :
    δ n n' (mappingCone.descCochain φ α β h) = mappingCone.descCochain φ
      (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) (by omega) :=
  mappingCone.δ_descCochain φ α β h n' hn'

def V {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ) (z : Cochain (mappingCone φ) I n) : Prop :=
  (∀ p q (hpq : p + (n - 1) = q), k < p →
    ((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v p q hpq = 0) ∧
  (∀ p q (hpq : p + n = q), k < p →
    ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v p q hpq = 0)

lemma step {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hk : Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n))
    (z : Cochain (mappingCone φ) I n) (hz : δ n (n + 1) z = 0) (hV : V φ k n z) :
    ∃ c : Cochain (mappingCone φ) I (n - 1), V φ (k - 1) n (z - δ (n - 1) n c) := by
  obtain ⟨hV1, hV2⟩ := hV
  have hzd := desc_eta φ (show n - 1 + 1 = n by omega) z
  generalize hα : (mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega) = α at hV1 hzd
  generalize hβ : (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n) = β at hV2 hzd
  have hV1' : ∀ p q (hpq : p + (n - 1) = q), k < p → α.v p q hpq = 0 := fun p q hpq h => by
    rw [← hα]; exact hV1 p q hpq h
  have hδ := hz
  rw [hzd, δ_desc φ (by omega) rfl] at hδ
  have e1 : δ (n - 1) n α + (n + 1).negOnePow • (Cochain.ofHom φ).comp β (zero_add n) = 0 := by
    have := congrArg (fun x => (mappingCone.inl φ).comp x (show -1 + (n + 1) = n by omega)) hδ
    simpa only [mappingCone.inl_descCochain, Cochain.comp_zero] using this
  have e2 : δ n (n + 1) β = 0 := by
    have := congrArg (fun x => (Cochain.ofHom (mappingCone.inr φ)).comp x (zero_add (n + 1))) hδ
    simpa only [mappingCone.inr_descCochain, Cochain.comp_zero] using this
  have hg : β.v k (k + n) rfl ≫ I.d (k + n) (k + (n + 1)) = 0 := by
    have := Cochain.congr_v e2 k (k + (n + 1)) rfl
    rw [δ_v n (n + 1) rfl β k (k + (n + 1)) rfl (k + n) (k + 1) (by omega) rfl, Cochain.zero_v,
      hV2 (k + 1) (k + (n + 1)) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  have hf : α.v k (k + (n - 1)) rfl ≫ I.d (k + (n - 1)) (k + n) +
      (n + 1).negOnePow • (φ.f k ≫ β.v k (k + n) rfl) = 0 := by
    have := Cochain.congr_v e1 k (k + n) rfl
    rw [Cochain.add_v, Cochain.units_smul_v,
      δ_v (n - 1) n (by omega) α k (k + n) rfl (k + (n - 1)) (k + 1) (by omega) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v,
      hV1' (k + 1) (k + n) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  obtain ⟨a, b, ha, hb⟩ := level_of φ k n hk _ _ hg hf
  refine ⟨mappingCone.descCochain φ (Cochain.single a (n - 1 - 1)) (Cochain.single b (n - 1))
    (by omega), ?_, ?_⟩
  · intro p q hpq hp
    rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inl_descCochain,
      Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v,
      δ_v (n - 1 - 1) (n - 1) (by omega) _ p q hpq (p + (n - 1 - 1)) (p + 1) (by omega) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.single_v_eq_zero a _ (p + 1) q _ (by omega)]
    rcases eq_or_lt_of_le (show k ≤ p by omega) with hkp | hkp
    · subst hkp
      obtain rfl : q = k + (n - 1) := by omega
      have h1 : ((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v k (k + (n - 1)) hpq =
        α.v k (k + (n - 1)) hpq := by rw [hα]
      rw [Cochain.single_v, Cochain.single_v, h1, ha]
      simp
    · rw [hV1 p q hpq hkp, Cochain.single_v_eq_zero a _ p _ _ (by omega),
        Cochain.single_v_eq_zero b _ p _ _ (by omega)]
      simp
  · intro p q hpq hp
    rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inr_descCochain,
      Cochain.sub_v,
      δ_v (n - 1) n (by omega) _ p q hpq (p + (n - 1)) (p + 1) (by omega) rfl,
      Cochain.single_v_eq_zero b _ (p + 1) q _ (by omega)]
    rcases eq_or_lt_of_le (show k ≤ p by omega) with hkp | hkp
    · subst hkp
      obtain rfl : q = k + n := by omega
      have h2 : ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v k (k + n) hpq =
        β.v k (k + n) hpq := by rw [hβ]
      rw [Cochain.single_v, h2, hb]
      simp
    · rw [(show ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v p q hpq = 0 by rw [hβ]; exact hV2 p q hpq hkp), Cochain.single_v_eq_zero b _ p _ _ (by omega)]
      simp

end LateralTheory.E.FiltGenPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FracAICPf
section
open Polynomial

namespace LateralTheory.E.FracAICPf

open Classical in
theorem FracAIC_of : LateralTheory.E.ULAStalkPf.FracAIC := by
  intro T K _ _ _ _ _ hT p hp hdeg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T)
    (p.support.image p.coeff)
  set s : K := algebraMap T K b with hs
  have hs0 : s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  set q := p.scaleRoots s with hq
  have hqm : q.Monic := (monic_scaleRoots_iff _).mpr hp
  have hqd : q.natDegree = p.natDegree := natDegree_scaleRoots _ _
  have hlift : q ∈ lifts (algebraMap T K) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [hq, coeff_scaleRoots]
    by_cases hi : p.coeff i = 0
    · rw [hi, zero_mul]; exact ⟨0, map_zero _⟩
    have hile : i ≤ p.natDegree := le_natDegree_of_ne_zero hi
    rcases lt_or_eq_of_le hile with hlt | heq
    · obtain ⟨c, hc⟩ := hb (p.coeff i) (Finset.mem_image_of_mem _ (mem_support_iff.mpr hi))
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      refine ⟨c * (b : T) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, hc, Algebra.smul_def, pow_succ, hs]
      ring
    · subst heq
      rw [Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree]
      exact ⟨1, map_one _⟩
  obtain ⟨q', hq'map, hq'deg, hq'm⟩ := lifts_and_natDegree_eq_and_monic hlift hqm
  obtain ⟨r, hr⟩ := hT q' hq'm (by rw [hq'deg, hqd]; exact hdeg)
  refine ⟨algebraMap T K r / s, ?_⟩
  have h1 : q.eval (algebraMap T K r) = 0 := by
    rw [← hq'map, eval_map, eval₂_at_apply, hr, map_zero]
  have h2 := scaleRoots_eval₂_mul (p := p) (RingHom.id K) (algebraMap T K r / s) s
  simp only [RingHom.id_apply, eval₂_id] at h2
  rw [mul_div_cancel₀ _ hs0, ← hq, h1] at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hs0)

end LateralTheory.E.FracAICPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HKCoprodPf
section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.HKCoprodPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type} {K : ι → CochainComplex C ℤ} (c : Cofan K)
  (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {L : CochainComplex C ℤ}

include hc in
theorem hom_ext_v {p q : ℤ} {a b : c.pt.X p ⟶ L.X q} (h : ∀ j, (c.inj j).f p ≫ a = (c.inj j).f p ≫ b) : a = b :=
  (hc p).hom_ext fun ⟨j⟩ => h j

include hc in
theorem cochain_ext {n : ℤ} {x y : Cochain c.pt L n}
    (h : ∀ j, (Cochain.ofHom (c.inj j)).comp x (zero_add n) = (Cochain.ofHom (c.inj j)).comp y (zero_add n)) : x = y := by
  ext p q hpq
  refine hom_ext_v c hc fun j => ?_
  have := congrArg (fun z => Cochain.v z p q hpq) (h j)
  simpa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using this

def cof (L : CochainComplex C ℤ) {n : ℤ} (b : ∀ j, Cochain (K j) L n) (p q : ℤ) (hpq : p + n = q) :
    Cocone (Discrete.functor K ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) p) where
  pt := L.X q
  ι := Discrete.natTrans fun k => (b k.as).v p q hpq

def glue (hc : ∀ p, IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapCocone c)) {n : ℤ}
    (b : ∀ j, Cochain (K j) L n) : Cochain c.pt L n :=
  Cochain.mk fun p q hpq => (hc p).desc (cof L b p q hpq)

theorem restr_glue {n : ℤ} (b : ∀ j, Cochain (K j) L n) (j : ι) :
    (Cochain.ofHom (c.inj j)).comp (glue c hc b) (zero_add n) = b j := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact (hc p).fac (cof L b p q hpq) ⟨j⟩

include hc in
theorem bij (n : ℤ) : Function.Bijective fun (x : CohomologyClass c.pt L n) (j : ι) =>
    cpre (Cocycle.ofHom (c.inj j)) L n n (zero_add n) x := by
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    have hj : ∀ j, ∃ β : Cochain (K j) L (n - 1),
        δ (n - 1) n β = (Cochain.ofHom (c.inj j)).comp (x - y : Cocycle c.pt L n).1 (zero_add n) := by
      intro j
      have h := congrFun hxy j
      simp only [cpre_mk] at h
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (by omega)] at h
      obtain ⟨β, hβ⟩ := h
      refine ⟨β, ?_⟩
      rw [hβ]
      simp [zcomp, Cochain.comp_sub]
    choose β hβ using hj
    refine ⟨glue c hc β, cochain_ext c hc fun j => ?_⟩
    rw [← δ_ofHom_comp, restr_glue, hβ]
  · intro y
    choose z hz using fun j => (y j).mk_surjective
    have hδ : δ n (n + 1) (glue c hc fun j => (z j).1) = 0 := cochain_ext c hc fun j => by
      rw [← δ_ofHom_comp, restr_glue, Cocycle.δ_eq_zero]; simp
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hδ), funext fun j => ?_⟩
    simp only [cpre_mk]
    rw [← hz j]
    congr 1
    exact Cocycle.ext (restr_glue c hc (fun j => (z j).1) j)

end General

set_option synthInstance.maxHeartbeats 400000 in
theorem HKCoprod_of : LateralTheory.E.CoprodPf.HKCoprod := by
  intro R _ ι K c hc F n
  have h1 : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits.{1} (Shv R)
  have h0 : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} (Shv R)
  have : HasColimitsOfShape (Discrete ι) (Shv R) := inferInstance
  exact bij c (fun p => isColimitOfPreserves (HomologicalComplex.eval _ _ p) hc) n

end LateralTheory.E.HKCoprodPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IECobPf
section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IECobPf

theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

theorem IECob_of : LateralTheory.E.ULAStalkPf.IECob := by
  intro A B C D f g u v sq hf
  have := et_cobase
  have hI : IE.IsStableUnderCobaseChange := by
    unfold IE; infer_instance
  exact hI.of_isPushout sq.flip hf

end LateralTheory.E.IECobPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LZProperCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.LineZeroCut

namespace LateralTheory.E.LZProperCut

def LZHensFinite : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B],
  ConnectedSpace ↑(Spec (CommRingCat.of B)) → IsLocalRing B

end LateralTheory.E.LZProperCut
end
end

