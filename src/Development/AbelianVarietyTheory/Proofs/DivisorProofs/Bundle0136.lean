module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueClosedImmersionsOpenCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCandidateBorelMoveOpenFramesBaire
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

noncomputable section

theorem countable_GL_numberField {E : Type} [Field E] [NumberField E] (r : ℕ) :
    Countable (GL (Fin r) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable
    (f := fun g : GL (Fin r) E => (g : Matrix (Fin r) (Fin r) E)) fun _ _ h => Units.ext h

theorem continuous_mat_lact {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (g : GL (Fin r) E) (τ : Ψ) :
    Continuous fun z : Frame Ψ r => mat (lact g z) τ := by
  have h : Continuous fun z : Frame Ψ r => mat z τ := continuous_apply τ
  exact continuous_const.matrix_mul h

theorem baire_one_candidate {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (S : Set (GL (Fin r) E)) (a c : GL (Fin r) E) (W : Set (Frame X.Ψ r)) :
    IsOpen W → W.Nonempty → W ⊆ X.dom →
    (∀ z ∈ W, ∃ γ ∈ S, ∃ b ∈ Bor X.Ψ r, lact c z = rmul (lact γ (lact a z)) b) →
    ∃ γ ∈ S, ∃ V : Set (Frame X.Ψ r), IsOpen V ∧ V.Nonempty ∧ V ⊆ X.dom ∧
      ∀ x ∈ V, ∃ b ∈ Bor X.Ψ r, lact ((γ * a)⁻¹ * c) x = rmul x b := by
  intro hW hne hWdom hmove
  let C : GL (Fin r) E → Set (Frame X.Ψ r) := fun g => {z | ∀ τ : X.Ψ, ∀ p q : Fin r, q < p →
    ((mat (lact (g * a) z) τ).adjugate * mat (lact c z) τ) p q = 0}
  have hC : ∀ g, IsClosed (C g) := by
    intro g
    simp only [C, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun p => isClosed_iInter fun q =>
      isClosed_iInter fun _ => ?_
    exact isClosed_eq ((((continuous_mat_lact (g * a) τ).matrix_adjugate).matrix_mul
      (continuous_mat_lact c τ)).matrix_elem p q) continuous_const
  have cover : ∀ z ∈ W, ∃ γ ∈ S, z ∈ C γ := by
    intro z hz
    obtain ⟨γ, hγ, b, hb, heq⟩ := hmove z hz
    refine ⟨γ, hγ, fun τ p q hqp => ?_⟩
    have key : mat (lact c z) τ = mat (lact (γ * a) z) τ * mat b τ := by
      have h1 : mat (lact c z) τ =
          ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((a : Matrix (Fin r) (Fin r) E).map τ.1 *
            mat z τ)) * mat b τ := congrFun heq τ
      rw [h1]
      show _ = (((γ * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ) * mat b τ
      rw [Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    rw [key, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
    have : mat b τ p q = 0 := (hb τ).2 p q hqp
    rw [this, mul_zero]
  haveI : Countable (GL (Fin r) E) := countable_GL_numberField r
  let f : Option S → Set (Frame X.Ψ r) := fun o => o.elim Wᶜ (fun γ => C γ.1)
  have hf : ∀ o, IsClosed (f o) := by
    rintro (_ | γ)
    exacts [hW.isClosed_compl, hC γ.1]
  have hU : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ W
    · obtain ⟨γ, hγ, hzC⟩ := cover z hz
      exact Set.mem_iUnion.2 ⟨some ⟨γ, hγ⟩, hzC⟩
    · exact Set.mem_iUnion.2 ⟨none, hz⟩
  have hD := dense_iUnion_interior_of_closed hf hU
  obtain ⟨z, hzW, hz⟩ := hD.inter_open_nonempty W hW hne
  obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hz
  cases o with
  | none => exact absurd hzW (interior_subset ho)
  | some γ =>
    refine ⟨γ.1, γ.2, W ∩ interior (C γ.1), hW.inter isOpen_interior, ⟨z, hzW, ho⟩,
      fun x hx => hWdom hx.1, fun x hx => ?_⟩
    have hxd : x ∈ X.dom := hWdom hx.1
    have hxC : x ∈ C γ.1 := interior_subset hx.2
    simp only [C, Set.mem_setOf_eq] at hxC
    generalize γ.1 * a = g at hxC ⊢
    have hdetg : ∀ (g' : GL (Fin r) E) (τ : X.Ψ),
        ((g' : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
      intro g' τ
      have h := RingHom.map_det τ.1 (g' : Matrix (Fin r) (Fin r) E)
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units g').ne_zero
    have hdetx : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := fun τ => (hxd τ).1
    have hdetA : ∀ (g' : GL (Fin r) E) (τ : X.Ψ), (mat (lact g' x) τ).det ≠ 0 := by
      intro g' τ
      show ((g' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hdetg g' τ) (hdetx τ)
    let b : Frame X.Ψ r := fun τ =>
      ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ : Matrix (Fin r) (Fin r) ℂ)
    refine ⟨b, fun τ => ⟨?_, fun p q hqp => ?_⟩, ?_⟩
    · show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero
        (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 (hdetA g τ))).ne_zero (hdetA c τ)
    · show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ) p q = 0
      rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, hxC τ p q hqp, smul_zero]
    · funext τ
      have hginv : ((g : Matrix (Fin r) (Fin r) E).map τ.1)⁻¹ =
          ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 := by
        apply Matrix.inv_eq_right_inv
        rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      show ((g⁻¹ * c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
        mat x τ * (((g : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)⁻¹ *
          ((c : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ))
      rw [Matrix.mul_inv_rev, hginv, Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (mat x τ) (mat x τ)⁻¹,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdetx τ)), Matrix.one_mul]

end

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedImmersionRepresentsOfAffineOpens
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_closedImmersion_represents_of_affineOpens : ∀ (S : Scheme.{0}) (U T : Over S) (P : ∀ Y : Over S, (Y ⟶ U) → (Y ⟶ T) → Prop), (∀ (Y Y' : Over S) (f : Y' ⟶ Y) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t → P Y' (f ≫ u) (f ≫ t)) → (∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), (∀ y : Y.left, ∃ W : Y.left.Opens, y ∈ W ∧ P (Over.mk (W.ι ≫ Y.hom)) (Over.homMk W.ι rfl ≫ u) (Over.homMk W.ι rfl ≫ t)) → P Y u t) → (∀ V : T.left.affineOpens, ∃ (H : Over S) (h : H ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Flat (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ Surjective (h ≫ snd U (Over.mk (V.1.ι ≫ T.hom))).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ Over.mk (V.1.ι ≫ T.hom)), P Y u (t ≫ Over.homMk V.1.ι rfl) ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t) → ∃ (H : Over S) (h : H ⟶ U ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd U T).left ∧ Flat (h ≫ snd U T).left ∧ Surjective (h ≫ snd U T).left ∧ ∀ (Y : Over S) (u : Y ⟶ U) (t : Y ⟶ T), P Y u t ↔ ∃ z : Y ⟶ H, z ≫ h = lift u t := by
  intro S U T P hres hloc hV
  choose H h hci hfin hflat hsurj hrep using hV
  have key : ∀ (V : T.left.affineOpens) (Y : Over S) (g : Y ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom)),
      P Y (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ fst U T)
        (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) ≫ snd U T) ↔
      ∃ z : Y.left ⟶ (H V).left, z ≫ (h V).left = g.left := by
    intro V Y g
    rw [whiskerLeft_fst, whiskerLeft_snd, ← Category.assoc g]
    rw [hrep V Y (g ≫ fst _ _) (g ≫ snd _ _), lift_comp_fst_snd]
    constructor
    · rintro ⟨z, hz⟩; exact ⟨z.left, by rw [← Over.comp_left, hz]⟩
    · rintro ⟨z, hz⟩
      refine ⟨Over.homMk z ?_, ?_⟩
      · rw [← Over.w (h V), ← Category.assoc, hz, Over.w g]
      · apply Over.OverMorphism.ext; simpa using hz

  have hpb : ∀ V : T.left.affineOpens,
      IsPullback (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left
        (snd U (Over.mk (V.1.ι ≫ T.hom))).left (snd U T).left V.1.ι :=
    fun V => _root_.GlobalTheory.whiskerLeft_left_isPullback_snd S U T _ _
  have hoi : ∀ V : T.left.affineOpens,
      IsOpenImmersion (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left :=
    fun V => MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb V).flip inferInstance
  have hmem : ∀ y : T.left, ∃ V : T.left.affineOpens, y ∈ V.1 := by
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      T.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact ⟨⟨V, hV⟩, hyV⟩
  have hsup : (⨆ V : T.left.affineOpens, (V.1 : T.left.Opens)) = ⊤ := by
    rw [eq_top_iff]; intro y _
    obtain ⟨V, hV⟩ := hmem y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V, hV⟩
  have hcov : ∀ x : (U ⊗ T).left, ∃ V : T.left.affineOpens,
      x ∈ Set.range (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left := by
    intro x
    obtain ⟨V, hV⟩ := hmem ((snd U T).left x)
    obtain ⟨v, hv⟩ : (snd U T).left x ∈ Set.range V.1.ι := by rw [Scheme.Opens.range_ι]; exact hV
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback x v hv.symm
    refine ⟨V, (hpb V).isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]; exact hw1
  have compat : ∀ (V V' : T.left.affineOpens) (Y : Scheme.{0})
      (g : Y ⟶ (U ⊗ Over.mk (V.1.ι ≫ T.hom)).left) (g' : Y ⟶ (U ⊗ Over.mk (V'.1.ι ≫ T.hom)).left),
      g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left =
        g' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ T)).left →
      ((∃ z : Y ⟶ (H V).left, z ≫ (h V).left = g) ↔ (∃ z : Y ⟶ (H V').left, z ≫ (h V').left = g')) := by
    intro V V' Y g g' hgg
    let Y' : Over S := Over.mk (g ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)).left ≫ (U ⊗ T).hom)
    let e : Y' ⟶ U ⊗ Over.mk (V.1.ι ≫ T.hom) := Over.homMk g (by simp [Y'])
    let e' : Y' ⟶ U ⊗ Over.mk (V'.1.ι ≫ T.hom) := Over.homMk g' (by
      show _ = g ≫ _ ≫ _; rw [← Category.assoc g, hgg, Category.assoc, Over.w])
    have hm : e ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) =
        e' ≫ (U ◁ (Over.homMk V'.1.ι rfl : Over.mk (V'.1.ι ≫ T.hom) ⟶ T)) := by
      apply Over.OverMorphism.ext; simpa [e, e'] using hgg
    have k := key V Y' e
    have k' := key V' Y' e'
    rw [reassoc_of% hm, reassoc_of% hm] at k
    exact k.symm.trans k'
  obtain ⟨B, b, hb, hbrep⟩ := _root_.GlobalTheory.GlueClosed.exists_glue_isClosedImmersion (U ⊗ T).left T.left.affineOpens _ _ hoi hcov
    (fun V => (H V).left) (fun V => (h V).left) hci compat
  have hprops := _root_.GlobalTheory.finite_flat_surjective_of_openCover (U ⊗ T).left T.left (snd U T).left T.left.affineOpens
    (fun V => V.1) hsup _ _ _ hpb B b hb _ _ hci hbrep
    (fun V => ⟨hfin V, hflat V, hsurj V⟩)
  refine ⟨Over.mk (b ≫ (U ⊗ T).hom), Over.homMk b rfl, hb, hprops.1, hprops.2.1, hprops.2.2, ?_⟩
  intro Y u t

  have hW : ∀ (V : T.left.affineOpens),
      P (Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom)) (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u)
        (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t) ↔
      ∃ z : (t.left ⁻¹ᵁ V.1).toScheme ⟶ B, z ≫ b = (t.left ⁻¹ᵁ V.1).ι ≫ (lift u t).left := by
    intro V
    have hr : Set.range ((t.left ⁻¹ᵁ V.1).ι ≫ t.left) ⊆ Set.range V.1.ι := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      have h1 : (t.left ⁻¹ᵁ V.1).ι w ∈ ((t.left ⁻¹ᵁ V.1 : Y.left.Opens) : Set Y.left) := by
        rw [← Scheme.Opens.range_ι]; exact Set.mem_range_self w
      rw [Scheme.Hom.comp_apply]; exact h1
    let tW : Over.mk ((t.left ⁻¹ᵁ V.1).ι ≫ Y.hom) ⟶ Over.mk (V.1.ι ≫ T.hom) :=
      Over.homMk (IsOpenImmersion.lift V.1.ι _ hr) (by simp [IsOpenImmersion.lift_fac_assoc])
    have htW : tW ≫ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T) =
        Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ t := by
      apply Over.OverMorphism.ext; simp [tW, IsOpenImmersion.lift_fac]
    let gW := lift (Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ u) tW
    have hgW : gW ≫ (U ◁ (Over.homMk V.1.ι rfl : Over.mk (V.1.ι ≫ T.hom) ⟶ T)) =
        Over.homMk (t.left ⁻¹ᵁ V.1).ι rfl ≫ lift u t := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [gW, htW]
    have k := key V _ gW
    rw [reassoc_of% hgW, reassoc_of% hgW, lift_fst, lift_snd] at k
    rw [k, ← hbrep V _ gW.left, ← Over.comp_left, hgW]
    rfl
  constructor
  · intro hP
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.exists_factor_closedImmersion_of_locally _ _ _ b hb (lift u t).left (fun y => by
      obtain ⟨V, hV⟩ := hmem (t.left y)
      exact ⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mp (hres _ _ _ u t hP)⟩)
    refine ⟨Over.homMk z ?_, ?_⟩
    · simp only [Over.mk_hom]; rw [← Category.assoc, hz, Over.w]
    · apply Over.OverMorphism.ext; simpa using hz
  · rintro ⟨z, hz⟩
    apply hloc
    intro y
    obtain ⟨V, hV⟩ := hmem (t.left y)
    refine ⟨t.left ⁻¹ᵁ V.1, hV, (hW V).mpr ⟨(t.left ⁻¹ᵁ V.1).ι ≫ z.left, ?_⟩⟩
    rw [Category.assoc, ← hz]; rfl
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRepresentativeAverage
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LocRep


open MeasureTheory in
open scoped ContDiff Pointwise in
theorem _root_.GlobalTheory.LocRep.exists_continuous_rep_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → (∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g)) → ∀ (η : G → ℂ) (v : K), Continuous η → HasCompactSupport η → ∃ φ : G → ℂ, Continuous φ ∧ ι (∫ y, η y • ρ y v ∂μ) =ᵐ[μ] φ := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ι hloc hlin ρ hnorm hcont htrans η v hηc hηs
  have hιv : LocallyIntegrable (ι v) μ := _root_.GlobalTheory.LocRep.locallyIntegrable_rep hloc v
  obtain ⟨B, hB⟩ := hηc.bounded_above_of_compact_support hηs
  set φ : G → ℂ := fun x => ∫ y, η y * ι v (x * y) ∂μ with hφdef
  have hφeq : φ = fun x => ∫ z, η (x⁻¹ * z) * ι v z ∂μ := by
    funext x
    rw [hφdef, ← integral_mul_left_eq_self (fun z => η (x⁻¹ * z) * ι v z) x]
    simp
  have hφc : Continuous φ := by
    rw [hφeq, continuous_iff_continuousAt]
    intro x₀
    obtain ⟨V, hV, hVn⟩ := exists_compact_mem_nhds x₀
    have hL : IsCompact (V * tsupport η) := hV.mul hηs
    refine continuousAt_of_dominated (bound := (V * tsupport η).indicator fun z => B * ‖ι v z‖)
      (Filter.Eventually.of_forall fun x =>
        ((hηc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul
          hιv.aestronglyMeasurable) ?_ ?_
      (Filter.Eventually.of_forall fun z =>
        ((hηc.comp (continuous_id.inv.mul continuous_const)).mul continuous_const).continuousAt)
    · filter_upwards [hVn] with x hx
      refine Filter.Eventually.of_forall fun z => ?_
      by_cases hz : η (x⁻¹ * z) = 0
      · rw [hz, zero_mul, norm_zero]
        exact Set.indicator_nonneg
          (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hB 1)) (norm_nonneg _)) _
      have hzL : z ∈ V * tsupport η := by
        have := Set.mul_mem_mul hx (subset_tsupport η hz)
        rwa [mul_inv_cancel_left] at this
      rw [Set.indicator_of_mem hzL, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · exact IntegrableOn.integrable_indicator
        ((hιv.integrableOn_isCompact hL).norm.const_mul B) hL.measurableSet
  refine ⟨φ, hφc, _root_.GlobalTheory.LocRep.rep_of_pairing hloc hφc.locallyIntegrable ?_⟩
  intro C hC
  obtain ⟨Λ, hΛ⟩ := _root_.GlobalTheory.LocRep.exists_pairing hloc hlin hC
  obtain ⟨M, hM⟩ := hloc C hC
  have hint : Integrable (fun y => η y • ρ y v) μ :=
    (hηc.smul (hcont v)).integrable_of_hasCompactSupport hηs.smul_right
  have hηI : Integrable η μ := hηc.integrable_of_hasCompactSupport hηs
  have hrestr : μ.prod (μ.restrict C) = (μ.prod μ).restrict (Set.univ ×ˢ C) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEStronglyMeasurable (fun p : G × G => η p.1 * ι v (p.2 * p.1))
      (μ.prod (μ.restrict C)) := by
    have h1 : AEStronglyMeasurable (fun p : G × G => ι v (p.2 * p.1)) (μ.prod μ) :=
      (hιv.aestronglyMeasurable.comp_snd (μ := μ)).comp_measurePreserving
        (measurePreserving_prod_mul_swap μ μ)
    rw [hrestr]
    exact ((hηc.comp continuous_fst).aestronglyMeasurable).mul h1.restrict
  have hslice : ∀ y, IntegrableOn (fun x => ι v (x * y)) C μ ∧
      ∫ x in C, ‖ι v (x * y)‖ ∂μ ≤ M * ‖v‖ := by
    intro y
    have hae : ι (ρ y v) =ᵐ[μ.restrict C] fun x => ι v (x * y) := ae_restrict_of_ae (htrans y v)
    obtain ⟨h1, h2⟩ := hM (ρ y v)
    refine ⟨h1.congr_fun_ae hae, ?_⟩
    rw [← hnorm y v]
    refine le_of_eq_of_le (integral_congr_ae (hae.mono fun x hx => ?_)).symm h2
    simp only [hx]
  have hprod : Integrable (Function.uncurry fun y x => η y * ι v (x * y))
      (μ.prod (μ.restrict C)) := by
    refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall fun y =>
      (hslice y).1.const_mul (η y), ?_⟩
    refine Integrable.mono' (hηI.norm.mul_const (M * ‖v‖)) hmeas.norm.integral_prod_right' ?_
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [norm_mul, Function.uncurry_apply_pair]
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => by positivity), integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hslice y).2 (norm_nonneg _)
  calc ∫ x in C, ι (∫ y, η y • ρ y v ∂μ) x ∂μ = Λ (∫ y, η y • ρ y v ∂μ) := (hΛ _).symm
    _ = ∫ y, Λ (η y • ρ y v) ∂μ := (Λ.integral_comp_comm hint).symm
    _ = ∫ y, ∫ x in C, η y * ι v (x * y) ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [map_smul, hΛ, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (htrans y v)] with x hx
        rw [hx]
    _ = ∫ x in C, φ x ∂μ := integral_integral_swap hprod

end GlobalTheory.LocRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulIsIntegralOfPadicIntegral
section
open scoped TensorProduct Classical
open Polynomial

namespace GlobalTheory.IntegralDescent

theorem not_dvd_den_coeff_minpoly (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (w : E) (hw : IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w)) (i : ℕ) :
    ¬ ℓ ∣ ((minpoly ℚ w).coeff i).den := by
  obtain ⟨p, hpm, hp⟩ := hw
  have hzi : IsIntegral ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) := IsIntegral.of_finite _ _
  have hdvd : minpoly ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) ∣ p.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_map]
    exact hp
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ_[ℓ] hpm hdvd
  rw [(minpoly.monic hzi).leadingCoeff, C_1, mul_one, GlobalTheory.DescCoeff.minpoly_one_tmul_eq] at hg
  have hc := congrArg (fun q => q.coeff i) hg
  simp only [coeff_map] at hc
  have hn : ‖(((minpoly ℚ w).coeff i : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
    rw [← eq_ratCast (algebraMap ℚ ℚ_[ℓ]), ← hc]
    exact (g.coeff i).2
  intro hd
  have hu := PadicInt.isUnit_den _ hn
  exact PadicInt.irreducible_p.not_isUnit
    (isUnit_of_dvd_unit (Nat.cast_dvd_cast (α := ℤ_[ℓ]) hd) hu)

theorem exists_not_dvd_isIntegral_mul : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (w : E), IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) → ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * w) := by
  intro E _ _ _ ℓ hℓ w hw
  set f := minpoly ℚ w with hf
  have hfm : f.Monic := minpoly.monic (IsIntegral.of_finite ℚ w)
  set d : ℕ := ∏ i ∈ Finset.range f.natDegree, (f.coeff i).den with hd
  refine ⟨d, ?_, ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (hℓ.out.prime.dvd_finsetProd_iff _).mp h
    exact not_dvd_den_coeff_minpoly E ℓ w hw i hi
  · have hroot : aeval ((d : E) * w) (f.scaleRoots (d : ℚ)) = 0 := by
      have := scaleRoots_aeval_eq_zero (r := (d : ℚ)) (minpoly.aeval ℚ w)
      rwa [map_natCast] at this
    have hlift : f.scaleRoots (d : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
      rw [lifts_iff_coeff_lifts]
      intro i
      rw [coeff_scaleRoots]
      rcases lt_trichotomy i f.natDegree with hi | hi | hi
      · obtain ⟨c, hc⟩ : (f.coeff i).den ∣ d :=
          Finset.dvd_prod_of_mem (fun j => (f.coeff j).den) (Finset.mem_range.mpr hi)
        obtain ⟨k, hk⟩ : ∃ k, f.natDegree - i = k + 1 := ⟨f.natDegree - i - 1, by omega⟩
        refine ⟨(f.coeff i).num * c * (d : ℤ) ^ k, ?_⟩
        rw [hk, pow_succ]
        have h1 : (d : ℚ) = ((f.coeff i).den : ℚ) * c := by exact_mod_cast hc
        have h2 : f.coeff i * ((f.coeff i).den : ℚ) = (f.coeff i).num := Rat.mul_den_eq_num _
        simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
        rw [← h2]
        linear_combination (-(f.coeff i) * (d : ℚ) ^ k) * h1
      · subst hi
        exact ⟨1, by simp [hfm.coeff_natDegree]⟩
      · exact ⟨0, by simp [coeff_eq_zero_of_natDegree_lt hi]⟩
    obtain ⟨q, hq, -, hqm⟩ :=
      lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff _).mpr hfm)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ, hq]
    exact hroot

end GlobalTheory.IntegralDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegLtTwoCorrectionSimple
section
open Polynomial

namespace GlobalTheory.PicDiv

theorem exists_deg_lt_two_correction_simple :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A),
      P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧
        w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  intro k A _ _ _ _ _ _ _ _ _ n b P₀ w hP
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨φ, hφ⟩ := ((GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A).2.1 P₀ hP).2
  set α : k := φ (algebraMap k[X] A X) with hα
  have hC : algebraMap k[X] A (C α) = algebraMap k A α := by
    rw [IsScalarTower.algebraMap_apply k k[X] A]; rfl
  have hlin : algebraMap k[X] A (X - C α) ∈ P₀ := by
    rw [hφ, map_sub, map_sub, hC, φ.commutes, ← hα]
    simp
  have hne : algebraMap k[X] A (X - C α) ≠ 0 := by
    intro h0
    have h1 : (X - C α) • (1 : A) = 0 := by rw [Algebra.smul_def, h0, zero_mul]
    have h3 : b.repr (1 : A) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp h3
    have h4 := congrArg (fun a => b.repr a i) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h4
    exact mul_ne_zero (X_sub_C_ne_zero α) hi h4
  have hbot : P₀ ≠ ⊥ := fun h => hne (by rw [h] at hlin; simpa using hlin)
  have hlt := Ideal.pow_lt_self P₀ hbot hP.ne_top 2 le_rfl
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  set q : k[X] := (X - C α) ^ 2 with hq
  have hmon : q.Monic := (monic_X_sub_C α).pow 2
  have hqdeg : q.degree = (2 : ℕ) := by
    rw [hq, degree_pow, degree_X_sub_C]; rfl
  have hqmem : algebraMap k[X] A q ∈ P₀ ^ 2 := by
    rw [hq, map_pow]; exact Ideal.pow_mem_pow hlin 2
  let c : Fin n → k[X] := fun i => b.repr (π - w) i
  let p : Fin n → k[X] := fun i => c i %ₘ q
  let d : Fin n → k[X] := fun i => c i /ₘ q
  have hs : ∑ i, c i • b i = π - w := b.sum_repr (π - w)
  have h2 : ∑ i, c i • b i = ∑ i, p i • b i + algebraMap k[X] A q * ∑ i, d i • b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, smul_smul, ← add_smul]
    exact congrArg (· • b i) (modByMonic_add_div (c i) q).symm
  have key : w + ∑ i, p i • b i = π - algebraMap k[X] A q * ∑ i, d i • b i := by
    linear_combination hs - h2
  have hM : algebraMap k[X] A q * ∑ i, d i • b i ∈ P₀ ^ 2 := Ideal.mul_mem_right _ _ hqmem
  refine ⟨p, fun i => ?_, ?_, ?_⟩
  · rw [← hqdeg]; exact degree_modByMonic_lt _ hmon
  · rw [key]; exact P₀.sub_mem hπP (Ideal.pow_le_self two_ne_zero hM)
  · intro h
    apply hπ2
    have : π = (w + ∑ i, p i • b i) + algebraMap k[X] A q * ∑ i, d i • b i := by
      rw [key]; ring
    rw [this]; exact (P₀ ^ 2).add_mem h hM

end GlobalTheory.PicDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqReStatement
section
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  first | exact @GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re | exact GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re | (intros; apply GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re <;> assumption)
end

