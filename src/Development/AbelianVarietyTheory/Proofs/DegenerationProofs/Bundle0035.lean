module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompRel
section
open GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.HomCalc
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}

def comp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') : NumD.Hom (g.comp f) N N'' where
  φ := I'.φ.comp I.φ
  h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
  h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
  θ_eq x y u := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.θ_eq x y u)
    have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
    have c : Units.map (g.comp f).toMonoidHom (N.θ x y u) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.θ x y u)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
    linear_combination (norm := abel) a + b
  σ_eq x := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.σ_eq x)
    have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
    have c : Units.map (g.comp f).toMonoidHom (N.σ x) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.σ x)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply, map_inv I.φ] at a b ⊢
    linear_combination (norm := abel) a + b
  lam := I'.lam * Units.map g.toMonoidHom I.lam
  th_eq x := by
    rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq]
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.comp_apply]
    ring
  e := I.e.trans I'.e
  c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
  ψ_eq χ := by
    have c : Units.map (g.comp f).toMonoidHom (N.ψ χ) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.ψ χ)) := rfl
    rw [c, ← I.ψ_eq, map_mul, ← I'.ψ_eq, I.c_eq, AddEquiv.trans_apply, mul_assoc]

theorem comp_rel {I : NumD.Hom f N N'} {I' : NumD.Hom g N' N''} {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b)
    (h' : I'.Rel b c) : (comp I I').Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have u := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (h.2 χ)
  have v := congrArg Additive.ofMul (h'.2 (I.e χ))
  have w : Units.map (g.comp f).toMonoidHom (a.s χ) = Units.map g.toMonoidHom (Units.map f.toMonoidHom (a.s χ)) := rfl
  rw [I.c_eq, h.1] at v
  show c.s (I'.e (I.e χ)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) =
    _ * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _))
  apply Additive.ofMul.injective
  simp only [w, map_mul, ofMul_mul] at u v ⊢
  linear_combination (norm := abel) u + v

def inv {M M' : NumD O} (I : NumD.Iso M' M) : NumD.Hom (RingHom.id O) M M' where
  φ := I.φ.symm.toMonoidHom
  h x := (I.h (I.φ.symm x))⁻¹
  h_one := by rw [map_one, I.h_one, inv_one]
  θ_eq x y u := by
    have a := congrArg Additive.ofMul (I.θ_eq (I.φ.symm x) (I.φ.symm y) (I.φ.symm u))
    show M'.θ (I.φ.symm x) (I.φ.symm y) (I.φ.symm u) * _ * _ * _ = M.θ x y u * _ * _ * _ * _
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  σ_eq x := by
    have a := congrArg Additive.ofMul (I.σ_eq (I.φ.symm x))
    show M'.σ (I.φ.symm x) * _ = M.σ x * _
    apply Additive.ofMul.injective
    simp only [map_inv I.φ.symm, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  lam := I.lam⁻¹
  th_eq x := by
    have a := I.th_eq (I.φ.symm x)
    rw [MulEquiv.apply_symm_apply] at a
    show M'.th (I.φ.symm x) = _ * M.th x
    rw [a, ← mul_inv, Units.inv_mul_cancel_left]
  e := I.e.symm
  c_eq χ := by
    show _ = I.φ.symm _
    rw [MulEquiv.eq_symm_apply, ← I.c_eq, AddEquiv.apply_symm_apply]
  ψ_eq χ := by
    obtain ⟨χ, rfl⟩ := I.e.surjective χ
    show _ = M.ψ _
    rw [AddEquiv.symm_apply_apply, I.c_eq, MulEquiv.symm_apply_apply, ← I.ψ_eq, mul_inv_cancel_right]

theorem inv_rel {M M' : NumD O} {I : NumD.Iso M' M} {a : M'.Gt} {b : M.Gt} (h : I.Rel a b) : (inv I).Rel b a := by
  refine ⟨(I.φ.symm_apply_eq.2 h.1).symm, fun χ => ?_⟩
  obtain ⟨χ, rfl⟩ := I.e.surjective χ
  have u := congrArg Additive.ofMul (h.2 χ)
  show a.s (I.e.symm _) * (I.h (I.φ.symm _))⁻¹ = b.s _ * (I.h (I.φ.symm _))⁻¹ * (I.h (I.φ.symm _))⁻¹
  rw [AddEquiv.symm_apply_apply, I.c_eq, h.1, ← map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, MulEquiv.symm_apply_apply] at u ⊢
  linear_combination (norm := abel) -u

end GlobalTheory.HomCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingPropertiesStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
theorem _root_.GlobalTheory.T.degenerationWeilPairing_properties : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (p p' p'' : N.QT k), N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' ∧ N.wp p p = 1 ∧ N.wp p p' * N.wp p' p = 1 ∧ N.wp p p' ^ k = 1 ∧ (N.QEq p p' → N.wp p p'' = N.wp p' p'') ∧ (p.1.1 = 1 → p.1.2.b = 1 → N.wp p p' = p.1.2.s p'.1.1.toAdd) ∧ (p.1.1 = 1 → p'.1.1 = 1 → N.wp p p' = N.weil k p.1.2.b p'.1.2.b) := by
  first | exact @GlobalTheory.Ex.WpPairing.wp_pairing | exact GlobalTheory.Ex.WpPairing.wp_pairing | (intros; apply GlobalTheory.Ex.WpPairing.wp_pairing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrpFlatDesc

open GrpDense MorphismProperty

variable {Z U : Scheme.{0}}

theorem hom_ext_of_points (j : U ⟶ Z) [Flat j] [Surjective j] {X Y : Over Z} {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have := Flat.epi_of_flat_of_surjective (pullback.fst X.hom j)
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom j))
    (Over.homMk (pullback.fst X.hom j) (by simpa using pullback.condition)))


set_option backward.isDefEq.respectTransparency.types false in
theorem isProper_of_isPullback {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have h₁ : UniversallyClosed g :=
    of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip hj inferInstance
  have h₂ : LocallyOfFiniteType g :=
    of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip hj inferInstance
  have : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
    @IsStableUnderBaseChange.inf _ _ _ _ (@IsStableUnderBaseChange.inf _ _ _ _ inferInstance inferInstance)
      inferInstance
  have : MorphismProperty.RespectsIso (C := Scheme.{0}) @UniversallyClosed := universallyClosed_respectsIso
  have h₃ : UniversallyClosed (pullback.diagonal g) :=
    of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) h.flip hj
      (show UniversallyClosed (pullback.diagonal f) from inferInstance)
  have h₄ : IsSeparated g :=
    ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal g).isClosedMap.isClosed_range⟩
  exact {}

theorem geometricallyConnected_of_isPullback {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Surjective j] (h : IsPullback φ f g j) [hf : GeometricallyConnected f] : GeometricallyConnected g := by
  refine ⟨fun K _ y W a b hW => ?_⟩

  obtain ⟨p, -⟩ := (pullback.fst y j).surjective (Classical.arbitrary _)
  let r := (Limits.pullback y j).fromSpecResidueField p
  let s := r ≫ pullback.fst y j
  let t := r ≫ pullback.snd y j
  have hst : t ≫ j = s ≫ y := by simp only [t, s, Category.assoc, pullback.condition]
  have hs : Surjective s := inferInstance

  have hc : ConnectedSpace ↥(Limits.pullback f t) := pullback_of_geometrically hf.1 _ t

  have hout : IsPullback (pullback.fst f t ≫ φ) (pullback.snd f t) g (s ≫ y) := by
    rw [← hst]
    exact (IsPullback.of_hasPullback f t).paste_horiz h
  let q : Limits.pullback f t ⟶ W :=
    hW.lift (pullback.fst f t ≫ φ) (pullback.snd f t ≫ s) (by simpa only [Category.assoc] using hout.w)
  have hq : IsPullback q (pullback.snd f t) b s :=
    IsPullback.of_right (by rwa [hW.lift_fst]) (hW.lift_snd _ _ _) hW
  have hqs : Surjective q := MorphismProperty.of_isPullback hq.flip hs
  exact hqs.surj.connectedSpace q.continuous

theorem grpObj_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] (G : Over Z) (A : Over U) [GrpObj A]
    [IsCommMonObj A] (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G) (i : G ⟶ G)
    (e : 𝟙_ (Over Z) ⟶ G)
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  have hM := fun {T : Over U} => pushPt_mul h.w hm (T := T)
  have hI := fun {T : Over U} => pushPt_inv h.w hi (T := T)
  have hE := pushPt_one h.w he
  letI : MonObj G :=
    { one := e
      mul := m
      one_mul := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (toUnit _) (pushPt h.w x) :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        rw [lift_whiskerRight_assoc, hE, hM, _root_.one_mul, lift_leftUnitor_hom]
      mul_one := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
        obtain rfl : t = lift (pushPt h.w x) (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [lift_whiskerLeft_assoc, hE, hM, _root_.mul_one, lift_rightUnitor_hom]
      mul_assoc := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := pushPt_surjective h T (t ≫ snd _ _)
        obtain rfl : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          ext <;> simp [hx, hy, hz]
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, hM, hM, hM, hM,
          _root_.mul_assoc] }
  letI : GrpObj G :=
    { inv := i
      left_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, inv_mul_cancel, comp_toUnit_assoc, hE]
      right_inv := GrpFlatDesc.hom_ext_of_points j fun T t => by
        obtain ⟨x, rfl⟩ := pushPt_surjective h T t
        change _ ≫ _ ≫ m = _ ≫ _ ≫ e
        rw [comp_lift_assoc, Category.comp_id, hI, hM, mul_inv_cancel, comp_toUnit_assoc, hE] }
  refine ⟨inferInstance, rfl, rfl, rfl, ⟨GrpFlatDesc.hom_ext_of_points j fun T t => ?_⟩, h, fun T x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨x, hx⟩ := pushPt_surjective h T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := pushPt_surjective h T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.w x) (pushPt h.w y) := by ext <;> simp [hx, hy]
    change _ ≫ _ ≫ m = _ ≫ m
    rw [lift_braiding_hom_assoc, hM, hM, _root_.mul_comm]
  · obtain rfl : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    exact congrArg (fun z => z.left) (hM x y)

theorem isAbelianScheme_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] [QuasiCompact j] (G : Over Z) (A : Over U)
    [GrpObj A] (hA : IsAbelianScheme A) (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G)
    (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G) (φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left) (h₂ : IsSquare φ φ₂)
    (hm : φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, IsAbelianScheme G ∧ IsGrpPullback A G j φ := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨_, -, -, -, hc, hp⟩ := grpObj_of_flat_cover j G A φ h m i e (fun ψ hψ => by
    obtain rfl : ψ = φ₂ := Over.tensorObj_ext _ _ (hψ.1.trans h₂.1.symm) (hψ.2.trans h₂.2.symm)
    exact hm) hi he
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) j :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact ⟨inferInstance, ⟨hc, of_isPullback_of_descendsAlong (P := @Smooth) h.flip hj hA.smooth,
    isProper_of_isPullback h, geometricallyConnected_of_isPullback h⟩, hp⟩

end GlobalTheory.GrpFlatDesc

namespace GlobalTheory

theorem isAbelianScheme_descends_subfield :
    ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (B : Over (Sp K)) [GrpObj B] (B₀ : Over (Sp k)) (φ : B.left ⟶ B₀.left), IsAbelianScheme B → IsPullback φ B.hom B₀.hom (spMap β) → ∀ (m : B₀ ⊗ B₀ ⟶ B₀) (i : B₀ ⟶ B₀) (e : 𝟙_ (Over (Sp k)) ⟶ B₀) (φ₂ : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left), φ₂ ≫ (fst B₀ B₀).left = (fst B B).left ≫ φ → φ₂ ≫ (snd B₀ B₀).left = (snd B B).left ≫ φ → φ₂ ≫ m.left = (μ[B]).left ≫ φ → φ ≫ i.left = (ι[B]).left ≫ φ → spMap β ≫ e.left = (η[B]).left ≫ φ → ∃ _ : GrpObj B₀, IsAbelianScheme B₀ ∧ IsGrpPullback B B₀ (spMap β) φ := by
  intro k K _ _ β B _ B₀ φ hB h m i e φ₂ h₁ h₂ hm hi he
  have : Flat (spMap β) := by
    algebraize [β]
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat k K)
  have : Surjective (spMap β) := ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  exact GrpFlatDesc.isAbelianScheme_of_flat_cover (spMap β) B₀ B hB φ h m i e φ₂ ⟨h₁, h₂⟩ hm hi he

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomPairDescendsToFinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.HomPairDescent

open GlobalTheory.Spread

theorem id_pow_left_comm {S S' : Scheme.{0}} {j : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G j φ) (m : ℕ) :
    (𝟙 G' ^ m : G' ⟶ G').left ≫ φ = φ ≫ (𝟙 G ^ m : G ⟶ G).left := by
  have e₁ := congrArg (fun a => a.left) (map_pow (pushHom h G') (𝟙 G') m)
  have e₂ := congrArg (fun a => a.left) (MonObj.comp_pow (𝟙 G) m (pushHom h G' (𝟙 G')))
  rw [Category.comp_id] at e₂
  refine e₁.trans (e₂.symm.trans ?_)
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isGrpPullback_bcMap {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (A : Over (Sp k)) [GrpObj A] (ρ : R →ₐ[k] S) :
    IsGrpPullback ((Over.pullback (spMap (algebraMap k S))).obj A) ((Over.pullback (spMap (algebraMap k R))).obj A)
      (spMap ρ.toRingHom) (bcMap A.hom ρ) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (spMap_algHom_comp ρ).symm (bcMap_fst A.hom ρ).symm) (bcMap_snd A.hom ρ)

theorem exists_descend {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A B : Over (Sp K))
    [QuasiCompact A.hom] [QuasiSeparated A.hom] [LocallyOfFinitePresentation B.hom]
    (f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) :
    ∃ s : Finset Ω, ∀ L : IntermediateField K Ω, (s : Set Ω) ⊆ L →
      ∃ g : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B,
        bcMap A.hom L.val ≫ g.left = f.left ≫ bcMap B.hom L.val := by
  have hfw : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  obtain ⟨R, ψ, ⟨s, rfl⟩, hψ, hψf⟩ := exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ _) hfw)
  refine ⟨s, fun L hL => ?_⟩
  have hle : Algebra.adjoin K (s : Set Ω) ≤ L.toSubalgebra := Algebra.adjoin_le hL
  let ρ : Algebra.adjoin K (s : Set Ω) →ₐ[K] L := Subalgebra.inclusion hle
  have hw : (bcMap A.hom ρ ≫ ψ) ≫ B.hom = pullback.snd _ _ ≫ spMap (algebraMap K L) := by
    rw [Category.assoc, hψ, bcMap_fst_assoc, pullback.condition]
  let g₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ pullback B.hom (spMap (algebraMap K L)) :=
    pullback.lift (bcMap A.hom ρ ≫ ψ) (pullback.snd _ _) hw
  let f₀ : pullback A.hom (spMap (algebraMap K Ω)) ⟶ pullback B.hom (spMap (algebraMap K Ω)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := hfw
  have hψ₀ : bcMap A.hom (Algebra.adjoin K (s : Set Ω)).val ≫ ψ = f₀ ≫ pullback.fst _ _ := hψf
  refine ⟨Over.homMk g₀ (pullback.lift_snd _ _ _), ?_⟩
  change bcMap A.hom L.val ≫ g₀ = f₀ ≫ bcMap B.hom L.val
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, pullback.lift_fst,
      bcMap_comp_of_eq_assoc A.hom ρ L.val (Algebra.adjoin K (s : Set Ω)).val fun _ ↦ rfl, hψ₀]
  · rw [Category.assoc, Category.assoc, bcMap_snd, pullback.lift_snd, bcMap_snd, reassoc_of% hf₀]

theorem comp_eq_pow_of_epi {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] {G' H' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (h : IsGrpPullback G' G j φ) [Epi φ]
    {a' : G' ⟶ H'} {b' : H' ⟶ G'} {a : G ⟶ H} {b : H ⟶ G}
    (ha : φ ≫ a.left = a'.left ≫ ψ) (hb : ψ ≫ b.left = b'.left ≫ φ) (m : ℕ)
    (e : a' ≫ b' = 𝟙 _ ^ m) : a ≫ b = 𝟙 _ ^ m := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi φ, ← id_pow_left_comm h m, ← e, Over.comp_left, Over.comp_left, reassoc_of% ha, hb,
    Category.assoc]

end GlobalTheory.HomPairDescent

namespace GlobalTheory

open HomPairDescent Spread

theorem homPair_descends_to_finite : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (A B : Over (Sp K)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (i : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) (r : (Over.pullback (spMap (algebraMap K Ω))).obj B ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj A), IsMonHom i → IsMonHom r → ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (i' : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B) (r' : (Over.pullback (spMap (algebraMap K L))).obj B ⟶ (Over.pullback (spMap (algebraMap K L))).obj A), IsMonHom i' ∧ IsMonHom r' ∧ ∀ m : ℕ, (i ≫ r = 𝟙 _ ^ m → i' ≫ r' = 𝟙 _ ^ m) ∧ (r ≫ i = 𝟙 _ ^ m → r' ≫ i' = 𝟙 _ ^ m) := by
  classical
  intro K Ω _ _ _ _ A B _ _ hA hB i r hi hr
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  obtain ⟨s, hs⟩ := exists_descend A B i
  obtain ⟨t, ht⟩ := exists_descend B A r
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((s ∪ t : Finset Ω) : Set Ω)
  have hL : ((s ∪ t : Finset Ω) : Set Ω) ⊆ L := IntermediateField.subset_adjoin _ _
  obtain ⟨i', hi'⟩ := hs L ((Finset.coe_subset.2 Finset.subset_union_left).trans hL)
  obtain ⟨r', hr'⟩ := ht L ((Finset.coe_subset.2 Finset.subset_union_right).trans hL)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have gA := isGrpPullback_bcMap A L.val
  have gB := isGrpPullback_bcMap B L.val
  obtain ⟨hepi, hmon⟩ := FieldBaseChange.epi_and_isMonHom_iff L Ω L.val.toRingHom
  have eA := (hepi _ _ _ _ _ gA.1).1
  have eB := (hepi _ _ _ _ _ gB.1).1
  exact ⟨L, hfin, i', r', (hmon _ _ _ _ _ _ i' i gA gB hi').1 hi, (hmon _ _ _ _ _ _ r' r gB gA hr').1 hr,
    fun m => ⟨comp_eq_pow_of_epi gA hi' hr' m, comp_eq_pow_of_epi gB hr' hi' m⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelSmoothOfRelativeDimension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.Ord

theorem model_smoothOfRelativeDimension {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {A : Over (Sp K)} {d : ℕ} (hA : SmoothOfRelativeDimension d A.hom) (M : Model R A) :
    SmoothOfRelativeDimension d M.Y.hom := by
  have := M.smooth
  choose n W hW hd using H1.exists_dim M.Y.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  have hne : ∃ y : A.left, M.j y ∈ W x := by
    by_contra hc
    have e : M.j ⁻¹ᵁ W x = ⊥ := le_bot_iff.1 fun y hy => (hc ⟨y, hy⟩).elim
    have h1 : Subsingleton Γ(A.left, M.j ⁻¹ᵁ W x) := by rw [e]; infer_instance
    have h2 : Subsingleton Γ(M.Y.left, W x) := (j_app_injective M (W x)).subsingleton
    have : Nonempty (W x) := ⟨⟨x, hW x⟩⟩
    exact not_subsingleton _ h2
  obtain ⟨y, hy⟩ := hne
  rw [← H1.dim_base (isPullback_j M) (hd x) hA y hy]
  exact hd x

theorem exists_etale_coord : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (I : Type) [Fintype I], SmoothOfRelativeDimension (Fintype.card I) A.hom → ∀ (M : Model R A) (x : M.Y.left) (O : M.Y.left.Opens), x ∈ O → ∃ (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)), IsAffineOpen U ∧ x ∈ U ∧ U ≤ O ∧ (MvPolynomial.eval₂Hom (cst M U) t).Etale := by
  intro R K _ _ _ _ _ _ A I _ hA M x O hx
  have hM := model_smoothOfRelativeDimension hA M
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (Fintype.card I)) M.Y.hom hM
    ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨g, hg⟩, hxg⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen g
  have h1 := h' g hg Γ(M.Y.left, M.Y.left.basicOpen g)
  have h2 : (cst M (M.Y.left.basicOpen g)).IsStandardSmoothOfRelativeDimension (Fintype.card I) := by
    have h3 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
    have e : cst M (M.Y.left.basicOpen g) = (rs _ (M.Y.left.basicOpen_le g)).comp (cst M W) :=
      RingHom.ext fun r => (rs_cst M (M.Y.left.basicOpen_le g) r).symm
    rw [e]
    exact h3
  obtain ⟨φ, hC, hφ⟩ := h2.exists_etale_mvPolynomial
  let e := Fintype.equivFin I
  refine ⟨M.Y.left.basicOpen g, fun i => φ (MvPolynomial.X (e i)), hW.basicOpen g, hxg,
    (M.Y.left.basicOpen_le g).trans hWO, ?_⟩
  have h4 := RingHom.Etale.respectsIso.2 φ (MvPolynomial.renameEquiv R e).toRingEquiv hφ
  convert h4 using 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [← hC]
  · simp

end GlobalTheory.SS.Ord
end
end

