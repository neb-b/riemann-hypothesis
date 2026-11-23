module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedUniformisationIsoOneLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.Mum.Two.GlueLevel

section General

variable {X₁ X₂ B₁ B₂ H₁ H₂ : Scheme.{0}} {M₁ : LB B₁} {M₂ : LB B₂} {L₁ : LB H₁} {L₂ : LB H₂}

theorem map_inl_apply (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₁) :
    (coprod.map f₁ f₂) ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x) = (coprod.inl : B₁ ⟶ B₁ ⨿ B₂) (f₁ x) := by
  change ((coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ coprod.map f₁ f₂) x = _
  rw [coprod.inl_map]; rfl

theorem map_inr_apply (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₂) :
    (coprod.map f₁ f₂) ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x) = (coprod.inr : B₂ ⟶ B₁ ⨿ B₂) (f₂ x) := by
  change ((coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ coprod.map f₁ f₂) x = _
  rw [coprod.inr_map]; rfl

theorem mem_pull_inl (M₁ : LB B₁) (M₂ : LB B₂) (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₁)
    (J : PUnit → (join M₁ M₂).ι) :
    (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈ ((join M₁ M₂).pull (coprod.map f₁ f₂)).U J ↔
      x ∈ (M₁.pull f₁).U (fun _ => (J PUnit.unit).1) := by
  rw [mem_pull, mem_pull, map_inl_apply]
  exact (isPart_inl M₁ M₂).mem _ _

theorem mem_pull_inr (M₁ : LB B₁) (M₂ : LB B₂) (f₁ : X₁ ⟶ B₁) (f₂ : X₂ ⟶ B₂) (x : X₂)
    (J : PUnit → (join M₁ M₂).ι) :
    (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈ ((join M₁ M₂).pull (coprod.map f₁ f₂)).U J ↔
      x ∈ (M₂.pull f₂).U (fun _ => (J PUnit.unit).2) := by
  rw [mem_pull, mem_pull, map_inr_apply]
  exact (isPart_inr M₁ M₂).mem _ _

end General

section Glue

variable {X₁ X₂ B₁ B₂ H₁ H₂ : Scheme.{0}} {M₁ : LB B₁} {M₂ : LB B₂} {L₁ : LB H₁} {L₂ : LB H₂}
  {p₁ : X₁ ⟶ B₁} {p₂ : X₂ ⟶ B₂} {f₁ : X₁ ⟶ H₁} {f₂ : X₂ ⟶ H₂}

theorem gm_div_inl (x : X₁) (i j : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι))
    (hi : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U i)
    (hj : (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U j) :
    gm coprod.inl x _
        ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).g i j) =
      gm (𝟙 X₁) x _ ((LB.div (M₁.pull p₁) (L₁.pull f₁)).g
        (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1)
        (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1)) := by
  obtain ⟨I₁, K₁⟩ := i
  obtain ⟨I₂, K₂⟩ := j
  have a₁ := mem_pull.1 hi.1
  have a₂ := mem_pull.1 hj.1
  have b₁ := mem_pull.1 hi.2
  have b₂ := mem_pull.1 hj.2
  rw [map_inl_apply] at a₁ a₂ b₁ b₂
  have a₁' := ((isPart_inl M₁ M₂).mem _ _).1 a₁
  have a₂' := ((isPart_inl M₁ M₂).mem _ _).1 a₂
  have b₁' := ((isPart_inl L₁ L₂).mem _ _).1 b₁
  have b₂' := ((isPart_inl L₁ L₂).mem _ _).1 b₂
  have d := gm_div_g (L := join M₁ M₂) (F := coprod.map p₁ p₂) (L' := (join L₁ L₂).pull (coprod.map f₁ f₂))
    coprod.inl x (I₁ PUnit.unit) (I₂ PUnit.unit) K₁ K₂ (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
  have d₁ := gm_div_g (L := M₁) (F := p₁) (L' := L₁.pull f₁) (𝟙 X₁) x (I₁ PUnit.unit).1 (I₂ PUnit.unit).1
    (fun _ => (K₁ PUnit.unit).1) (fun _ => (K₂ PUnit.unit).1) a₁' a₂' (mem_pull.2 b₁') (mem_pull.2 b₂')
  refine d.trans (Eq.trans ?_ d₁.symm)
  rw [gm_pull_g (join L₁ L₂) (coprod.map f₁ f₂) coprod.inl x K₁ K₂ hi.2 hj.2,
    gm_pull_g L₁ f₁ (𝟙 X₁) x _ _ (mem_pull.2 b₁') (mem_pull.2 b₂'), coprod.inl_map, coprod.inl_map,
    (isPart_inl M₁ M₂).g _ p₁ x _ _ a₁' a₂', (isPart_inl L₁ L₂).g _ f₁ x _ _ b₁' b₂', Category.id_comp,
    Category.id_comp]

theorem gm_div_inr (x : X₂) (i j : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι))
    (hi : (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U i)
    (hj : (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) x ∈
      (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U j) :
    gm coprod.inr x _
        ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).g i j) =
      gm (𝟙 X₂) x _ ((LB.div (M₂.pull p₂) (L₂.pull f₂)).g
        (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2)
        (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2)) := by
  obtain ⟨I₁, K₁⟩ := i
  obtain ⟨I₂, K₂⟩ := j
  have a₁ := mem_pull.1 hi.1
  have a₂ := mem_pull.1 hj.1
  have b₁ := mem_pull.1 hi.2
  have b₂ := mem_pull.1 hj.2
  rw [map_inr_apply] at a₁ a₂ b₁ b₂
  have a₁' := ((isPart_inr M₁ M₂).mem _ _).1 a₁
  have a₂' := ((isPart_inr M₁ M₂).mem _ _).1 a₂
  have b₁' := ((isPart_inr L₁ L₂).mem _ _).1 b₁
  have b₂' := ((isPart_inr L₁ L₂).mem _ _).1 b₂
  have d := gm_div_g (L := join M₁ M₂) (F := coprod.map p₁ p₂) (L' := (join L₁ L₂).pull (coprod.map f₁ f₂))
    coprod.inr x (I₁ PUnit.unit) (I₂ PUnit.unit) K₁ K₂ (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
  have d₁ := gm_div_g (L := M₂) (F := p₂) (L' := L₂.pull f₂) (𝟙 X₂) x (I₁ PUnit.unit).2 (I₂ PUnit.unit).2
    (fun _ => (K₁ PUnit.unit).2) (fun _ => (K₂ PUnit.unit).2) a₁' a₂' (mem_pull.2 b₁') (mem_pull.2 b₂')
  refine d.trans (Eq.trans ?_ d₁.symm)
  rw [gm_pull_g (join L₁ L₂) (coprod.map f₁ f₂) coprod.inr x K₁ K₂ hi.2 hj.2,
    gm_pull_g L₂ f₂ (𝟙 X₂) x _ _ (mem_pull.2 b₁') (mem_pull.2 b₂'), coprod.inr_map, coprod.inr_map,
    (isPart_inr M₁ M₂).g _ p₂ x _ _ a₁' a₂', (isPart_inr L₁ L₂).g _ f₂ x _ _ b₁' b₂', Category.id_comp,
    Category.id_comp]

theorem exists_iso_glue (w₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (w₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂))
    (hw₁ : w₁.IsGen) (hw₂ : w₂.IsGen) :
    ∃ W : LB.Iso ((join L₁ L₂).pull (coprod.map f₁ f₂)) ((join M₁ M₂).pull (coprod.map p₁ p₂)), W.IsGen ∧
      (∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : (join M₁ M₂).ι) (k : (join L₁ L₂).ι), p₁ (r z) ∈ M₁.U j.1 →
        f₁ (r z) ∈ L₁.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw w₁ r z j.1 (fun _ => k.1)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X₂) (z : Z) (j : (join M₁ M₂).ι) (k : (join L₁ L₂).ι), p₂ (r z) ∈ M₂.U j.2 →
        f₂ (r z) ∈ L₂.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw w₂ r z j.2 (fun _ => k.2) := by
  have key : ∀ p : (PUnit → (join M₁ M₂).ι) × (PUnit → (join L₁ L₂).ι),
      ∃ a : Γ(X₁ ⨿ X₂,
        (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p)ˣ,
      (∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₁) (z : Z), (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) (ψ z) ∈
          (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p →
        gm (ψ ≫ coprod.inl) z _ a =
          gm ψ z _ (w₁.s (fun _ => (p.1 PUnit.unit).1, fun _ => (p.2 PUnit.unit).1))) ∧
      ∀ (Z : Scheme.{0}) (ψ : Z ⟶ X₂) (z : Z), (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) (ψ z) ∈
          (LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p →
        gm (ψ ≫ coprod.inr) z _ a =
          gm ψ z _ (w₂.s (fun _ => (p.1 PUnit.unit).2, fun _ => (p.2 PUnit.unit).2)) := fun p =>
    exists_glue ((LB.div ((join M₁ M₂).pull (coprod.map p₁ p₂)) ((join L₁ L₂).pull (coprod.map f₁ f₂))).U p)
      ((LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (p.1 PUnit.unit).1, fun _ => (p.2 PUnit.unit).1))
      ((LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (p.1 PUnit.unit).2, fun _ => (p.2 PUnit.unit).2))
      (fun x hx => ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.2⟩)
      (fun x hx => ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.2⟩) _ _
  choose s hs₁ hs₂ using key
  let W : LB.Iso ((join L₁ L₂).pull (coprod.map f₁ f₂)) ((join M₁ M₂).pull (coprod.map p₁ p₂)) := ⟨s⟩
  refine ⟨W, fun i j => unit_ext_coprod (fun x hx => ?_) (fun x hx => ?_), fun Z r z j k hj hk => ?_,
    fun Z r z j k hj hk => ?_⟩
  · have e₁ := hs₁ i X₁ (𝟙 _) x hx.1
    have e₂ := hs₁ j X₁ (𝟙 _) x hx.2
    rw [Category.id_comp] at e₁ e₂
    have m₁ : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U
        (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1) :=
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.1.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.1.2⟩
    have m₂ : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U
        (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1) :=
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ x _).1 hx.2.1, (mem_pull_inl L₁ L₂ f₁ f₂ x _).1 hx.2.2⟩
    have h := congrArg (gm (𝟙 X₁) x _) (hw₁ (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1)
      (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1))
    have m : x ∈ (LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (i.1 PUnit.unit).1, fun _ => (i.2 PUnit.unit).1) ⊓
        (LB.div (M₁.pull p₁) (L₁.pull f₁)).U (fun _ => (j.1 PUnit.unit).1, fun _ => (j.2 PUnit.unit).1) := ⟨m₁, m₂⟩
    rw [map_mul, gm_res _ x _ m, gm_res _ x _ m] at h
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_div_inl x i j hx.1 hx.2]
    exact e₁.trans (h.trans (congrArg _ e₂.symm))
  · have e₁ := hs₂ i X₂ (𝟙 _) x hx.1
    have e₂ := hs₂ j X₂ (𝟙 _) x hx.2
    rw [Category.id_comp] at e₁ e₂
    have m₁ : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U
        (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2) :=
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.1.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.1.2⟩
    have m₂ : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U
        (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2) :=
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ x _).1 hx.2.1, (mem_pull_inr L₁ L₂ f₁ f₂ x _).1 hx.2.2⟩
    have h := congrArg (gm (𝟙 X₂) x _) (hw₂ (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2)
      (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2))
    have m : x ∈ (LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (i.1 PUnit.unit).2, fun _ => (i.2 PUnit.unit).2) ⊓
        (LB.div (M₂.pull p₂) (L₂.pull f₂)).U (fun _ => (j.1 PUnit.unit).2, fun _ => (j.2 PUnit.unit).2) := ⟨m₁, m₂⟩
    rw [map_mul, gm_res _ x _ m, gm_res _ x _ m] at h
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_div_inr x i j hx.1 hx.2]
    exact e₁.trans (h.trans (congrArg _ e₂.symm))
  · exact hs₁ (fun _ => j, fun _ => k) Z r z
      ⟨(mem_pull_inl M₁ M₂ p₁ p₂ _ _).2 (mem_pull.2 hj), (mem_pull_inl L₁ L₂ f₁ f₂ _ _).2 (mem_pull.2 hk)⟩
  · exact hs₂ (fun _ => j, fun _ => k) Z r z
      ⟨(mem_pull_inr M₁ M₂ p₁ p₂ _ _).2 (mem_pull.2 hj), (mem_pull_inr L₁ L₂ f₁ f₂ _ _).2 (mem_pull.2 hk)⟩

end Glue

theorem exists_iso_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ), ∃ W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left)), W.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e
  exact exists_iso_glue (U₁.w e) (U₂.w e) (U₁.w_gen e) (U₂.w_gen e)

end GlobalTheory.Mum.Two.GlueLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodLevelMultipleSameAdelicPart
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Pointwise

namespace GlobalTheory.GoodMultipleLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coprime_M_N {M d : ℕ} (hM : M ≠ 0) (hd : d.Prime) (hd2 : d ≠ 2) :
    Nat.Coprime M ((2 * (M / d ^ M.factorization d)) ^ 2 + d) := by
  set c := M / d ^ M.factorization d with hc
  have hnc : ¬ d ∣ c := Nat.not_dvd_ordCompl hd hM
  have hmul : d ^ M.factorization d * c = M := Nat.ordProj_mul_ordCompl_eq_self M d
  apply Nat.coprime_of_dvd
  intro q hq hqM hqN
  have hqd : q ∣ d → q = d := fun h => (Nat.prime_dvd_prime_iff_eq hq hd).1 h
  by_cases hqc : q ∣ c
  · have h1 : q ∣ (2 * c) ^ 2 := Dvd.dvd.pow (Dvd.dvd.mul_left hqc 2) two_ne_zero
    have h2 : q ∣ d := (Nat.dvd_add_right h1).1 hqN
    exact hnc (hqd h2 ▸ hqc)
  · rw [← hmul] at hqM
    have h1 : q ∣ d ^ M.factorization d := ((Nat.Prime.dvd_mul hq).1 hqM).resolve_right hqc
    have h2 := hqd (hq.dvd_of_dvd_pow h1)
    subst h2
    have h3 : q ∣ (2 * c) ^ 2 := (Nat.dvd_add_left (dvd_refl q)).1 hqN
    have h4 := (Nat.Prime.dvd_mul hq).1 (hq.dvd_of_dvd_pow h3)
    rcases h4 with h | h
    · exact hd2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
    · exact hnc h

theorem exists_good_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H),
    ∃ l₂ : Level H, l.Dvd l₂ ∧ l₂.A = l.A ∧ ∀ q : ℕ, q.Prime → l₂.GoodAt q := by
  intro E _ _ _ H l
  have hdm := H.d_mod
  have hdp := H.d_prime
  have hM3 := l.three_le
  have hM0 : l.M ≠ 0 := by omega
  set c := l.M / H.d ^ l.M.factorization H.d with hc
  set a : ℕ := 2 * c with ha
  set N : ℕ := a ^ 2 + H.d with hN
  have hcop : Nat.Coprime l.M N := coprime_M_N hM0 hdp (by omega)
  have hdodd : Odd H.d := Nat.odd_iff.mpr (by omega)
  have hNodd : Odd N := Even.add_odd ⟨2 * c ^ 2, by rw [ha]; ring⟩ hdodd
  have hN3 : 3 ≤ N := by omega
  have hcd : Nat.Coprime a H.d := by
    rw [ha]
    refine Nat.Coprime.mul_left (Nat.coprime_two_left.mpr hdodd) ?_
    exact ((Nat.Prime.coprime_iff_not_dvd hdp).2 (Nat.not_dvd_ordCompl hdp hM0)).symm
  set α : 𝓞 E := (a : 𝓞 E) + H.rt with hα
  have hαb : H.bar α = (a : 𝓞 E) - H.rt := by
    rw [hα, map_add (f := _), map_natCast, GlobalTheory.HostModel.bar_rt, sub_eq_add_neg]
  have hnorm : α * ((a : 𝓞 E) - H.rt) = (N : 𝓞 E) := GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H a
  have hαα : IsCoprime α ((a : 𝓞 E) - H.rt) := GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hcd hNodd
  have hαmem : α ∈ Algebra.adjoin ℤ {H.w0} := add_mem (natCast_mem _ a) (GlobalTheory.HostModel.rt_mem_adjoin H)
  have hmapI : (Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.map_span, Set.image_singleton]; exact congrArg _ (congrArg _ hαb)
  have hmapM : (l.Mb * Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.map_mul, hmapI]
  have hMN : Ideal.span {(l.M : 𝓞 E)} ⊔ Ideal.span {(N : 𝓞 E)} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact Nat.Coprime.cast hcop
  have hMle : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := by rw [← l.prod]; exact Ideal.mul_le_left
  have hMle' : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [← l.prod]; exact Ideal.mul_le_right
  have hNle : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {α} := by
    rw [Ideal.span_singleton_le_span_singleton, ← hnorm]; exact dvd_mul_right _ _
  have hNle' : Ideal.span {(N : 𝓞 E)} ≤ Ideal.span {(a : 𝓞 E) - H.rt} := by
    rw [Ideal.span_singleton_le_span_singleton, ← hnorm]; exact dvd_mul_left _ _
  have c1 : IsCoprime l.Mb (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.isCoprime_iff_sup_eq.2 l.coprime
  have c2 : IsCoprime l.Mb (Ideal.span {(a : 𝓞 E) - H.rt}) := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]; exact sup_le_sup hMle hNle'
  have c3 : IsCoprime (Ideal.span {α}) (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by
    rw [Ideal.isCoprime_iff_sup_eq, eq_top_iff, ← hMN]
    exact sup_le (le_sup_of_le_right hMle') (le_sup_of_le_left hNle)
  have c4 : IsCoprime (Ideal.span {α}) (Ideal.span {(a : 𝓞 E) - H.rt}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 hαα
  have hspan : l.Mb * Ideal.span {α} = Ideal.span ({x | x ∈ l.Mb ∧ x ∈ Algebra.adjoin ℤ {H.w0}} * ({α} : Set (𝓞 E))) := by
    conv_lhs => rw [l.fromK]
    exact Ideal.span_mul_span' _ _
  let l₂ : Level H :=
    { M := l.M * N
      three_le := by nlinarith
      odd := l.odd.mul hNodd
      Mb := l.Mb * Ideal.span {α}
      fromK := by
        refine le_antisymm ?_ (Ideal.span_le.2 fun x hx => hx.1)
        refine (le_of_eq hspan).trans (Ideal.span_mono ?_)
        rintro x ⟨s, hs, t, ht, rfl⟩
        rw [Set.mem_singleton_iff] at ht
        subst ht
        refine ⟨?_, mul_mem hs.2 hαmem⟩
        exact Ideal.mul_mem_mul hs.1 (Ideal.mem_span_singleton_self _)
      prod := by
        rw [hmapM]
        calc l.Mb * Ideal.span {α} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) * Ideal.span {(a : 𝓞 E) - H.rt})
            = (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) * (Ideal.span {α} * Ideal.span {(a : 𝓞 E) - H.rt}) := by ring
          _ = Ideal.span {((l.M * N : ℕ) : 𝓞 E)} := by
            rw [l.prod, Ideal.span_singleton_mul_span_singleton, hnorm,
              Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]
      coprime := by
        rw [hmapM, ← Ideal.isCoprime_iff_sup_eq]
        exact (c1.mul_right c2).mul_left (c3.mul_right c4)
      A := l.A
      A_pos := l.A_pos }
  refine ⟨l₂, ⟨dvd_mul_right _ _, Ideal.mul_le_left, dvd_refl _⟩, rfl, fun q hq => ?_⟩
  exact GlobalTheory.GlobalModelGuards.goodAt_of_coprime l₂ l.M N hM3 hN3 hcop rfl q hq

end GlobalTheory.GoodMultipleLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedDataCompleteDVRExtension
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

noncomputable section

namespace GlobalTheory.FramedExt

theorem eSec_hom {S : Scheme.{0}} (X : Over S) [GrpObj X] : eSec X ≫ X.hom = 𝟙 _ := by
  simp [eSec]

theorem dualMapR_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_ext {R R' : Type} [CommRing R] [CommRing R'] (F₁ F₂ : DualNumber R →+* DualNumber R')
    (h : ∀ a : R, F₁ (algebraMap R (DualNumber R) a) = F₂ (algebraMap R (DualNumber R) a))
    (hε : F₁ DualNumber.eps = F₂ DualNumber.eps) : F₁ = F₂ := by
  refine RingHom.ext fun x => ?_
  have hx : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, h, h, hε]

theorem generates_of_flat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {R R₂ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R₂] [IsDomain R₂] (φ : R →+* R₂) (hφ : Function.Injective φ) (G : SAB H (Sp R)) (G₂ : SAB H (Sp R₂)) (m : SABMap G₂ G (spMap φ)) (wI : G₂.PP.L.Iso (G.PP.L.pull m.φ)) (hwI : LB.Gen.IsGen wI) (θ : G.PP.L.Sec) (θ₂ : G₂.PP.L.Sec) (hθ : IsoMaps wI θ₂ (thfPull G.PP.L m.φ θ)) : Generates (X := G.G) θ → Generates (X := G₂.G) θ₂ := by
  intro hgen
  letI := φ.toAlgebra
  have : FaithfulSMul R R₂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : Module.Flat R R₂ := inferInstance
  haveI : IsSeparated G.G.hom := G.semi.separated
  haveI : QuasiCompact G.G.hom := G.semi.quasiCompact
  haveI : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
  have hinter : ∀ U W : G.G.left.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal G.G.hom)) ⊤
      (isAffineOpen_top _) U le_top W le_top hU hW
  have Hpb : IsPullback m.φ G₂.G.hom G.G.hom (Spec.map (CommRingCat.ofHom (algebraMap R R₂))) := m.cart.1
  exact fun s' => ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flatBC_iso G.G.hom G₂.G.hom m.φ Hpb hinter G.PP.L G.PP.isLB θ hgen
    G₂.PP.L G₂.PP.isLB wI hwI θ₂ _ hθ (fun _ _ => rfl) s'

theorem isFibreOf_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (θ : L.Sec) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (k : KeyIn R') (k' : KeyIn R'') (f : R →+* R') (g : R' →+* R'') : IsFibreOf k G L rig θ w f → KeyPB k' k g → IsFibreOf k' G L rig θ w (g.comp f) := by
  intro H H'
  obtain ⟨φ, he, w₀, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g₀ := (isGen_iff w₀).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp k.P.isLB w₀ w' g₀ g' hL k'.P.isLB
  have he'' : eSec k'.P.A ≫ φ' ≫ φ = spMap (g.comp f) ≫ eSec G := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f g).symm rfl,
    (isGen_iff w'').2 (T.pgen_comp k.P.isLB g₀ g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w₀ _ (fun _ => eSec G) _ k.rig rig (spMap f) _
      (rigPull_le φ (spMap f) he L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec k.P.A) _ k'.rig k.rig (spMap g) _
      (rigPull_le φ' (spMap g) he' k.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp k.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec G) _ k'.rig rig (spMap (g.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (g.comp f)) he'' L) (fun _ => rfl)).2 r₂
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk w'' θ k'.th fun z j k₀ hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart k.P.isLB (φ' z)
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq w₀ θ k.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq w' k.th k'.th hs' (𝟙 _) z i k₀ hi hk
    rw [T _ (𝟙 _) z j i k₀ hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

theorem isFibreOf_descend {R R₂ K : Type} [CommRing R] [CommRing R₂] [CommRing K] (φ : R →+* R₂) (f : R₂ →+* K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (L₂ : LB G₂.left) (hL₂ : L₂.IsLB) (rig₂ : (L₂.pull (eSec G₂)).Gen) (ψ : G₂.left ⟶ G.left) (hψ : IsGrpPullback G₂ G (spMap φ) ψ) (he : eSec G₂ ≫ ψ = spMap φ ≫ eSec G) (wI : L₂.Iso (L.pull ψ)) (hwI : LB.Gen.IsGen wI) (hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂) fun _ => 1) rig₂ (rigPullOf ψ (spMap φ) he L rig)) (θ : L.Sec) (θ₂ : L₂.Sec) (hθ : IsoMaps wI θ₂ (thfPull L ψ θ)) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (w₂ : Fin n → (epsR R₂ ⟶ G₂)) (hw : ∀ i, (w₂ i).left ≫ ψ = spMap (Chart.dualMapR φ) ≫ (w i).left) (k : KeyIn K) : IsFibreOf k G L rig θ w (f.comp φ) → IsFibreOf k G₂ L₂ rig₂ θ₂ w₂ f := by
  intro H
  obtain ⟨φk, hek, e, hg, F, hp, hgen, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨ψ₂, hfac, hbase⟩ : ∃ ψ₂ : k.P.A.left ⟶ G₂.left, ψ₂ ≫ ψ = φk ∧ ψ₂ ≫ G₂.hom = k.P.A.hom ≫ spMap f :=
    ⟨hψ.1.lift φk (k.P.A.hom ≫ spMap f) (by rw [hp.1.w, spMap_comp, Category.assoc]),
      hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  subst hfac
  have hp₂ : IsGrpPullback k.P.A G₂ (spMap f) ψ₂ := hψ.cancel (hp.congr (spMap_comp φ f) rfl) hbase
  have he₂ : eSec k.P.A ≫ ψ₂ = spMap f ≫ eSec G₂ := by
    apply hψ.1.hom_ext
    · rw [Category.assoc, hek, Category.assoc, he, spMap_comp, Category.assoc]
    · rw [Category.assoc, hbase, ← Category.assoc, eSec_hom, Category.assoc, eSec_hom]
      simp
  have gI := (isGen_iff wI).1 hwI
  have g₀ := (isGen_iff e).1 hgen
  obtain ⟨e₂, T⟩ := exists_cancel hL wI e gI g₀ hL₂ k.P.isLB
  have hFe : F = (Chart.dualMapR f).comp (Chart.dualMapR φ) := dual_ext _ _ (fun a => by
      simp only [hF, RingHom.comp_apply]
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by rw [hε]; ext <;> simp [Chart.dualMapR])
  refine ⟨ψ₂, he₂, e₂, hg, Chart.dualMapR f, hp₂, (isGen_iff e₂).2 (T.pgen_cancel hL gI g₀), ?_, ?_,
    fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff wI _ (fun _ => eSec G) _ rig₂ rig (spMap φ) _
      (rigPull_le ψ (spMap φ) he L) (fun _ => rfl)).1 hrig
    have r'' := (maps_iff e _ (fun _ => eSec G) _ k.rig rig (spMap (f.comp φ)) _
      (rigPull_le (ψ₂ ≫ ψ) (spMap (f.comp φ)) hek L) (fun _ => rfl)).1 hr
    rw [spMap_comp] at r''
    have r₂ := T.pmaps_cancel hL (fun _ => he₂) r₀ r''
    exact (maps_iff e₂ _ (fun _ => eSec G₂) _ k.rig rig₂ (spMap f) _
      (rigPull_le ψ₂ (spMap f) he₂ L₂) (fun _ => rfl)).2 r₂
  · have hθ' : ∀ (j : (L.pull ψ).ι) (i : L₂.ι) (hle : (L.pull ψ).U j ⊓ L₂.U i ≤ ψ ⁻¹ᵁ L.U (j PUnit.unit)),
        (Scheme.Hom.appLE ψ (L.U (j PUnit.unit)) ((L.pull ψ).U j ⊓ L₂.U i) hle).hom (θ.f (j PUnit.unit)) =
          (show Γ(G₂.left, (L.pull ψ).U j ⊓ L₂.U i) from (wI.s (j, i)).val) * resG _ inf_le_right (θ₂.f i) := by
      intro j i hle
      refine Eq.trans ?_ (hθ j i)
      dsimp only [thfPull]
      first
        | (erw [Scheme.Hom.appLE_map])
        | (simp only [Scheme.Hom.appLE_map])
        | (rw [← Scheme.Hom.appLE_map ψ _ (homOfLE inf_le_left).op]; rfl)
    refine GlobalTheory.KeyPow.appLE_eq_of_stalk e₂ θ₂ k.th fun z j k₀ hj hk => ?_
    obtain ⟨jL, hjL⟩ := exists_chart hL (ψ (ψ₂ z))
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq e θ k.th hs (𝟙 _) z jL k₀ hjL hk
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq wI θ θ₂ hθ' (𝟙 _ ≫ ψ₂) z jL j hjL hj
    rw [Category.assoc] at b
    rw [T _ (𝟙 _) z jL j k₀ hjL hj hk, b, Units.val_mul, _root_.mul_assoc] at a
    exact (Units.mul_right_inj _).1 a
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hψ.1.hom_ext
    · rw [Category.assoc, hv i, Category.assoc, hw, ← Category.assoc, hFe, spMap_comp]
    · rw [Category.assoc, hbase, ← Category.assoc, Over.w (k.v i), Category.assoc, Over.w (w₂ (Fin.cast hg i))]
      simp only [epsR, Over.mk_hom]
      rw [← spMap_comp, ← spMap_comp, dualMapR_comp_algebraMap]

theorem exists_framed_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  intro E _ _ _ H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  have hφ' : (algebraMap T'.V T'.Fr).comp φ = iT.comp (algebraMap T.V T.Fr) := RingHom.ext hφ
  have hsq : spMap iT ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp, hφ']
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → SABMap s' s f →
      Nonempty (SABMap s' s g) := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m⟩
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G₂ : SAB H (Sp T'.V), Nonempty (SABMap G₂ G (spMap φ)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, ⟨p⟩⟩ : ∃ t₂ : SAB H (Sp T'.Fr), Nonempty (SABMap t₂ t' (spMap iT)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap iT) t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨a₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 p
  obtain ⟨b₂⟩ := tr hsq a₂
  obtain ⟨m2', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b₂
  obtain ⟨w', hw', hww⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ G.G G₂.G m.φ m.cart G.semi.smooth n w hw
  obtain ⟨k', hk'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring k iT
  obtain ⟨wI, hwI, hrI, -⟩ := m.lin
  obtain ⟨θ₂, hθ₂⟩ := GlobalTheory.ArcQ.NormalForm.exists_isoMaps wI hwI G.PP.isLB G₂.PP.isLB (thfPull G.PP.L m.φ θ)
  have he : eSec G₂.G ≫ m.φ = spMap φ ≫ eSec G.G := m.cm.e_comm.trans (congrArg (· ≫ eSec G.G) m.base)
  have hr : ∀ (e : Sp T'.V ⟶ Sp T.V) (_ : m.cm.e = e) (he : eSec G₂.G ≫ m.φ = e ≫ eSec G.G),
      rigPullOf m.φ e he G.PP.L G.PP.rig = m.cm.rigPull G.PP.L G.PP.rig := by
    rintro _ rfl _
    rfl
  have hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂.G) fun _ => 1) G₂.PP.rig
      (rigPullOf m.φ (spMap φ) he G.PP.L G.PP.rig) := by
    rw [hr _ m.base he]; exact hrI
  have h1 := isFibreOf_trans G.G G.PP.L G.PP.isLB G.PP.rig θ w k k' (algebraMap T.V T.Fr) iT hk hk'
  rw [← hφ'] at h1
  have hinj : Function.Injective φ := fun a b hab => IsFractionRing.injective T.V T.Fr
    (iT.injective (by rw [← hφ a, ← hφ b, hab]))
  exact ⟨G₂, t₂, p, m2', n, w', θ₂, k', hw', generates_of_flat φ hinj G G₂ m wI hwI θ θ₂ hθ₂ hθ,
    isFibreOf_descend φ (algebraMap T'.V T'.Fr) G.G G₂.G G.PP.L G.PP.isLB G.PP.rig G₂.PP.L G₂.PP.isLB G₂.PP.rig m.φ
      m.cart he wI hwI hrig θ θ₂ hθ₂ w w' hww k' h1, hk'⟩

end GlobalTheory.FramedExt
end
end

