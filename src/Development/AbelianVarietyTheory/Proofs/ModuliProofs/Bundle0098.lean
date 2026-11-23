module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfQuotientOfRigid
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace SabMapDescent

section Bundles

variable {X Y : Scheme.{0}}

def chartPullDivPull (A B : LB X) (h : Y ⟶ X) :
    ChartPull ((LB.div B A).pull h) (LB.div (B.pull h) (A.pull h)) (𝟙 Y) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have b := mem_pull.1 hj'
    refine (gm_pull_g _ h (𝟙 Y) y J J' hj hj').trans ((gm_div A B (𝟙 Y ≫ h) y _ _ ⟨a, b⟩).trans (Eq.symm ?_))
    refine (gm_div (A.pull h) (B.pull h) (𝟙 Y) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, ⟨mem_pull.2 b.1, mem_pull.2 b.2⟩⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹) (gm_pull_g B h (𝟙 Y) y _ _ (mem_pull.2 a.1) (mem_pull.2 b.1))
      (gm_pull_g A h (𝟙 Y) y _ _ (mem_pull.2 a.2) (mem_pull.2 b.2))

theorem lbIso_of_gen_of_gen {A B : LB X} (s : A.Gen) (hs : s.IsGen) (t : B.Gen) (ht : t.IsGen) : LBIso A B := by
  refine ⟨⟨fun p => res (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ _) (t.s p.1) *
    (res (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ _) (s.s p.2))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have v : ∀ p : B.ι × A.ι, y ∈ B.U p.1 ⊓ A.U p.2 → gm (𝟙 X) y (B.U p.1 ⊓ A.U p.2)
      (res (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ _) (t.s p.1) *
        (res (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ _) (s.s p.2))⁻¹) =
      gm (𝟙 X) y _ (t.s p.1) * (gm (𝟙 X) y _ (s.s p.2))⁻¹ := fun p hp => by
    rw [map_mul, map_inv, gm_res _ y _ hp, gm_res _ y _ hp]
  have w : ∀ {C : LB X} (c : C.Gen), c.IsGen → ∀ i j, y ∈ C.U i → y ∈ C.U j →
      gm (𝟙 X) y _ (c.s i) = gm (𝟙 X) y _ (C.g i j) * gm (𝟙 X) y _ (c.s j) := fun {C} c hc i j hi hj => by
    have hm : (𝟙 X : X ⟶ X) y ∈ C.U i ⊓ C.U j := ⟨hi, hj⟩
    have := congrArg (gm (𝟙 X) y _) (hc i j)
    rwa [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at this
  refine ((gm_res _ y _ hy _).trans (v p hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [w t ht p.1 q.1 hy.1.1 hy.2.1, w s hs p.2 q.2 hy.1.2 hy.2.2, mul_inv, _root_.mul_mul_mul_comm]

end Bundles

def IsQuot {Γ : Type} [Group Γ] {X X' : Scheme.{0}} (ρ : Γ →* Aut X) (π : X ⟶ X') : Prop :=
  IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧
    ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) →
      f ∈ Set.range (π.app V).hom

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem IsQuot.epi {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π) : Epi π :=
  ⟨fun {T} a b e => (quotient_existsUnique_comp_eq Γ X X' ρ π h T (π ≫ a)
    fun g => by rw [← Category.assoc, h.2.1 g]).unique rfl e.symm⟩

theorem IsQuot.epi_of_isPullback {X X' Y Y' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π)
    {φ : Y ⟶ Y'} {p : Y ⟶ X} {p' : Y' ⟶ X'} (H : IsPullback φ p p' π) (hp : Flat p') : Epi φ := by
  have hbase := quotient_flat_baseChange Γ X X' Y Y' ρ π φ p p' h H hp
  obtain ⟨hex, hall⟩ := hbase
  obtain ⟨τ, hτ⟩ := hex
  exact IsQuot.epi (hall τ hτ)

omit [Finite Γ] in
theorem IsQuot.isReduced {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π) [IsReduced X] :
    IsReduced X' :=
  ⟨fun V => isReduced_of_injective (π.app V).hom (h.2.2 V).1⟩

theorem exists_isPullback {U U' X' P P' P₁ : Scheme.{0}} {ρ : Γ →* Aut U} {r : U ⟶ U'} (hq : IsQuot ρ r)
    {j : U' ⟶ X'} {p : P ⟶ U} {p' : P' ⟶ U'} {p₁ : P₁ ⟶ X'} [Flat p'] [Flat p₁] {φ : P ⟶ P'} {n : P ⟶ P₁}
    (hφ : IsPullback φ p p' r) (hn : IsPullback n p p₁ (r ≫ j)) (τ : Γ →* Aut P)
    (hτ : ∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom ∧ (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ n = n) :
    ∃ ψ : P' ⟶ P₁, φ ≫ ψ = n ∧ IsPullback ψ p' p₁ j := by
  have hφq : IsQuot τ φ := (quotient_flat_baseChange Γ U U' P P' ρ r φ p p' hq hφ inferInstance).2 τ
    fun g => ⟨(hτ g).2.1, (hτ g).1⟩
  have := hφq.epi
  obtain ⟨ψ, hψ, -⟩ := quotient_existsUnique_comp_eq Γ _ _ τ φ hφq _ n fun g => (hτ g).2.2
  have w : ψ ≫ p₁ = p' ≫ j := by
    rw [← cancel_epi φ, ← Category.assoc, hψ, hn.w, ← Category.assoc, ← hφ.w, Category.assoc]
  have H := IsPullback.of_hasPullback p₁ j
  let θ : P' ⟶ pullback p₁ j := pullback.lift ψ p' w
  have h₁ : θ ≫ pullback.fst p₁ j = ψ := pullback.lift_fst _ _ _
  have h₂ : θ ≫ pullback.snd p₁ j = p' := pullback.lift_snd _ _ _
  have hκ : IsPullback (φ ≫ θ) p (pullback.snd p₁ j) r :=
    IsPullback.of_right (by rw [Category.assoc, h₁, hψ]; exact hn) (by rw [Category.assoc, h₂, hφ.w]) H
  have hκq : IsQuot τ (φ ≫ θ) := (quotient_flat_baseChange Γ U U' P _ ρ r _ p _ hq hκ inferInstance).2 τ
    fun g => ⟨by rw [← Category.assoc, (hτ g).2.1], (hτ g).1⟩
  have := hκq.epi
  obtain ⟨σ, hσ, -⟩ := quotient_existsUnique_comp_eq Γ _ _ τ _ hκq _ φ fun g => (hτ g).2.1
  have : IsIso θ := ⟨σ, by rw [← cancel_epi φ, ← Category.assoc, hσ, Category.comp_id],
    by rw [← cancel_epi (φ ≫ θ), ← Category.assoc, hσ, Category.comp_id]⟩
  refine ⟨ψ, hψ, ?_⟩
  have := (IsPullback.of_horiz_isIso (fst := θ) (snd := p') (f := pullback.snd p₁ j) (g := 𝟙 U')
    ⟨by rw [h₂, Category.comp_id]⟩).paste_horiz H
  rwa [h₁, Category.id_comp] at this

theorem isGrpPullback_of_quot {U U' X' : Scheme.{0}} {ρ : Γ →* Aut U} {r : U ⟶ U'} (hq : IsQuot ρ r)
    {j : U' ⟶ X'} {G : Over U} {G' : Over U'} {G₁ : Over X'} [GrpObj G] [GrpObj G'] [GrpObj G₁] [Flat G'.hom]
    {φ : G.left ⟶ G'.left} {ψ : G'.left ⟶ G₁.left} (hφ : IsGrpPullback G G' r φ)
    (hn : IsGrpPullback G G₁ (r ≫ j) (φ ≫ ψ)) (hψ : IsPullback ψ G'.hom G₁.hom j) :
    IsGrpPullback G' G₁ j ψ := by
  have key : ∀ (T : Over U') (x y : T ⟶ G'), Flat T.hom →
      (pushPt hψ.w x * pushPt hψ.w y).left = (x * y).left ≫ ψ := by
    intro T x y hT
    have H := IsPullback.of_hasPullback T.hom r
    have := hq.epi_of_isPullback H hT
    let q := pullback.fst T.hom r
    let W : Over U := Over.mk (pullback.snd T.hom r)
    let l : (T ⟶ G') → (W ⟶ G) := fun z => Over.homMk
      (hφ.1.lift (q ≫ z.left) (pullback.snd T.hom r) (by rw [Category.assoc, Over.w z]; exact H.w))
      (hφ.1.lift_snd _ _ _)
    have hl : ∀ z, (l z).left ≫ φ = q ≫ z.left := fun z => hφ.1.lift_fst _ _ _
    let q' : Over.mk (W.hom ≫ r) ⟶ T := Over.homMk q H.w
    let q₁ : Over.mk (W.hom ≫ r ≫ j) ⟶ Over.mk (T.hom ≫ j) := Over.homMk q (by
      show q ≫ T.hom ≫ j = pullback.snd T.hom r ≫ r ≫ j
      rw [← Category.assoc, H.w, Category.assoc])
    have e₁ := hφ.2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
    have e₂ := hn.2 W (l x) (l y) (q₁ ≫ pushPt hψ.w x) (q₁ ≫ pushPt hψ.w y)
      (by rw [← Category.assoc (l x).left, hl, Category.assoc]; rfl)
      (by rw [← Category.assoc (l y).left, hl, Category.assoc]; rfl)
    rw [← MonObj.comp_mul] at e₁ e₂
    rw [← Category.assoc (l x * l y).left, ← e₁] at e₂
    rw [← cancel_epi q, ← Category.assoc q]
    exact e₂
  refine ⟨hψ, fun T x y x₀ y₀ hx hy => ?_⟩
  have hf : Flat (G' ⊗ G').hom := inferInstanceAs (Flat (pullback.fst G'.hom G'.hom ≫ G'.hom))
  have e := key (G' ⊗ G') (fst _ _) (snd _ _) hf
  let z : Over.mk (T.hom ≫ j) ⟶ Over.mk ((G' ⊗ G').hom ≫ j) := Over.homMk (lift x y).left (by
    show (lift x y).left ≫ (G' ⊗ G').hom ≫ j = T.hom ≫ j
    rw [← Category.assoc, Over.w])
  have hx' : x₀ = z ≫ pushPt hψ.w (fst _ _) := Over.OverMorphism.ext (by
    show _ = (lift x y).left ≫ (fst G' G').left ≫ ψ
    rw [← Category.assoc, ← Over.comp_left, lift_fst, hx])
  have hy' : y₀ = z ≫ pushPt hψ.w (snd _ _) := Over.OverMorphism.ext (by
    show _ = (lift x y).left ≫ (snd G' G').left ≫ ψ
    rw [← Category.assoc, ← Over.comp_left, lift_snd, hy])
  have hxy : x * y = lift x y ≫ (fst G' G' * snd G' G') := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [hx', hy', ← MonObj.comp_mul, hxy, Over.comp_left, e, Over.comp_left, Category.assoc]
  rfl

theorem subset_abLocus {S : Scheme.{0}} (G : Over S) [IsProper G.hom] (A : Set S) : A ⊆ abLocus G :=
  fun _ _ _ _ _ _ _ => inferInstance

end SabMapDescent


open SabMapDescent in
theorem exists_sabMap_of_quotient :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (U U' X' : Scheme.{0}) (ρ : Γ →* Aut U) (r : U ⟶ U') (t : SAB H U) (t' : SAB H U') (t₁ : SAB H X') (τ : Γ →* Aut t.G.left) (ν : SABMap t t' r) (j : U' ⟶ X') (n : SABMap t t₁ (r ≫ j)), (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsReduced U → IsProper t.G.hom → (∀ g, (τ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ g).asIso.hom ∧ (τ g).asIso.hom ≫ ν.φ = ν.φ ∧ (τ g).asIso.hom ≫ n.φ = n.φ) → ∃ n' : SABMap t' t₁ j, ν.φ ≫ n'.φ = n.φ := by
  intro E _ _ _ H Γ _ _ U U' X' ρ r t t' t₁ τ ν j n hq hred hprop hτ
  have hq : IsQuot ρ r := hq
  have := t.semi.smooth
  have := t.semi.geomConnected
  have := t'.semi.smooth
  have := t'.semi.separated
  have := t₁.semi.smooth
  obtain ⟨ψ, hψ, hpb⟩ := exists_isPullback hq ν.cart.1 n.cart.1 τ hτ
  have hgp : IsGrpPullback t'.G t₁.G j ψ := isGrpPullback_of_quot hq ν.cart (hψ ▸ n.cart) hpb
  have := hq.epi_of_isPullback ν.cart.1 inferInstance
  obtain ⟨hint, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ U U' ρ r hq
  have : Surjective ν.cm.F := MorphismProperty.of_isPullback (P := @Surjective) ν.cart.1.flip hsurj
  have : UniversallyClosed (ν.cm.F ≫ t'.G.hom) := by rw [ν.cart.1.w]; infer_instance
  have : UniversallyClosed t'.G.hom := .of_comp_surjective ν.cm.F _
  have : IsProper t'.G.hom := {}
  have he : eSec t.G ≫ t.G.hom = 𝟙 U := Over.w η[t.G]
  have he' : eSec t'.G ≫ t'.G.hom = 𝟙 U' := Over.w η[t'.G]
  have hiso : LBIso t'.PP.L (t₁.PP.L.pull ψ) := by
    refine exists_gen_of_quotient_of_rigid Γ U U' ρ r t.G t'.G ν.cm.F (eSec t.G) (eSec t'.G)
      (LB.div (t₁.PP.L.pull ψ) t'.PP.L) hq ν.cart.1 inferInstance he he' (by rw [ν.cm.e_comm, ν.base])
      (eq_one_of_appLE_section_eq_one U t.G _ he inferInstance
        (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) ⟨hred, subset_abLocus _ _⟩)
      (LB.isLB_div (pull_isLB t₁.PP.isLB ψ) t'.PP.isLB) ?_ ?_
    · obtain ⟨c, hc⟩ := gen_chartPull (chartPullLinComb t₁.PP.L ψ (K := PUnit) (fun _ => eSec t'.G)
        (fun _ => eSec t₁.G) (fun _ => 1) j fun _ => (cubeMapOf hgp).e_comm) t₁.PP.rig t₁.PP.rigGen
      obtain ⟨w, hw⟩ := lbIso_of_gen_of_gen t'.PP.rig t'.PP.rigGen c hc
      exact gen_chartPull (chartPullDivPull _ _ _) w hw
    · obtain ⟨a, ha, -⟩ := ν.lin
      obtain ⟨b, hb, -⟩ := n.lin
      have hb' : LBIso t.PP.L ((t₁.PP.L.pull ψ).pull ν.cm.F) :=
        LBIso.chartPull (chartPullId _) (chartPullLinComb t₁.PP.L ψ (K := PUnit) (fun _ => ν.cm.F)
          (fun _ => n.cm.F) (fun _ => 1) (𝟙 _) fun _ => hψ.trans (Category.id_comp _).symm) ⟨b, hb⟩
      obtain ⟨w, hw⟩ := LBIso.trans (pull_isLB t'.PP.isLB _) t.PP.isLB
        (pull_isLB (pull_isLB t₁.PP.isLB ψ) _) (LBIso.symm ⟨a, ha⟩) hb'
      exact gen_chartPull (chartPullDivPull _ _ _) w hw
  obtain ⟨n', hn'⟩ := GlobalTheory.exists_sabMap_of_lbIso E H X' U' t₁ t' j ψ ⟨hq.isReduced, subset_abLocus _ _⟩ hgp (fun a => by
    rw [← cancel_epi ν.cm.F, ← Category.assoc, ← ν.act, Category.assoc, hψ, n.act, ← Category.assoc, hψ]) hiso
  exact ⟨n', hn' ▸ hψ⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeomPtRangeEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem exists_geomPt_range_eq (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X), Set.range z = {g} := by
  let κ := X.residueField g
  let k := AlgebraicClosure κ
  refine ⟨k, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g, ?_⟩
  have hsub : Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g) ⊆ {g} := by
    rw [← X.range_fromSpecResidueField g]
    rintro _ ⟨p, rfl⟩
    exact ⟨_, rfl⟩
  have hne : (Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g)).Nonempty :=
    Set.range_nonempty _
  exact (Set.Nonempty.subset_singleton_iff hne).mp hsub

private lemma exists_factor_of_range_subset_closedImmersion {T N B : Scheme.{0}} [IsReduced T] (x : T ⟶ B) (ν : N ⟶ B)
    [IsClosedImmersion ν] (h : Set.range x ⊆ Set.range ν) : ∃ l : T ⟶ N, l ≫ ν = x := by
  have : Surjective (pullback.snd ν x) := ⟨fun t => by
    have ht : t ∈ Set.range (pullback.snd ν x) := by
      rw [Scheme.Pullback.range_snd]
      exact h ⟨t, rfl⟩
    exact ht⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd ν x)
  exact ⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem etSet_of_kerSet :
    ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') (K : Set G.left), IsSeparated G'.hom → IsFinite ψ.left → Etale ψ.left → KerSet ψ K → EtSet G K ∧ (IsReduced S → ∀ (C : Over S) (j : C ⟶ G), Etale C.hom → IsClosedImmersion j.left → Set.range j.left = K → IsPullback j (toUnit C) ψ η[G']) := by
  intro S G G' _ _ ψ K hsep hfin het hK
  have hew : (η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom = 𝟙 S := Over.w _
  have : IsClosedImmersion ((η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom) := by
    rw [hew]
    have : IsIso (𝟙 S) := inferInstance
    infer_instance
  have he : IsClosedImmersion (η[G'] : 𝟙_ (Over S) ⟶ G').left := IsClosedImmersion.of_comp _ G'.hom
  have htu : ∀ Y : Over S, (toUnit Y).left = Y.hom := fun Y =>
    (Category.comp_id _).symm.trans (Over.w (toUnit Y))
  have hfac : ∀ {T : Scheme.{0}} [IsReduced T] (w : T ⟶ G.left),
      Set.range (w ≫ ψ.left) ⊆ Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left →
      w ≫ ψ.left = (w ≫ G.hom) ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    intro T _ w hw
    obtain ⟨l, hl⟩ := exists_factor_of_range_subset_closedImmersion (w ≫ ψ.left) _ hw
    have hl' : l = w ≫ G.hom := by
      have := congrArg (· ≫ G'.hom) hl
      simp only [Category.assoc, hew, Over.w] at this
      exact this
    rw [← hl, hl']
  have hKeq : K = ψ.left ⁻¹' Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    ext q
    obtain ⟨k, _, _, w, hw⟩ := exists_geomPt_range_eq G.left q
    have key := hK k (w ≫ G.hom) (Over.homMk w rfl)
    have hr : Set.range (Over.homMk (U := Over.mk (w ≫ G.hom)) w rfl).left = {q} := hw
    rw [hr, Set.singleton_subset_iff] at key
    rw [← key, Set.mem_preimage]
    obtain ⟨p, rfl⟩ : q ∈ Set.range w := hw ▸ rfl
    constructor
    · intro h
      have h2 : w ≫ ψ.left = (toUnit (Over.mk (w ≫ G.hom))).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left :=
        congrArg (fun f => f.left) h
      refine ⟨(toUnit (Over.mk (w ≫ G.hom))).left p, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← h2, Scheme.Hom.comp_apply]
    · intro h
      have hw2 := hfac w (by
        rintro _ ⟨p', rfl⟩
        have h3 : w p' ∈ ({w p} : Set G.left) := hw ▸ Set.mem_range_self p'
        rw [Set.mem_singleton_iff] at h3
        rw [Scheme.Hom.comp_apply, h3]
        exact h)
      ext1
      change w ≫ ψ.left = (toUnit (Over.mk (w ≫ G.hom))).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left
      rw [htu]
      exact hw2
  have hsqS : ∀ (C : Over S) (j : C ⟶ G), IsReduced C.left → Set.range j.left = K →
      j.left ≫ ψ.left = C.hom ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    intro C j _ hjr
    have := hfac j.left (by
      rintro _ ⟨p, rfl⟩
      have hp : j.left p ∈ K := hjr ▸ Set.mem_range_self p
      rw [hKeq] at hp
      rw [Scheme.Hom.comp_apply]
      exact hp)
    rw [this, Over.w j]
  have hPfst : Set.range (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) = K := by
    rw [Scheme.Pullback.range_fst, hKeq]
  have hfin' : IsFinite (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  have het' : Etale (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  have hci : IsClosedImmersion (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  refine ⟨⟨Over.mk (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left : _ ⟶ S),
    Over.homMk (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) (by
      change _ = pullback.snd _ _
      rw [← Over.w ψ, ← Category.assoc, pullback.condition, Category.assoc, hew]
      exact Category.comp_id _),
    hfin', het', hci, hPfst⟩, ?_⟩
  intro hred C j hCet hj hjr
  have hCred : IsReduced C.left := GlobalTheory.isReduced_of_smooth_of_isReduced C.hom
  have hsq := hsqS C j hCred hjr
  have hred' : IsReduced (𝟙_ (Over S)).left := hred
  have hPred : IsReduced (pullback ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left)
  let φ : C.left ⟶ pullback ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left := pullback.lift j.left C.hom hsq
  have hφ1 : φ ≫ pullback.fst _ _ = j.left := pullback.lift_fst _ _ _
  have hφci : IsClosedImmersion φ := by
    have : IsClosedImmersion (φ ≫ pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) := by
      rw [hφ1]; exact hj
    exact IsClosedImmersion.of_comp φ (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left)
  have hφs : Surjective φ := ⟨fun r => by
    have hr : pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left r ∈ Set.range j.left := by
      rw [hjr, ← hPfst]; exact Set.mem_range_self r
    obtain ⟨c, hc⟩ := hr
    refine ⟨c, (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ1, hc]⟩
  have hφi : IsIso φ := isIso_of_isClosedImmersion_of_surjective φ
  have HS : IsPullback j.left (toUnit C).left ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    rw [htu C]
    exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso φ) hφ1 (pullback.lift_snd _ _ _)
  have hw : j ≫ ψ = toUnit C ≫ η[G'] := by
    ext1
    change j.left ≫ ψ.left = (toUnit C).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left
    rw [htu C]; exact hsq
  exact IsPullback.of_map (Over.forget S) hw HS

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.RigidBundleGlue

variable {X Y Z : Scheme.{0}}

theorem exists_gen_of_lbIso {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X) (𝟙 X) rfl)
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem LBIso.pull {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (chartPullPull P f f rfl) (chartPullPull Q f f rfl)

def chartPullComp (L : LB X) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Z ⟶ X) (e : c = g ≫ f) :
    ChartPull (L.pull c) ((L.pull f).pull g) (𝟙 Z) := by
  subst e
  exact chartPullIn L (fun _ : PUnit => f) (fun _ => 1) g

theorem eq_one_of_section {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {e : S ⟶ A.left}
    (he : e ≫ A.hom = 𝟙 S) (V : S.Opens) (u : Γ(A.left, A.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (A.hom ⁻¹ᵁ V))
    (hu : (e.appLE _ V h).hom u = 1) : u = 1 := by
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have := GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth A.hom V
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (A.hom.app V)).2 u
  have k : ∀ (q : S ⟶ S) (_ : q = 𝟙 S) (l : V ≤ q ⁻¹ᵁ V), (q.appLE V V l).hom a = a := by
    rintro _ rfl l
    have : (𝟙 S : S ⟶ S).appLE V V l = 𝟙 _ := by
      simp [Scheme.Hom.appLE]
      exact S.presheaf.map_id _
    rw [this]; rfl
  have h₁ : (e.appLE _ V h).hom ((A.hom.app V).hom a) = a :=
    (congrArg (fun q => q.hom a) (Scheme.Hom.comp_appLE e A.hom V V h)).symm.trans (k (e ≫ A.hom) he h)
  rw [h₁.symm.trans hu, map_one]

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem exists_glue : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (M : ∀ i, LB (G i).left) (B : I → I → Scheme.{0}) (a : ∀ i j, B i j ⟶ (G i).left) (b : ∀ i j, B i j ⟶ (G j).left), (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i, (M i).IsLB) → (∀ i, Out.Rigidified (G i) (M i)) → (∀ i j, LBIso ((M i).pull (a i j)) ((M j).pull (b i j))) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ ∀ i, LBIso (M i) (L.pull (ψ i)) := by
  intro S I U A _ G _ ψ hU hψ hA _ M B a b hB hM hr hiso
  have oi : ∀ i, IsOpenImmersion (ψ i) := fun i => CoverGlue.isOpenImmersion (hψ i).1
  choose N hN₁ hN₂ hN₃ hN₄ using fun i => _root_.GlobalTheory.LBPush.exists_push _ _ (ψ i) (M i) (hM i)
  have hR : ∀ i x, x ∈ (ψ i).opensRange ↔ A.hom x ∈ U i := fun i x => CoverGlue.mem_range (hψ i).1 x
  have hNU : ∀ i k, (N i).U k ≤ (ψ i).opensRange := fun i k => (le_iSup (N i).U k).trans (hN₁ i).le
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  obtain ⟨L, hL, hLr, hLi⟩ := _root_.GlobalTheory.PartialBundleGlue.exists_glue A.left S A.hom e I U N he (eq_one_of_section A hA he) hU
    (fun i => (hN₁ i).trans (TopologicalSpace.Opens.ext (Set.ext (hR i)))) hN₂
    (fun i => by
      refine (_root_.GlobalTheory.GenPush.gen_iso_of_charts_le_range S (U i).toScheme (U i).ι).1 _ (fun k s hs => ?_) ?_
      · have h₁ := (hR i _).1 (hNU i _ (mem_pull.1 hs))
        rw [← Scheme.Hom.comp_apply, he] at h₁
        exact ⟨⟨s, h₁⟩, rfl⟩
      · let e' : (U i).toScheme ⟶ (G i).left := eSec (G i)
        have hc : e' ≫ ψ i = (U i).ι ≫ e := eSec_comm (hψ i)
        obtain ⟨t, ht⟩ := exists_gen_of_lbIso (pull_isLB (hM i) e') (pull_isLB (hN₃ i) e')
          (LBIso.pull (hN₄ i) e') (hr i)
        obtain ⟨t', ht'⟩ := gen_chartPull (chartPullComp (N i) (ψ i) e' _ hc.symm) t ht
        exact gen_chartPull (chartPullOut (N i) (fun _ : PUnit => e) (fun _ => 1) (U i).ι _ fun _ => rfl) t' ht')
    (fun i j => by
      have : IsOpenImmersion (a i j) :=
        MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hB i j).flip (oi j)
      refine (_root_.GlobalTheory.GenPush.gen_iso_of_charts_le_range A.left (B i j) (a i j ≫ ψ i)).2 _ _ (fun k l x hx => ?_) ?_
      · obtain ⟨y, hy⟩ := hNU i k hx.1
        obtain ⟨y', hy'⟩ := hNU j l hx.2
        obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hB i j) y y' (hy.trans hy'.symm)
        exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
      · refine LBIso.chartPull (chartPullComp (N i) (ψ i) (a i j) _ rfl)
          (chartPullComp (N j) (ψ j) (b i j) _ (hB i j).w) ?_
        exact ((LBIso.pull (hN₄ i) (a i j)).symm.trans (pull_isLB (hN₃ i) _) (pull_isLB (hM i) _)
          (pull_isLB (hM j) _) (hiso i j)).trans (pull_isLB (hN₃ i) _) (pull_isLB (hM j) _) (pull_isLB (hN₃ j) _)
          (LBIso.pull (hN₄ j) (b i j)))
  exact ⟨L, hL, hLr, fun i => (hN₄ i).trans (hM i) (hN₃ i) (pull_isLB hL _) (LBIso.pull (hLi i) (ψ i))⟩

end GlobalTheory.RigidBundleGlue
end
end

