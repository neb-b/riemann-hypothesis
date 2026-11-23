module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarLeibnizEvenFormMul
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

theorem del_dbar_even_mul (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (w : A.Pt → Ev n) (β : A.Fld)
    (hw : A.IsForm (GlobalTheory.LineForm.fld A w)) (hβ : A.IsForm β) :
    A.del (GlobalTheory.LineForm.fld A w * β) = A.del (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.del β ∧
    A.dbar (GlobalTheory.LineForm.fld A w * β) = A.dbar (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.dbar β := by
  have hloc : ∀ i, A.loc (GlobalTheory.LineForm.fld A w * β) i =
      fun v => A.loc (GlobalTheory.LineForm.fld A w) i v * A.loc β i v := by
    intro i
    funext v
    unfold HolAtlas.loc
    split_ifs
    · rfl
    · simp
  have hd : ∀ α : A.Fld, A.IsForm α → ∀ (x : A.Pt) (S),
      DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd := fun α hα x S =>
    ((hα.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)
  have key := fun x : A.Pt => _root_.GlobalTheory.CxForm.FormMul.leibniz_of_comm n (A.loc (GlobalTheory.LineForm.fld A w) x.1.1) (A.loc β x.1.1) x.crd
    (GlobalTheory.LineForm.fld A w x) (hd _ hw x) (hd _ hβ x)
  have hc : ∀ (x : A.Pt) (b : Alt n), b * A.loc (GlobalTheory.LineForm.fld A w) x.1.1 x.crd = GlobalTheory.LineForm.fld A w x * b := by
    intro x b
    rw [A.loc_crd]
    exact Subalgebra.mem_center_iff.1 (w x).2 b
  constructor
  · funext x
    have := (key x).1 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.del, Pi.add_apply, Pi.mul_apply, hloc]
    exact this
  · funext x
    have := (key x).2 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.dbar, Pi.add_apply, Pi.mul_apply, hloc]
    exact this

end GlobalTheory.CxForm.HolAtlas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedChartTransitionsCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumDescent.cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → ∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k := by
  intro R _ _ _ _ S X π hπp hπs hS U hU J e he V τ hV hτ i j k T x y w hxy hw
  set pP := pullback.fst U.hom π with hpP

  set O : U.left.Opens := V i j ⊓ V i k with hO
  let m₁ : O.toScheme ⟶ (V i j).toScheme := U.left.homOfLE inf_le_left
  let m₂ : O.toScheme ⟶ (V i k).toScheme := U.left.homOfLE inf_le_right
  have hm₁ : m₁ ≫ (V i j).ι = O.ι := Scheme.homOfLE_ι _ _
  have hm₂ : m₂ ≫ (V i k).ι = O.ι := Scheme.homOfLE_ι _ _

  let FinalForm : (pullback U.hom π).Opens := pP ⁻¹ᵁ O
  let p' : FinalForm.toScheme ⟶ O.toScheme := pP ∣_ O
  have hp' : p' ≫ O.ι = FinalForm.ι ≫ pP := morphismRestrict_ι _ _
  have hsq : IsPullback p' (FinalForm.ι ≫ pullback.snd U.hom π) (O.ι ≫ U.hom) π :=
    (isPullback_morphismRestrict pP O).paste_vert (IsPullback.of_hasPullback U.hom π)
  have hp'surj : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hπs
  have hZ : ∀ (l : J) (z : FinalForm.toScheme), (FinalForm.ι ≫ e i) z ∈ Set.range (e l) ↔ pP (FinalForm.ι z) ∈ V i l := by
    intro l z; rw [hV]; rfl
  have hZO : ∀ z : FinalForm.toScheme, pP (FinalForm.ι z) ∈ O := by
    intro z
    have : (FinalForm.ι ≫ pP) z ∈ O := by
      rw [← hp']; exact (Scheme.Opens.range_ι O).subset ⟨p' z, rfl⟩
    exact this
  have rj : Set.range (FinalForm.ι ≫ e i) ⊆ Set.range (e j) := by
    rintro _ ⟨z, rfl⟩; exact (hZ j z).2 (hZO z).1
  have rk : Set.range (FinalForm.ι ≫ e i) ⊆ Set.range (e k) := by
    rintro _ ⟨z, rfl⟩; exact (hZ k z).2 (hZO z).2
  let b := IsOpenImmersion.lift (e j) (FinalForm.ι ≫ e i) rj
  let c := IsOpenImmersion.lift (e k) (FinalForm.ι ≫ e i) rk
  have hb : b ≫ e j = FinalForm.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
  have hc : c ≫ e k = FinalForm.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _

  have h1 : p' ≫ m₁ ≫ τ i j = b ≫ pP :=
    hτ i j _ FinalForm.ι b (p' ≫ m₁) hb.symm (by rw [Category.assoc, hm₁, hp'])
  have h2 : p' ≫ m₂ ≫ τ i k = c ≫ pP :=
    hτ i k _ FinalForm.ι c (p' ≫ m₂) hc.symm (by rw [Category.assoc, hm₂, hp'])

  have rw₀ : Set.range (m₁ ≫ τ i j) ⊆ Set.range (V j k).ι := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨z, rfl⟩ := hp'surj.surj o
    have e1 : (p' ≫ m₁ ≫ τ i j) z = (b ≫ pP) z := by rw [h1]
    have e2 : (b ≫ e j) z = (c ≫ e k) z := by rw [hb, hc]
    simp only [Scheme.Hom.comp_apply] at e1 e2
    rw [Scheme.Opens.range_ι]
    show (m₁ ≫ τ i j) (p' z) ∈ V j k
    simp only [Scheme.Hom.comp_apply]
    rw [e1, hV, e2]
    exact ⟨_, rfl⟩
  let w₀ := IsOpenImmersion.lift (V j k).ι (m₁ ≫ τ i j) rw₀
  have hw₀ : w₀ ≫ (V j k).ι = m₁ ≫ τ i j := IsOpenImmersion.lift_fac _ _ _
  have h3 : p' ≫ w₀ ≫ τ j k = c ≫ pP :=
    hτ j k _ b c (p' ≫ w₀) (hb.trans hc.symm) (by rw [Category.assoc, hw₀, h1])
  haveI := hU
  have heq : pullback.fst p' p' ≫ c ≫ pP = pullback.snd p' p' ≫ c ≫ pP := by
    rw [← h2, pullback.condition_assoc]
  obtain ⟨h₀, -, huniq⟩ := _root_.GlobalTheory.MorDescent.descend R S O.toScheme FinalForm.toScheme U.left π (O.ι ≫ U.hom) p'
    (FinalForm.ι ≫ pullback.snd U.hom π) hπp hπs hS inferInstance hsq (c ≫ pP) heq
  have E : w₀ ≫ τ j k = m₂ ≫ τ i k := (huniq _ h3).trans (huniq _ h2).symm

  have rt : Set.range (x ≫ (V i j).ι) ⊆ Set.range O.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← Scheme.Opens.range_ι (V i j)]; exact ⟨x s, rfl⟩
    · rw [hxy, ← Scheme.Opens.range_ι (V i k)]; exact ⟨y s, rfl⟩
  let t := IsOpenImmersion.lift O.ι (x ≫ (V i j).ι) rt
  have ht : t ≫ O.ι = x ≫ (V i j).ι := IsOpenImmersion.lift_fac _ _ _
  have tx : t ≫ m₁ = x := (cancel_mono (V i j).ι).1 (by rw [Category.assoc, hm₁, ht])
  have ty : t ≫ m₂ = y := (cancel_mono (V i k).ι).1 (by rw [Category.assoc, hm₂, ht, hxy])
  have tw : w = t ≫ w₀ := (cancel_mono (V j k).ι).1 (by rw [← hw, Category.assoc, hw₀, ← Category.assoc, tx])
  rw [tw, Category.assoc, E, ← Category.assoc, ty]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedCommGroupOfPullbackProperSurjection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R}

theorem ext_of_pts (hP : IsProper π) (hS : Surjective π) (hI : IsIntegral S) {Y W : Over (Sp R)} (hY : Flat Y.hom)
    (f₁ f₂ : Y ⟶ W) (h : ∀ (T : Over S) (P : Over.mk (T.hom ≫ π) ⟶ Y), P ≫ f₁ = P ≫ f₂) : f₁ = f₂ := by
  have hpb : IsPullback (pullback.fst Y.hom π) (pullback.snd Y.hom π) Y.hom π := IsPullback.of_hasPullback _ _
  have key : pullback.fst Y.hom π ≫ f₁.left = pullback.fst Y.hom π ≫ f₂.left := by
    have := h (Over.mk (pullback.snd Y.hom π)) (Over.homMk (pullback.fst Y.hom π) pullback.condition)
    simpa using congrArg CommaMorphism.left this
  obtain ⟨h₀, _, hu⟩ := _root_.GlobalTheory.MorDescent.descend R S Y.left (pullback Y.hom π) W.left π Y.hom (pullback.fst Y.hom π)
    (pullback.snd Y.hom π) hP hS hI hY hpb (pullback.fst Y.hom π ≫ f₁.left)
    (by rw [← Category.assoc, ← Category.assoc, pullback.condition])
  ext
  exact (hu _ rfl).trans (hu _ key.symm).symm

variable {G' : Over S} {G : Over (Sp R)} {β : G'.left ⟶ G.left}

def dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : Over.mk (T.hom ≫ π) ⟶ G :=
  Over.homMk (x.left ≫ β) (by
    change x.left ≫ β ≫ G.hom = T.hom ≫ π
    rw [hpb.w, ← Category.assoc, Over.w x])

def up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) : T ⟶ G' :=
  Over.homMk (hpb.lift a.left T.hom (by simpa using Over.w a)) (hpb.lift_snd _ _ _)

theorem dn_up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) :
    dn hpb (up hpb a) = a := by
  ext; simp [dn, up]

theorem up_dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : up hpb (dn hpb x) = x := by
  ext; apply hpb.hom_ext <;> simp [dn, up]

end GlobalTheory.Mum.DescGrp

end

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R} {G' : Over S} [GrpObj G'] {G : Over (Sp R)} {β : G'.left ⟶ G.left}

theorem pt_mul (hpb : IsPullback β G'.hom G.hom π) (m : G ⊗ G ⟶ G)
    (hm : ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β)
    (T : Over S) (a b : Over.mk (T.hom ≫ π) ⟶ G) : lift a b ≫ m = dn hpb (up hpb a * up hpb b) := by
  ext
  rw [hm T (up hpb a) (up hpb b) a b (by simp [up]) (by simp [up])]
  rfl

theorem pt_one (hpb : IsPullback β G'.hom G.hom π) (e : 𝟙_ (Over (Sp R)) ⟶ G)
    (he : ∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) (T : Over S) :
    toUnit (Over.mk (T.hom ≫ π)) ≫ e = dn hpb 1 := by
  ext; rw [he]; rfl

theorem pt_inv (hpb : IsPullback β G'.hom G.hom π) (i : G ⟶ G)
    (hi : ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      (x₀ ≫ i).left = x⁻¹.left ≫ β) (T : Over S) (a : Over.mk (T.hom ≫ π) ⟶ G) :
    a ≫ i = dn hpb (up hpb a)⁻¹ := by
  ext; rw [hi T (up hpb a) a (by simp [up])]; rfl

section shapes
variable {G : Over (Sp R)} {T : Over (Sp R)}

theorem sh_assocL (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (m ▷ G) ≫ m = lift (lift (P ≫ fst _ _ ≫ fst _ _) (P ≫ fst _ _ ≫ snd _ _) ≫ m) (P ≫ snd _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_assocR (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (α_ G G G).hom ≫ (G ◁ m) ≫ m =
      lift (P ≫ fst _ _ ≫ fst _ _) (lift (P ≫ fst _ _ ≫ snd _ _) (P ≫ snd _ _) ≫ m) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneL (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (λ_ G).inv ≫ (e ▷ G) ≫ m = lift (toUnit T ≫ e) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneR (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (ρ_ G).inv ≫ (G ◁ e) ≫ m = lift P (toUnit T ≫ e) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_comm (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (β_ G G).hom ≫ m = lift (P ≫ snd _ _) (P ≫ fst _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_id (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ m = lift (P ≫ fst _ _) (P ≫ snd _ _) ≫ m := by
  rw [← comp_lift, lift_fst_snd, Category.comp_id]
theorem sh_invL (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift i (𝟙 G) ≫ m = lift (P ≫ i) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_invR (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift (𝟙 G) i ≫ m = lift P (P ≫ i) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_unit (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) : P ≫ toUnit G ≫ e = toUnit T ≫ e := by
  rw [← Category.assoc, comp_toUnit]
end shapes

theorem flat_prod2 (G : Over (Sp R)) [Flat G.hom] : Flat (G ⊗ G).hom :=
  inferInstanceAs (Flat (pullback.fst G.hom G.hom ≫ G.hom))
theorem flat_prod3 (G : Over (Sp R)) [Flat G.hom] : Flat ((G ⊗ G) ⊗ G).hom := by
  have := flat_prod2 G
  exact inferInstanceAs (Flat (pullback.fst (G ⊗ G).hom G.hom ≫ (G ⊗ G).hom))

end GlobalTheory.Mum.DescGrp


open GlobalTheory.Mum.DescGrp in
theorem GlobalTheory.Mum.descGrpObj_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ (m : G ⊗ G ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (i : G ⟶ G), (∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β) → (∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) → (∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β) → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hP hS hI G' _ _ G β hsm hpb m e i hm he hi
  haveI : Smooth G.hom := hsm
  have f1 : Flat G.hom := inferInstance
  have f2 : Flat (G ⊗ G).hom := flat_prod2 G
  have f3 : Flat ((G ⊗ G) ⊗ G).hom := flat_prod3 G
  have hM := pt_mul hpb m hm
  have hE := pt_one hpb e he
  have hI' := pt_inv hpb i hi
  have a1 : e ▷ G ≫ m = (λ_ G).hom := by
    rw [← cancel_epi (λ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneL, Category.comp_id, hE, hM, up_dn, _root_.one_mul, dn_up]
  have a2 : G ◁ e ≫ m = (ρ_ G).hom := by
    rw [← cancel_epi (ρ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneR, Category.comp_id, hE, hM, up_dn, _root_.mul_one, dn_up]
  have a3 : m ▷ G ≫ m = (α_ G G G).hom ≫ G ◁ m ≫ m := by
    refine ext_of_pts hP hS hI f3 _ _ (fun T P => ?_)
    rw [sh_assocL, sh_assocR]
    simp only [hM, up_dn, _root_.mul_assoc]
  have a4 : lift i (𝟙 G) ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invL, sh_unit, hE, hI', hM, up_dn, _root_.inv_mul_cancel]
  have a5 : lift (𝟙 G) i ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invR, sh_unit, hE, hI', hM, up_dn, _root_.mul_inv_cancel]
  have a6 : (β_ G G).hom ≫ m = m := by
    refine ext_of_pts hP hS hI f2 _ _ (fun T P => ?_)
    rw [sh_comm, sh_id P m, hM, hM]
    letI : CommMonoid (T ⟶ G') := Hom.commMonoid
    rw [_root_.mul_comm]
  letI inst : GrpObj G :=
    { one := e, mul := m, inv := i, one_mul := a1, mul_one := a2, mul_assoc := a3, left_inv := a4,
      right_inv := a5 }
  exact ⟨inst, ⟨a6⟩, hpb, fun T x y x₀ y₀ hx hy => by
    rw [Hom.mul_def]; exact hm T x y x₀ y₀ hx hy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentTransitionDiagonalInclusionOverBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem descend_transition_diag_over : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, τ i i = (V i i).ι) ∧ (∀ i j, τ i j ≫ U.hom = (V i j).ι ≫ U.hom) := by
  intro R _ _ _ _ S X π f hprop hsurj hint U hU J e he hef V τ hV hτ

  have hsq : ∀ O : U.left.Opens, IsPullback (pullback.fst U.hom π ∣_ O)
      ((pullback.fst U.hom π ⁻¹ᵁ O).ι ≫ pullback.snd U.hom π) (O.ι ≫ U.hom) π := fun O =>
    (IsPullback.paste_horiz (isPullback_morphismRestrict (pullback.fst U.hom π) O).flip
      (IsPullback.of_hasPullback U.hom π).flip).flip
  have huniq : ∀ (O : U.left.Opens) (W : Scheme.{0}) (g₁ g₂ : O.toScheme ⟶ W),
      (pullback.fst U.hom π ∣_ O) ≫ g₁ = (pullback.fst U.hom π ∣_ O) ≫ g₂ → g₁ = g₂ :=
    fun O W g₁ g₂ h => GlobalTheory.MorDescent.uniq R S O.toScheme _ π (O.ι ≫ U.hom) _ _ hprop hsurj hint
      inferInstance (hsq O) W g₁ g₂ h
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · apply huniq (V i i)
    have := hτ i i _ (pullback.fst U.hom π ⁻¹ᵁ V i i).ι (pullback.fst U.hom π ⁻¹ᵁ V i i).ι
      (pullback.fst U.hom π ∣_ V i i) rfl (morphismRestrict_ι _ _)
    rw [this, morphismRestrict_ι]
  · apply huniq (V i j)
    set Z := pullback.fst U.hom π ⁻¹ᵁ V i j
    have hr : Set.range (Z.ι ≫ e i) ⊆ Set.range (e j) := by
      rintro _ ⟨z, rfl⟩
      have hz : pullback.fst U.hom π (Z.ι z) ∈ V i j := by
        have h0 : Z.ι z = z.1 := Scheme.Opens.ι_apply _ _
        rw [h0]; exact z.2
      exact (hV i j (Z.ι z)).1 hz
    set b := IsOpenImmersion.lift (e j) (Z.ι ≫ e i) hr
    have hb : b ≫ e j = Z.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
    have h1 := hτ i j _ Z.ι b (pullback.fst U.hom π ∣_ V i j) hb.symm (morphismRestrict_ι _ _)
    have hbs : b ≫ pullback.snd U.hom π = Z.ι ≫ pullback.snd U.hom π := by
      calc b ≫ pullback.snd U.hom π = b ≫ e j ≫ f := by rw [hef]
        _ = Z.ι ≫ e i ≫ f := by rw [← Category.assoc, hb, Category.assoc]
        _ = Z.ι ≫ pullback.snd U.hom π := by rw [hef]
    rw [← Category.assoc, h1, Category.assoc, pullback.condition, ← Category.assoc, hbs,
      Category.assoc, ← pullback.condition, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetInvariantDiffIsoHodgeLineBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UMin.lbIso_detOm_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)),
    (GlobalTheory.FlagMod.detOm Y).IsLB →
      LBIso (GlobalTheory.FlagMod.detOm Y) (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) := by
  intro E _ _ _ H Dw l Xo c Y hO
  exact GlobalTheory.HodgeCech.lbIso_detOm_det Y hO (_root_.GlobalTheory.ModelRelDim.relDim_and_isVB_omega E H Dw l Xo c Y).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionLiftPadicAlgClosureNormLeOneIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_fractionLift_padicAlgClosure_norm_le_one_iff : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (i : V →+* OO p), IsLocalHom i → ∀ (hi : Function.Injective ((OO p).subtype.comp i)) (x : FractionRing V), ‖IsFractionRing.lift (K := FractionRing V) hi x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  first | exact @GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range | exact GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range | (intros; apply GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8FibrationAlgebraicallyClosedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

theorem exists_symplectic_labels : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ),
  ∃ Mat : Fin 2 → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ,
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → (l : K) ≠ 0 →
  ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (pt : Fin (2 * (8 * gQ)) → (Out.baseOver (Sp K) ⟶ P'.A)),
    (∀ i, pt i ^ ((l ^ j) ^ 2) = 1) ∧
    (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (x : Sp K' ⟶ Sp K) (y : Over.mk x ⟶ P'.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∃! c : Ix (8 * gQ) ((l ^ j) ^ 2), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp K)) ≫ pt i)
        (fun i => (c i).val) = y) ∧
    (∀ i i', Out.WeilIs P'.A P'.L (((l ^ j) ^ 2 : ℕ) : ℤ) (pt i) (pt i')
      (unitS (spMap k₀.subtype) bT.ζ ^ Out.stdSymp (8 * gQ) i i')) ∧
    ∀ (a : Fin 2) i, pt i ≫ act a = Out.linComb pt (fun i' => ((Mat a i' i : ZMod ((l ^ j) ^ 2))).val) := by
  intro W hW gQ
  refine ⟨E8Fibration.Lab.labMat W hW.2 gQ, ?_⟩
  intro l hl hlo j hj K _ _ k₀ hk₀ hlK P' hg B _ _ M pr hPP hP hE act hact hacts
  obtain ⟨L1, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hNK : (((l ^ j) ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ (pow_ne_zero _ hlK)
  have hNodd : Odd ((l ^ j) ^ 2) := (hlo.pow).pow
  have hNpos : 0 < (l ^ j) ^ 2 := hNodd.pos
  have hN0 : (((l ^ j) ^ 2 : ℕ) : k₀) ≠ 0 := fun h => hNK (by simpa using congrArg k₀.subtype h)
  haveI : NeZero (((l ^ j) ^ 2 : ℕ) : k₀) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic ((l ^ j) ^ 2) k₀)
    (Polynomial.degree_cyclotomic_pos _ k₀ hNpos).ne'
  have hp : IsPrimitiveRoot ζ ((l ^ j) ^ 2) := (Polynomial.isRoot_cyclotomic_iff).1 hζ
  let bT : TBase k₀ ((l ^ j) ^ 2) := ⟨(hp.isUnit hNpos.ne').unit, hN0.isUnit, fun K' _ β => hp.map_of_injective β.injective⟩
  let z : Kˣ := Units.map k₀.subtype.toMonoidHom bT.ζ
  have hz : IsPrimitiveRoot z ((l ^ j) ^ 2) := IsPrimitiveRoot.coe_units_iff.1 (bT.prim K k₀.subtype)
  have hu : unitS (spMap k₀.subtype) bT.ζ = unitOn z := by
    ext
    simp only [unitS, unitOn, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, z]
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom k₀.subtype)
    exact (congrArg (fun f => f.hom (bT.ζ : k₀)) this).symm
  obtain ⟨b, hb, hpair⟩ := _root_.GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis.exists_basis W hW gQ _ hNodd K hNK z hz P' hg B pr hP
    (_root_.GlobalTheory.Poinc.Sep.E8Fibration.PairVal.weilIs_of_form_eq W hW gQ K P' B M pr hPP hP hE _ hNpos)
  have := P'.isAb.comm
  obtain ⟨htor, hactc⟩ := GlobalTheory.T.e8_prod_torsion_section_bound W hW gQ P'.A B pr hP ((l ^ j) ^ 2) b hb
  have hpt : ∀ i i', Out.WeilIs P'.A P'.L ((l ^ j) ^ 2 : ℕ)
      (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)))
      (E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1))) (unitOn z ^ Out.stdSymp (8 * gQ) i i') := by
    intro i i'
    have h1 := hpair (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1))
      _ _ (E8Fibration.Lab.ptOf_pr hP b _) (E8Fibration.Lab.ptOf_pr hP b _)
    have h2 := E8Fibration.Lab.isSharpBasis_sharpBasis W hW.2 gQ i i'
    simp only [E8Fibration.e8] at h1
    rw [h2] at h1
    exact_mod_cast h1
  refine ⟨bT, fun i => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)), htor, ?_, ?_, ?_⟩
  · intro K' _ _ x y hy
    have key := GlobalTheory.symplectic_system_torsion_basis L1 K P' ((l ^ j) ^ 2) z
    revert key
    generalize P'.g = g' at hg ⊢
    subst hg
    intro key
    exact key _ hNK hz htor hpt K' x y hy
  · intro i i'
    rw [hu]
    exact hpt i i'
  · intro a i
    exact hactc act hacts a i

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end

