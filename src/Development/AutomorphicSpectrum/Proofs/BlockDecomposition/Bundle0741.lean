module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0132

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

variable {R : Type} [CommRing R] {X : Scheme.{0}}

abbrev ext (s : X ⟶ Sp R) (J : Ideal R) (U : X.Opens) : Ideal Γ(X, U) :=
  J.map (GlobalTheory.SmallExtLift.cst s U)

def tr (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) :
    Γ(X, V a ⊓ V b) :=
  rs X (inf_le_inf (hj a) (hj b)) (M.g (j a) (j b)).val

def trInv (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) :
    Γ(X, V a ⊓ V b) :=
  rs X (inf_le_inf (hj a) (hj b)) (M.g (j a) (j b))⁻¹.val

theorem tr_mul_trInv (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) : tr M V j hj a b * trInv M V j hj a b = 1 := by
  simp only [tr, trInv, ← map_mul, Units.mul_inv, map_one]

section Triple

variable {A : Type} (V : A → X.Opens) (a b d : A)

theorem le₁₂ : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b := inf_le_left

theorem le₂₃ : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d := le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem le₁₃ : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d := le_inf (inf_le_left.trans inf_le_left) inf_le_right

end Triple

theorem tr_cocycle {M : LB X} (hM : M.IsLB) {A : Type} (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (a b d : A) :
    rs X (le₁₂ V a b d) (tr M V j hj a b) * rs X (le₂₃ V a b d) (tr M V j hj b d) =
      rs X (le₁₃ V a b d) (tr M V j hj a d) := by
  have h := congrArg (fun u => rs X (le_inf (le_inf
    ((inf_le_left.trans inf_le_left).trans (hj a)) ((inf_le_left.trans inf_le_right).trans (hj b)))
    (inf_le_right.trans (hj d)) : V a ⊓ V b ⊓ V d ≤ M.U (j a) ⊓ M.U (j b) ⊓ M.U (j d)) u.val)
    (hM.cocycle (j a) (j b) (j d))
  have e : ∀ {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ), ((res h u : Γ(X, W)ˣ) : Γ(X, W)) = rs X h u :=
    fun _ _ => rfl
  simp only [Units.val_mul, map_mul, e, GlobalTheory.AbLaw.rs_rs] at h
  simp only [tr, GlobalTheory.AbLaw.rs_rs]
  exact h

def DepSt : Prop :=
  ∀ (k : Type) [Field k] (Y : Scheme.{0}) (s₀ : Y ⟶ Sp k), Y.IsSeparated → ∀ n r : ℕ,
    Module.Finite k (HO1 s₀) → Module.finrank k (HO1 s₀) ≤ n → n < r →
    ∀ (A : Type) (V : A → Y.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ α : Fin r → ∀ a b, Γ(Y, V a ⊓ V b),
      (∀ i a b d, rs Y (le₁₂ V a b d) (α i a b) + rs Y (le₂₃ V a b d) (α i b d) =
        rs Y (le₁₃ V a b d) (α i a d)) →
      ∃ (c : Fin r → k) (ψ : ∀ a, Γ(Y, V a)), c ≠ 0 ∧ ∀ a b,
        ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * α i a b =
          rs Y inf_le_left (ψ a) - rs Y inf_le_right (ψ b)

end GlobalTheory.CompanionTheory.FewEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusRepresentsTriviality
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivPull

theorem isPullback_fst_snd {S : Scheme.{0}} (A T : Over S) :
    IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback A.hom T.hom

theorem isPullback_whisker {S : Scheme.{0}} (A T : Over S) {B : Scheme.{0}} (b : B ⟶ T.left) :
    IsPullback (A ◁ (Over.homMk b rfl : Over.mk (b ≫ T.hom) ⟶ T)).left
      (snd A (Over.mk (b ≫ T.hom))).left (snd A T).left b := by
  have h1 := isPullback_fst_snd A T
  have h2 := isPullback_fst_snd A (Over.mk (b ≫ T.hom))
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_fst]
    exact h2
  · rw [← Over.comp_left, CartesianMonoidalCategory.whiskerLeft_snd, Over.comp_left]
    rfl

theorem pull_iso_eq_zero_iff {X Y : Scheme.{0}} (θ : Y ≅ X) (c : Pic X) :
    CechPic.pull θ.hom c = 0 ↔ c = 0 := by
  constructor
  · intro h
    have h' := congrArg (CechPic.pull θ.inv) h
    rwa [← pull_comp, θ.inv_hom_id, pull_id, map_zero] at h'
  · intro h
    rw [h, map_zero]

theorem triv_pull_iff {S : Scheme.{0}} (A Y Z : Over S) (N : LB (A ⊗ Y).left) (hN : N.IsLB) (i : Z ⟶ Y)
    (h : PositivityTheory.ObstructionTrivialLocus.IsTrivLocus A N i) (T : Over S) (y : T ⟶ Y) {B : Scheme.{0}} (b : B ⟶ T.left) :
    Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b)) ↔
      ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
  obtain ⟨-, h2⟩ := h
  obtain ⟨g, hg⟩ : ∃ g : Over.mk (b ≫ T.hom) ⟶ T, g = Over.homMk b rfl := ⟨_, rfl⟩
  have hW := isPullback_whisker A T b
  rw [← hg] at hW
  have hθ : hW.isoPullback.hom ≫ pullback.fst (snd A T).left b = (A ◁ g).left :=
    hW.isoPullback_hom_fst
  have hlift : lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y) =
      (A ◁ g) ≫ lift (fst A T) (snd A T ≫ y) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hF := pull_isLB hN (lift (fst A T) (snd A T ≫ y)).left
  have hP := pull_isLB hF (pullback.fst (snd A T).left b)
  have hE := pull_isLB hN (lift (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y)).left
  have e3 : cls _ hE = CechPic.pull hW.isoPullback.hom (cls _ hP) := by
    rw [cls_pull hN _ hE, cls_pull hF _ hP, cls_pull hN _ hF, ← pull_comp, ← pull_comp,
      hlift, Over.comp_left, hθ]
  have hg' : g.left = b := by
    rw [hg]
    rfl
  calc Triv ((ev N (fst A T) (snd A T ≫ y)).pull (pullback.fst (snd A T).left b))
      ↔ cls _ hP = 0 := (cls_eq_zero_iff hP).symm
    _ ↔ CechPic.pull hW.isoPullback.hom (cls _ hP) = 0 := (pull_iso_eq_zero_iff _ _).symm
    _ ↔ cls _ hE = 0 := by rw [e3]
    _ ↔ Triv (ev N (fst A (Over.mk (b ≫ T.hom))) (snd A (Over.mk (b ≫ T.hom)) ≫ g ≫ y)) :=
      cls_eq_zero_iff hE
    _ ↔ ∃ z, z ≫ i = g ≫ y := h2 _ _
    _ ↔ ∃ z : B ⟶ Z.left, z ≫ i.left = b ≫ y.left := by
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨z.left, ?_⟩
        have hz' : (z ≫ i).left = (g ≫ y).left := by rw [hz]
        rw [Over.comp_left, Over.comp_left, hg'] at hz'
        exact hz'
      · rintro ⟨z, hz⟩
        have hzw : z ≫ Z.hom = (Over.mk (b ≫ T.hom)).hom := by
          show z ≫ Z.hom = b ≫ T.hom
          rw [← Over.w i, ← Category.assoc, hz, Category.assoc, Over.w y]
        refine ⟨Over.homMk z hzw, ?_⟩
        apply Over.OverMorphism.ext
        rw [Over.comp_left, Over.comp_left, hg']
        exact hz

end GlobalTheory.CompanionTheory.TrivPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeFieldOfField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory.CompanionTheory.Hodge.WedgeField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo

theorem wedgeField_of_field :
    DescentSt → LowSt → SteinSt → H1StructureFieldDim → VanSt → HopfSt → HopfFieldSt → WedgeFieldSt := by
  intro hD hL hS hH1 hV hHopf hHF R _ A _ g hA hg hR
  haveI : IsAbelianScheme A := hA
  haveI : IsProper A.hom := IsAbelianScheme.proper
  haveI : CompactSpace (Sp R) := by
    unfold Sp
    infer_instance
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨P, iP, hfin, ⟨S⟩⟩ := exists_finite_sys A.hom
  letI := iP
  haveI := hfin
  have hQ : AllQIso (resSys A.hom S) := hD R A.left A.hom inferInstance P S
  obtain ⟨h1, h2, hSt⟩ := hL R _ _ _ _ (resSys A.hom S) hQ
  have hStein : Stein (OSys A.hom S) := hSt.mp (hS R A g hA hg)
  have hvb : VB R (H1 (OSys A.hom S)) g := vb_of_bijective (resSys A.hom S) h1 (hH1 R A g hA hg hR)
  have hvan : ∀ n : ℕ, g ≤ n → Function.Exact (dn (OSys A.hom S) n) (dn (OSys A.hom S) (n + 1)) :=
    fun n hn => hV R A g hA hg hR P S n hn
  have hh : Hopf (OSys A.hom S) (IsField R) := hHopf R A g hA hg P S
  rw [eq_true hR] at hh
  exact wedge_of_bijective (resSys A.hom S) h1 h2 (hHF R P (OSys A.hom S) g hR hStein hvb hvan hh)

end GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo
end
end

