module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem levelMaps_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) := by
  intro hL

  have hsm (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k) (hs : Smooth s) :
      IsReduced X ∧ GlobalTheory.IsNormalScheme X ∧ IsLocallyNoetherian X := by
    obtain ⟨hred, hnormal, hnoeth⟩ :=
      GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k X s hs
    exact ⟨hred, GlobalTheory.IsNormalScheme.of_pred hnormal, hnoeth⟩
  have hid := ObjMaps.id_comp_cancel
  have hlow := obj_lower_level
  have hrep := moduli_rep_of_base hid
  have hsim := SimAlg.sim_group
  have hact := Moduli.LevelAction.similitude_acts hsm hid hlow hrep
    (exists_obj_twist_by_similitude hsim) hsim
  exact levelMaps_of_parts
    (GlobalTheory.exists_levelMap
      GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
      hid hlow hrep) hact
    (LevCover.levelMap_finite_etale_surjective_of_laws hL)
    (levelMap_fibre_orbit hL obj_pull hid obj_isAbelianScheme_dim_rigidified_sym hlow
      (obj_rigid_closed hL) hrep tateIso_differ_by_similitude hsim hact)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevUniq

theorem exists_sab_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem map_to_univ_unique : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l₀ l : Level H) (Xo : Moduli D l₀) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (r r' : S ⟶ Xo.X) (ν : SABMap o.t Xo.univ.t r) (ν' : SABMap o.t Xo.univ.t r'), IsReduced S → r ≫ Xo.s = r' ≫ Xo.s → LevComp o Xo.univ r ν → LevComp o Xo.univ r' ν' → r = r' ∧ ν.φ = ν'.φ := by
  intro hL _ _ E _ _ _ H D l₀ l Xo B _ b S s o r r' ν ν' hS hs hν hν'
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l₀ (KA l₀) (KA l₀) (baseKA l₀) (baseKA l₀) (RingHom.id _) Xo.X S Xo.s
    (r ≫ Xo.s) r rfl rfl (by
      rw [show spMap (RingHom.id (KA l₀)) = 𝟙 (Sp (KA l₀)) from Spec.map_id _, Category.comp_id]) Xo.univ
  obtain ⟨n₁, hn₁⟩ := exists_sab_cast m₁.toSABMap (Category.id_comp r).symm
  obtain ⟨k, hk⟩ := ObjMaps.exists_sab_cancel ν n₁
  have hk' : m₁.toSABMap.φ = k.φ ≫ ν.φ := hn₁.symm.trans hk
  have pk : IsPullback k.φ o₁.t.G.hom o.t.G.hom (𝟙 S) := k.cart.1
  have pν : IsPullback ν.φ o.t.G.hom Xo.univ.t.G.hom r := ν.cart.1
  have key : ∀ (x : 𝟙_ (Over S) ⟶ o₁.t.G) (y : 𝟙_ (Over S) ⟶ o.t.G),
      x.left ≫ m₁.toSABMap.φ = y.left ≫ ν.φ → x.left ≫ k.φ = y.left := by
    intro x y h
    refine pν.hom_ext ?_ ?_
    · rw [Category.assoc, ← hk', h]
    · rw [Category.assoc, pk.w, Category.comp_id, Over.w x, Over.w y]
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp ν' k
  obtain ⟨n₃, hn₃⟩ := exists_sab_cast n₂ (Category.id_comp r')
  have h₃ : n₃.φ = k.φ ≫ ν'.φ := hn₃.trans hn₂
  have e₁ : ∀ a, (o₁.eta a).left ≫ n₃.φ = r' ≫ (Xo.univ.eta a).left := by
    intro a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.eta a).trans (hν.1 a).symm), hν'.1 a]
  have e₂ : ∀ a, (o₁.etaA a).left ≫ n₃.φ = r' ≫ (Xo.univ.etaA a).left := by
    intro a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.etaA a).trans (hν.2 a).symm), hν'.2 a]
  have hr : r = r' := (Xo.rep S (r ≫ Xo.s) hS o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨hs.symm, ⟨⟨n₃, e₁, e₂⟩⟩⟩
  subst hr
  refine ⟨rfl, ?_⟩
  have hφ : m₁.toSABMap.φ = n₃.φ :=
    obj_rigid_closed hL E H D l₀ (KA l₀) (KA l₀) (baseKA l₀) (baseKA l₀) Xo.X S Xo.s (r ≫ Xo.s) Xo.univ o₁ r
      (Or.inl hS) m₁.toSABMap n₃ (fun a => ⟨_, m₁.eta a, e₁ a⟩)
  have : IsIso k.φ := pk.isIso_fst_of_isIso
  rw [← cancel_epi k.φ, ← hk', ← h₃, hφ]

end GlobalTheory.LevUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemOfMemImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.GlueTwoLB

variable {X Y Z : Scheme.{0}}

def stU (f : Z ⟶ Y) (z : Z) : (Y.presheaf.stalk (f z))ˣ →* (Z.presheaf.stalk z)ˣ :=
  Units.map (f.stalkMap z).hom.toMonoidHom

theorem stU_gm (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    stU f z (gm g (f z) U a) = gm (f ≫ g) z U a := by
  rw [← gm_pull f g z U h]
  apply Units.ext
  rw [gm_val f z (g ⁻¹ᵁ U) h]
  show (f.stalkMap z).hom (gm g (f z) U a).val = _
  rw [gm_val g (f z) U h]
  exact Scheme.Hom.germ_stalkMap_apply f _ z h _

theorem stU_injective (f : Z ⟶ Y) [IsOpenImmersion f] (z : Z) : Function.Injective (stU f z) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (f.stalkMap z)).1

theorem stU_gm_id (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    stU f z (gm (𝟙 Y) (f z) U a) = gm f z U a := by
  rw [stU_gm f (𝟙 Y) z U h, Category.comp_id]

theorem exists_push (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W : Z.Opens) (V : Y.Opens)
    (h : ∀ y ∈ V, ∃ z ∈ W, ψ z = y) (a : Γ(Z, W)ˣ) :
    ∃ b : Γ(Y, V)ˣ, ∀ z : Z, ψ z ∈ V → gm ψ z V b = gm (𝟙 Z) z W a := by
  have hle : V ≤ ψ ''ᵁ W := fun y hy => h y hy
  refine ⟨res hle (Units.map (ψ.appIso W).inv.hom.toMonoidHom a), fun z hz => ?_⟩
  have hW : z ∈ W := by
    obtain ⟨z', hz', e⟩ := h _ hz
    rwa [← ψ.isOpenEmbedding.injective e]
  rw [gm_res ψ z hle hz]
  apply Units.ext
  rw [gm_val ψ z _ (hle hz), gm_val (𝟙 Z) z W hW]
  have e := congrArg (fun q => q.hom a.val) (ψ.appIso_inv_app W)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact (congrArg (Z.presheaf.germ (ψ ⁻¹ᵁ ψ ''ᵁ W) z (hle hz)).hom e).trans
    (TopCat.Presheaf.germ_res_apply Z.presheaf _ z (hle hz) _)

theorem iso_self {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem isLB_of_stalk {L : LB X} (hc : ∀ x, ∃ i, x ∈ L.U i)
    (h : ∀ x i j k, x ∈ L.U i → x ∈ L.U j → x ∈ L.U k →
      gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (L.g j k) = gm (𝟙 X) x _ (L.g i k)) : L.IsLB := {
  cover := top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 (hc y)
  g_self i := unit_ext fun y hy => by
    rw [gm_res (𝟙 X) y _ hy, map_one]
    exact mul_eq_left.1 (h y i i i hy hy hy)
  cocycle i j k := unit_ext fun y hy => by
    rw [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy]
    exact h y i j k hy.1.1 hy.1.2 hy.2 }

theorem cocycle_descend {L : LB Y} (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (z : Z) {i j k : L.ι}
    (hi : ψ z ∈ L.U i) (hj : ψ z ∈ L.U j) (hk : ψ z ∈ L.U k)
    (h : gm ψ z _ (L.g i j) * gm ψ z _ (L.g j k) = gm ψ z _ (L.g i k)) :
    gm (𝟙 Y) (ψ z) _ (L.g i j) * gm (𝟙 Y) (ψ z) _ (L.g j k) = gm (𝟙 Y) (ψ z) _ (L.g i k) := by
  apply stU_injective ψ z
  rw [map_mul, stU_gm_id ψ z (L.U i ⊓ L.U j) ⟨hi, hj⟩, stU_gm_id ψ z (L.U j ⊓ L.U k) ⟨hj, hk⟩,
    stU_gm_id ψ z (L.U i ⊓ L.U k) ⟨hi, hk⟩, h]

theorem mem_of_mem_image (ψ : Z ⟶ Y) [IsOpenImmersion ψ] {W : Z.Opens} {z : Z} (h : ψ z ∈ ψ ''ᵁ W) : z ∈ W := by
  obtain ⟨z', hz', e⟩ := h
  rwa [← ψ.isOpenEmbedding.injective e]

theorem exists_push_inf (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (W W' : Z.Opens) (a : Γ(Z, W ⊓ W')ˣ) :
    ∃ b : Γ(Y, ψ ''ᵁ W ⊓ ψ ''ᵁ W')ˣ, ∀ z : Z, z ∈ W → z ∈ W' →
      gm ψ z (ψ ''ᵁ W ⊓ ψ ''ᵁ W') b = gm (𝟙 Z) z (W ⊓ W') a := by
  obtain ⟨b, hb⟩ := exists_push ψ (W ⊓ W') (ψ ''ᵁ W ⊓ ψ ''ᵁ W') (by
    rintro y ⟨⟨z, hz, rfl⟩, h'⟩
    exact ⟨z, ⟨hz, mem_of_mem_image ψ h'⟩, rfl⟩) a
  exact ⟨b, fun z h h' => hb z ⟨⟨z, h, rfl⟩, ⟨z, h', rfl⟩⟩⟩

theorem gen_stalk {Y₀ Y₁ Y₂ : Scheme.{0}} {φ₁ : Y₀ ⟶ Y₁} {φ₂ : Y₀ ⟶ Y₂} {L₁ : LB Y₁} {L₂ : LB Y₂}
    {w : LB.Iso (L₁.pull φ₁) (L₂.pull φ₂)} (hw : w.IsGen) (y : Y₀) {i i' : L₁.ι} {k k' : L₂.ι}
    (hi : φ₁ y ∈ L₁.U i) (hi' : φ₁ y ∈ L₁.U i') (hk : φ₂ y ∈ L₂.U k) (hk' : φ₂ y ∈ L₂.U k') :
    gw w (𝟙 Y₀) y k (fun _ => i) = gm φ₂ y _ (L₂.g k k') * (gm φ₁ y _ (L₁.g i i'))⁻¹ *
      gw w (𝟙 Y₀) y k' (fun _ => i') := by
  have := (isGen_iff w).1 hw Y₀ (𝟙 Y₀) y k k' (fun _ => i) (fun _ => i') hk hk' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ φ₁ (𝟙 Y₀) y _ _ (mem_pull.2 hi) (mem_pull.2 hi'), Category.id_comp, Category.id_comp] at this
  exact this

def pullChart (L : LB X) (F : Y ⟶ X) : ChartPull (L.pull F) L F where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hj hj' := (gm_pull_g L F (𝟙 _) y J J' hj hj').trans (by rw [Category.id_comp])

theorem glue : ∀ (Y Y₀ Y₁ Y₂ : Scheme.{0}) (ψ₁ : Y₁ ⟶ Y) (ψ₂ : Y₂ ⟶ Y) (φ₁ : Y₀ ⟶ Y₁) (φ₂ : Y₀ ⟶ Y₂) (L₁ : LB Y₁) (L₂ : LB Y₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → Set.range ψ₁ ∪ Set.range ψ₂ = Set.univ → L₁.IsLB → L₂.IsLB → LBIso (L₁.pull φ₁) (L₂.pull φ₂) → ∃ L : LB Y, L.IsLB ∧ LBIso L₁ (L.pull ψ₁) ∧ LBIso L₂ (L.pull ψ₂) := by
  intro Y Y₀ Y₁ Y₂ ψ₁ ψ₂ φ₁ φ₂ L₁ L₂ o₁ o₂ hp hcov h₁ h₂ ⟨w, hw⟩
  have p₁ : IsOpenImmersion φ₁ := MorphismProperty.of_isPullback hp.flip o₂
  have hpt : ∀ y, ψ₁ (φ₁ y) = ψ₂ (φ₂ y) := fun y => congrArg (fun g => g y) hp.w
  have lift : ∀ y₁ y₂, ψ₁ y₁ = ψ₂ y₂ → ∃ y, φ₁ y = y₁ ∧ φ₂ y = y₂ := fun y₁ y₂ e =>
    Scheme.exists_preimage_of_isPullback hp y₁ y₂ e
  have hsq := hp.w
  choose g₁ hg₁ using fun i j => exists_push_inf ψ₁ _ _ (L₁.g i j)
  choose g₂ hg₂ using fun i j => exists_push_inf ψ₂ _ _ (L₂.g i j)
  have hm : ∀ (k : L₂.ι) (i : L₁.ι), ∃ b : Γ(Y, ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i)ˣ, ∀ y : Y₀,
      φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ b = gw w (𝟙 Y₀) y k (fun _ => i) := by
    intro k i
    obtain ⟨b, hb⟩ := exists_push (φ₁ ≫ ψ₁) ((L₂.pull φ₂).U (fun _ => k) ⊓ (L₁.pull φ₁).U (fun _ => i))
      (ψ₂ ''ᵁ L₂.U k ⊓ ψ₁ ''ᵁ L₁.U i) (by
        rintro y ⟨⟨y₂, h₂, rfl⟩, ⟨y₁, h₁, e⟩⟩
        obtain ⟨z, rfl, rfl⟩ := lift y₁ y₂ e
        exact ⟨z, ⟨mem_pull.2 h₂, mem_pull.2 h₁⟩, e⟩) (w.s (fun _ => k, fun _ => i))
    exact ⟨b, fun y hk hi => hb y ⟨⟨_, hk, (hpt y).symm⟩, ⟨_, hi, rfl⟩⟩⟩
  choose m hm using hm
  let L : LB Y :=
    { «ι» := L₁.ι ⊕ L₂.ι
      U := Sum.elim (fun i => ψ₁ ''ᵁ L₁.U i) (fun k => ψ₂ ''ᵁ L₂.U k)
      g := fun p q => match p, q with
        | .inl i, .inl j => g₁ i j
        | .inr k, .inr l => g₂ k l
        | .inr k, .inl i => m k i
        | .inl i, .inr k => (res (le_inf inf_le_right inf_le_left) (m k i))⁻¹ }

  have key : ∀ y : Y₀, ∃ t : L.ι → (Y₀.presheaf.stalk y)ˣ, ∀ p q, ψ₁ (φ₁ y) ∈ L.U p → ψ₁ (φ₁ y) ∈ L.U q →
      gm (φ₁ ≫ ψ₁) y _ (L.g p q) = t p * (t q)⁻¹ := by
    intro y
    obtain ⟨i₀, hi₀⟩ := exists_chart h₁ (φ₁ y)
    have ml : ∀ i, ψ₁ (φ₁ y) ∈ L.U (.inl i) → φ₁ y ∈ L₁.U i := fun i h => mem_of_mem_image ψ₁ h
    have mr : ∀ k, ψ₁ (φ₁ y) ∈ L.U (.inr k) → φ₂ y ∈ L₂.U k := fun k h => mem_of_mem_image ψ₂ (hpt y ▸ h)
    have mix : ∀ k i, φ₂ y ∈ L₂.U k → φ₁ y ∈ L₁.U i → gm (φ₁ ≫ ψ₁) y _ (m k i) =
        gw w (𝟙 Y₀) y k (fun _ => i₀) * (gm φ₁ y _ (L₁.g i i₀))⁻¹ := fun k i hk hi => by
      rw [hm k i y hk hi, gen_stalk hw y hi hi₀ hk hk, gm_self h₂ φ₂ y hk, _root_.one_mul, mul_comm]
    refine ⟨Sum.elim (fun i => gm φ₁ y _ (L₁.g i i₀)) (fun k => gw w (𝟙 Y₀) y k (fun _ => i₀)), ?_⟩
    rintro (i | k) (j | l) hp hq
    · have e := congrArg (stU φ₁ y) (hg₁ i j _ (ml i hp) (ml j hq))
      rw [stU_gm φ₁ ψ₁ y (ψ₁ ''ᵁ L₁.U i ⊓ ψ₁ ''ᵁ L₁.U j) ⟨hp, hq⟩, stU_gm_id φ₁ y (L₁.U i ⊓ L₁.U j) ⟨ml i hp, ml j hq⟩] at e
      refine e.trans ?_
      exact eq_mul_inv_of_mul_eq (gm_cocycle h₁ φ₁ y (ml i hp) (ml j hq) hi₀)
    · refine ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (φ₁ ≫ ψ₁) y _
        (show (φ₁ ≫ ψ₁) y ∈ ψ₁ ''ᵁ L₁.U i ⊓ ψ₂ ''ᵁ L₂.U l from ⟨hp, hq⟩) _).trans
        (mix l i (mr l hq) (ml i hp))))).trans ?_
      rw [mul_inv_rev, inv_inv]; rfl
    · exact mix k j (mr k hp) (ml j hq)
    · have e := congrArg (stU φ₂ y) (hg₂ k l _ (mr k hp) (mr l hq))
      rw [stU_gm φ₂ ψ₂ y (ψ₂ ''ᵁ L₂.U k ⊓ ψ₂ ''ᵁ L₂.U l) ⟨⟨_, mr k hp, rfl⟩, ⟨_, mr l hq, rfl⟩⟩,
        stU_gm_id φ₂ y (L₂.U k ⊓ L₂.U l) ⟨mr k hp, mr l hq⟩, ← hsq] at e
      refine e.trans (eq_mul_inv_of_mul_eq ?_)
      have := gen_stalk hw y hi₀ hi₀ (mr k hp) (mr l hq)
      rw [gm_self h₁ φ₁ y hi₀, inv_one, _root_.mul_one] at this
      exact this.symm
  have hL : L.IsLB := by
    refine isLB_of_stalk (fun x => ?_) ?_
    · rcases (hcov.symm ▸ Set.mem_univ x : x ∈ Set.range ψ₁ ∪ Set.range ψ₂) with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₁ y
        exact ⟨.inl i, y, hi, rfl⟩
      · obtain ⟨i, hi⟩ := exists_chart h₂ y
        exact ⟨.inr i, y, hi, rfl⟩
    have ov : ∀ x p q r (i : L₁.ι) (k : L₂.ι), x ∈ L.U (.inl i) → x ∈ L.U (.inr k) →
        x ∈ L.U p → x ∈ L.U q → x ∈ L.U r →
        gm (𝟙 Y) x _ (L.g p q) * gm (𝟙 Y) x _ (L.g q r) = gm (𝟙 Y) x _ (L.g p r) := by
      rintro x p q r i k ⟨y₁, -, rfl⟩ ⟨y₂, -, e⟩ hp hq hr
      obtain ⟨y, rfl, rfl⟩ := lift y₁ y₂ e.symm
      obtain ⟨t, ht⟩ := key y
      refine cocycle_descend (φ₁ ≫ ψ₁) y hp hq hr ?_
      rw [ht p q hp hq, ht q r hq hr, ht p r hp hr, _root_.mul_assoc, inv_mul_cancel_left]
    rintro x (i | i) (j | j) (k | k) hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₁ hj
      have hk' := mem_of_mem_image ψ₁ hk
      refine cocycle_descend ψ₁ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₁ i j y hy hj') (hg₁ j k y hj' hk')).trans
        ((gm_cocycle h₁ (𝟙 _) y hy hj' hk').trans (hg₁ i k y hy hk').symm)
    · exact ov x _ _ _ i k hi hk hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ i j hi hj hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ j i hj hi hi hj hk
    · exact ov x _ _ _ k i hk hi hi hj hk
    · obtain ⟨y, hy, rfl⟩ := id hi
      have hj' := mem_of_mem_image ψ₂ hj
      have hk' := mem_of_mem_image ψ₂ hk
      refine cocycle_descend ψ₂ y hi hj hk ?_
      exact (congrArg₂ (· * ·) (hg₂ i j y hy hj') (hg₂ j k y hj' hk')).trans
        ((gm_cocycle h₂ (𝟙 _) y hy hj' hk').trans (hg₂ i k y hy hk').symm)
  let c₁ : ChartPull L₁ L ψ₁ := ⟨Sum.inl, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₁ i j y hi hj).symm⟩
  let c₂ : ChartPull L₂ L ψ₂ := ⟨Sum.inr, fun i y hy => ⟨y, hy, rfl⟩, fun y i j hi hj => (hg₂ i j y hi hj).symm⟩
  exact ⟨L, hL, LBIso.chartPull c₁ (pullChart L ψ₁) (iso_self hL),
    LBIso.chartPull c₂ (pullChart L ψ₂) (iso_self hL)⟩

end GlobalTheory.GlueTwoLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MonoOfUnramifiedOfPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.ModuliEmbed

theorem mono_of_unramified_of_points {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (h : ∀ (k : Type) [Field k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y') : Mono f := by
  have hs : Surjective (pullback.diagonal f) := by
    exact ((tfae_universallyInjective f).out 2 4).1 fun (k : Type) [Field k] y y' e => h k y y' e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem objMap_of_comp_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S T Z : Scheme.{0}} {s : S ⟶ Sp B} {s' : T ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {t : SAB H Z}
    {f : S ⟶ Z} (ν : SABMap o.t t f) {u uA : D.La → (𝟙_ (Over Z) ⟶ t.G)}
    (h₁ : ∀ x, (o.eta x).left ≫ ν.φ = f ≫ (u x).left) (h₂ : ∀ x, (o.etaA x).left ≫ ν.φ = f ≫ (uA x).left)
    {y y' : T ⟶ S} (e : y ≫ f = y' ≫ f) (m : ObjMap o' o y) : Nonempty (ObjMap o' o y') := by
  have hn : ∃ n : SABMap o'.t t (y' ≫ f), n.φ = m.toSABMap.φ ≫ ν.φ := by
    rw [← e]; exact ObjMaps.exists_sab_comp ν m.toSABMap
  obtain ⟨n, hn⟩ := hn
  obtain ⟨m', hm'⟩ := ObjMaps.exists_sab_cancel ν n
  have k : m'.cm.F ≫ ν.cm.F = m.cm.F ≫ ν.cm.F := hm'.symm.trans hn
  exact ⟨⟨m', fun a => ObjComp.sec_cancel ν.cart.1 m'.cart.1.w (Over.w (o.eta a)) (Over.w (o'.eta a)) (h₁ a)
      (by rw [k, ← e]; exact ObjComp.sec_comp (h₁ a) (m.eta a)),
    fun a => ObjComp.sec_cancel ν.cart.1 m'.cart.1.w (Over.w (o.etaA a)) (Over.w (o'.etaA a)) (h₂ a)
      (by rw [k, ← e]; exact ObjComp.sec_comp (h₂ a) (m.etaA a))⟩⟩

end GlobalTheory.ModuliEmbed

namespace GlobalTheory

theorem moduli_isClosedImmersion : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (o : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) (_ : ObjMap o Xo.univ (pullback.fst _ _)) (Z : Scheme.{0}) (sZ : Z ⟶ Sp c.F) (t : SAB H Z) (f : Xo.XF c ⟶ Z) (ν : SABMap o.t t f) (η' ηA : D.La → (𝟙_ (Over Z) ⟶ t.G)), f ≫ sZ = pullback.snd _ _ → (∀ x, (o.eta x).left ≫ ν.φ = f ≫ (η' x).left) → (∀ x, (o.etaA x).left ≫ ν.φ = f ≫ (ηA x).left) → IsFinite f → IsClosedImmersion f := by
  intro _ _ _ E _ _ _ H D l Xo c o m0 Z sZ t f ν u uA hf h₁ h₂ hfin
  have key : ∀ (T : Scheme.{0}) (y y' : T ⟶ Xo.XF c), y ≫ f = y' ≫ f →
      y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _ ∧
      ∃ o' : Obj D l (baseKA l) ((y ≫ pullback.fst _ _) ≫ Xo.s),
        Nonempty (ObjMap o' Xo.univ (y ≫ pullback.fst _ _)) ∧
        Nonempty (ObjMap o' Xo.univ (y' ≫ pullback.fst _ _)) := by
    intro T y y' e
    refine ⟨by rw [← hf, ← Category.assoc, e, Category.assoc], ?_⟩
    obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ T _
      ((y ≫ pullback.fst _ _) ≫ Xo.s) y rfl rfl
      ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).symm.trans
        (congrArg (((y ≫ pullback.fst _ _) ≫ Xo.s) ≫ ·) (Spec.map_id _).symm))) o
    obtain ⟨m'⟩ := ModuliEmbed.objMap_of_comp_eq ν h₁ h₂ e m
    exact ⟨o', ⟨(ObjComp.objMap_comp m0 m).choose⟩, ⟨(ObjComp.objMap_comp m0 m').choose⟩⟩
  have hu : FormallyUnramified f := by
    refine TangentCrit.formallyUnramified_of_tangent f fun k _ _ w hw => ?_
    obtain ⟨e, o', m, m'⟩ := key _ w (constPt w) (hw.trans (by simp only [constPt, Category.assoc]))
    refine pullback.hom_ext ?_ e
    have e' : constPt w ≫ pullback.fst _ _ = constPt (w ≫ pullback.fst _ _) := by
      simp only [constPt, Category.assoc]
    rw [e'] at m'
    exact (Xo.unram k _ o' m m').trans e'.symm
  have hm : Mono f := by
    refine ModuliEmbed.mono_of_unramified_of_points f fun k _ y y' e => ?_
    obtain ⟨e₂, o', m, m'⟩ := key _ y y' e
    refine pullback.hom_ext ?_ e₂
    refine (Xo.rep _ _ inferInstance o').unique ⟨rfl, m⟩ ⟨?_, m'⟩
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← e₂, Category.assoc]
  exact (IsClosedImmersion.iff_isFinite_and_mono f).2 ⟨hfin, hm⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.PushInv

theorem pushInvertible_of_model : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B F O : Type) [CommRing B] [Field F] [CommRing O] (b : Base l B) (U : Scheme.{0}) (s : U ⟶ Sp B) (o : Obj D l b s) (c : U ⟶ Sp F) (β : O →+* F) (C : Cpt c o.t β), IsDedFrac β → HasTheta C.t.G C.t.PP.L → PushInvertible C.t.G C.t.PP.L := by
  intro hL hL2 hL3 E _ _ _ H D l B F O _ _ _ b U s o c β C hβ hθ
  have hS : Out.SecBaseChangeAnySt := by cases hL; cases hL2; cases hL3; assumption
  have hH : Out.GlobalSectionsRankAlgClosed := by cases hL; cases hL2; cases hL3; assumption
  obtain ⟨⟨hDom, hDed⟩, -, hFr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  obtain ⟨hN, -, -, hPre, hFl, hDo, hQC⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hPB : IsPullback C.m.φ o.t.G.hom C.t.G.hom (C.jQ ≫ pullback.fst C.s (spMap β)) := C.m.cart.1
  obtain ⟨w, hw, -⟩ := C.m.lin
  have hIso : LBIso o.t.PP.L (C.t.PP.L.pull C.m.φ) := ⟨w, hw⟩
  have hSm : Smooth C.t.G.hom := by
    have sa := C.t.semi
    first | infer_instance | exact sa.1 | (cases sa; assumption)
  have hGI : GeometricallyIntegral C.t.G.hom := by
    have sa := C.t.semi
    have _ := hSm
    have _ : GeometricallyConnected C.t.G.hom := by
      first | infer_instance | (cases sa; assumption)
    exact GlobalTheory.grpObj_geometricallyIntegral_of_smooth C.X C.t.G
  exact @GlobalTheory.PushInv.pushInvertible_of_densePart C.X U hN (C.jQ ≫ pullback.fst C.s (spMap β))
    (GlobalTheory.IsNormalScheme.of_pred C.normal) hPre hFl hDo hQC
    C.t.G o.t.G C.m.φ C.t.PP.L o.t.PP.L hSm hGI hPB C.t.PP.isLB o.t.PP.isLB hIso
    (GlobalTheory.PushInv.pushInvertible_any hS hH U (GlobalTheory.Obj.toPolAV o)) hθ

end GlobalTheory.PushInv
end

