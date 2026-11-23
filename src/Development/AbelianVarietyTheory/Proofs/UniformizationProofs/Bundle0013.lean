module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteAbelianWeightDecomposition
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfStalks
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootUnit

open TopologicalSpace

theorem gs_id {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (h : y ∈ U) (a : Γ(Y, U)) :
    gs (𝟙 Y) y U a = (Y.presheaf.germ U y h).hom a := gs_eq (𝟙 Y) y U h a

theorem gs_ne_zero {Y : Scheme.{0}} [IsIntegral Y] (y : Y) (U : Y.Opens) (h : y ∈ U) {a : Γ(Y, U)} (ha : a ≠ 0) :
    gs (𝟙 Y) y U a ≠ 0 := by
  rw [gs_id y U h]
  intro e
  exact ha (germ_injective_of_isIntegral Y y h (e.trans (map_zero _).symm))

theorem exists_unit_of_stalks {Y : Scheme.{0}} [IsIntegral Y] (W : Y.Opens) (a b : Γ(Y, W))
    (hb : ∀ y ∈ W, gs (𝟙 Y) y W b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y W a = v.val * gs (𝟙 Y) y W b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y W a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y W b := by
  have loc : ∀ y : W, ∃ (V : Y.Opens) (_ : y.1 ∈ V) (_ : V ≤ W) (c : Γ(Y, V)),
      ∀ z ∈ V, gs (𝟙 Y) z W a = gs (𝟙 Y) z V c * gs (𝟙 Y) z W b := by
    rintro ⟨y, hy⟩
    obtain ⟨v, hv⟩ := h y hy
    obtain ⟨U, hU, c, hc⟩ := Y.presheaf.germ_exist v.val
    have hm : y ∈ U ⊓ W := ⟨hU, hy⟩
    have e : gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_right).op).hom a) =
        gs (𝟙 Y) y (U ⊓ W) ((Y.presheaf.map (homOfLE inf_le_left).op).hom c *
          (Y.presheaf.map (homOfLE inf_le_right).op).hom b) := by
      rw [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, hv, gs_id y U hU]
      exact congrArg (· * _) hc.symm
    rw [gs_id y _ hm, gs_id y _ hm] at e
    have e' := germ_injective_of_isIntegral Y y hm e
    refine ⟨U ⊓ W, hm, inf_le_right, (Y.presheaf.map (homOfLE inf_le_left).op).hom c, fun z hz => ?_⟩
    have := congrArg (gs (𝟙 Y) z (U ⊓ W)) e'
    rwa [gs_mul _ z _ hz, gs_res _ z inf_le_right hz, gs_res _ z inf_le_right hz] at this
  choose V hV hle c hc using loc
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hle i))
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hV _⟩) c
    (fun i j => fn_ext (V := V i ⊓ V j) fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      exact mul_right_cancel₀ (hb y (hle i hy.1)) ((hc i y hy.1).symm.trans (hc j y hy.2)))
  have key : ∀ y ∈ W, gs (𝟙 Y) y W a = gs (𝟙 Y) y W s * gs (𝟙 Y) y W b := fun y hy => by
    rw [hc ⟨y, hy⟩ y (hV _), ← hs ⟨y, hy⟩]
    exact congrArg (· * _) (gs_res (𝟙 Y) y (hle ⟨y, hy⟩) (hV ⟨y, hy⟩) s)
  have hu : IsUnit (show Γ(Y, W) from s) := Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨v, hv⟩ := h y hy
    have := mul_right_cancel₀ (hb y hy) ((key y hy).symm.trans hv)
    exact (congrArg IsUnit ((gs_id y W hy _).symm.trans this)).mpr v.isUnit
  refine ⟨hu.unit, fun y hy => ?_⟩
  rw [← gs_unit _ y W hy]
  exact key y hy

theorem exists_unit_of_stalks' {Y : Scheme.{0}} [IsIntegral Y] (W U V : Y.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (a : Γ(Y, U)) (b : Γ(Y, V)) (hb : ∀ y ∈ W, gs (𝟙 Y) y V b ≠ 0)
    (h : ∀ y ∈ W, ∃ v : (Y.presheaf.stalk y)ˣ, gs (𝟙 Y) y U a = v.val * gs (𝟙 Y) y V b) :
    ∃ r : Γ(Y, W)ˣ, ∀ y ∈ W, gs (𝟙 Y) y U a = (gm (𝟙 Y) y W r).val * gs (𝟙 Y) y V b := by
  obtain ⟨r, hr⟩ := exists_unit_of_stalks W ((Y.presheaf.map (homOfLE hU).op).hom a)
    ((Y.presheaf.map (homOfLE hV).op).hom b)
    (fun y hy => by rw [gs_res (𝟙 Y) y hV hy]; exact hb y hy)
    (fun y hy => by rw [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy]; exact h y hy)
  refine ⟨r, fun y hy => ?_⟩
  have := hr y hy
  rwa [gs_res (𝟙 Y) y hU hy, gs_res (𝟙 Y) y hV hy] at this

theorem sec_gs_ne_zero {X Y : Scheme.{0}} [IsIntegral Y] {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (hs : ∃ j, s.f j ≠ 0) (y : Y) (i : K → L.ι)
    (hy : y ∈ LB.wchart L φ i) : gs (𝟙 Y) y (LB.wchart L φ i) (s.f i) ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hne : (LB.wchart L φ j : Set Y).Nonempty := by
    by_contra hn
    exact hj (fn_ext (V := LB.wchart L φ j) fun x hx => absurd ⟨x, hx⟩ hn)
  obtain ⟨z, hz, hz'⟩ := nonempty_preirreducible_inter (LB.wchart L φ j).isOpen (LB.wchart L φ i).isOpen hne ⟨y, hy⟩
  refine gs_ne_zero y _ hy fun e => gs_ne_zero z _ hz hj ?_
  rw [sec_trans s (𝟙 Y) z hz hz', e, gs_id z _ hz', map_zero, mul_zero]

theorem trF_pull {X Y : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (y : Y) (i j : PUnit → L.ι) :
    trF (L := L) (K := PUnit) (fun _ => f) (fun _ => 1) (𝟙 Y) y i j =
      gm (𝟙 Y ≫ f) y (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) (L.g _ _) := by
  rw [trF, Fintype.prod_unique, zpow_one]

theorem exists_gen_of_pow : ∀ (X Y : Scheme.{0}) [IsIntegral Y], (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → ∀ (L : LB X), L.IsLB → ∀ (f₁ f₂ : Y ⟶ X) (l : ℕ), 1 ≤ l → ∀ (s₁ : LB.Sec (L.pull f₁)) (s₂ : LB.Sec (L.pull f₂)) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![(l : ℤ), -(l : ℤ)])), u.IsGen → (∃ j, s₂.f j ≠ 0) → (∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J ^ l = (val u (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J ^ l) → ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![f₁, f₂] ![1, -1]), r.IsGen ∧ ∀ (y : Y) (J), Good L y J → sval s₁ (𝟙 Y) y J = (val r (𝟙 Y) y J).val * sval s₂ (𝟙 Y) y J := by
  intro X Y _ hN L hL f₁ f₂ l hl s₁ s₂ u _ hs H
  have l₁ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  have l₂ : ∀ j : Fin 2 → L.ι, LB.wchart L ![f₁, f₂] j ≤ LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1
  have main : ∀ j : Fin 2 → L.ι, ∃ r : Γ(Y, LB.wchart L ![f₁, f₂] j)ˣ, ∀ y ∈ LB.wchart L ![f₁, f₂] j,
      gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₁) (fun _ => j 0)) (s₁.f fun _ => j 0) =
        (gm (𝟙 Y) y _ r).val *
          gs (𝟙 Y) y (LB.wchart L (K := PUnit) (fun _ => f₂) (fun _ => j 1)) (s₂.f fun _ => j 1) := by
    intro j
    exact exists_unit_of_stalks' (LB.wchart L ![f₁, f₂] j) _ _ (l₁ j) (l₂ j) _ _
      (fun y hy => sec_gs_ne_zero s₂ hs y _ (l₂ j hy))
      (fun y hy => by
        choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
        have hJ' : Good L y J := hJ
        haveI := hN y
        have as : Associated (sval s₂ (𝟙 Y) y J) (sval s₁ (𝟙 Y) y J) :=
          (Associated.pow_iff (by omega : l ≠ 0)).1 ⟨val u (𝟙 Y) y J, (_root_.mul_comm _ _).trans (H y J hJ').symm⟩
        obtain ⟨v, hv⟩ := as
        have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ j hy) (hJ'.mem (K := PUnit) (fun _ => f₁) (𝟙 Y))
        have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ j hy) (hJ'.mem (K := PUnit) (fun _ => f₂) (𝟙 Y))
        change _ = _ * sval s₁ (𝟙 Y) y J at e₁
        change _ = _ * sval s₂ (𝟙 Y) y J at e₂
        rw [e₁, e₂, ← hv]
        generalize trF (L := L) (K := PUnit) (fun _ => f₁) (fun _ => 1) (𝟙 Y) y _ _ = t₁
        generalize trF (L := L) (K := PUnit) (fun _ => f₂) (fun _ => 1) (𝟙 Y) y _ _ = t₂
        refine ⟨t₁ * v * t₂⁻¹, ?_⟩
        rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, Units.val_mul]
        ring)
  choose r hr using main
  refine ⟨⟨r⟩, fun i j => unit_ext fun y hy => ?_, fun y J hJ => hr _ y (hJ.mem ![f₁, f₂] (𝟙 Y))⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y i j hy.1 hy.2) (gm_res _ y _ hy _))).symm)
  have e₁ := sec_trans s₁ (𝟙 Y) y (l₁ i hy.1) (l₁ j hy.2)
  have e₂ := sec_trans s₂ (𝟙 Y) y (l₂ i hy.1) (l₂ j hy.2)
  have hb := sec_gs_ne_zero s₂ hs y _ (l₂ j hy.2)
  rw [hr i y hy.1, hr j y hy.2, e₂, trF_pull, trF_pull, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
    ← Units.val_mul] at e₁
  have e := Units.ext (mul_right_cancel₀ hb e₁)
  rw [Fin.prod_univ_two]
  change gm (𝟙 Y) y _ (r i) = gm (𝟙 Y ≫ f₁) y _ (L.g (i 0) (j 0)) ^ (1 : ℤ) *
    gm (𝟙 Y ≫ f₂) y _ (L.g (i 1) (j 1)) ^ (-1 : ℤ) * gm (𝟙 Y) y _ (r j)
  rw [zpow_one, zpow_neg_one, mul_right_comm, ← e, mul_inv_cancel_right]

end GlobalTheory.RootUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeisenbergWeightSpaceFinrank
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeisenbergWeightDim

variable {F : Type} [Field F] {A : Type} [CommGroup A] {E : Type} [AddCommGroup E] [Module F E]

theorem units_eq_of_smul_eq {x y : Fˣ} {w : E} (hw : w ≠ 0) (h : (x : F) • w = (y : F) • w) :
    x = y :=
  Units.ext (smul_left_injective F hw h)

variable [Nontrivial E] {e : A → A → Fˣ} {Φ : A → (E ≃ₗ[F] E)}

theorem comm_swap (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (a b : A) :
    e a b * e b a = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hw : Φ a (Φ b v) ≠ 0 := by simpa using hv
  apply units_eq_of_smul_eq hw
  rw [Units.val_mul, mul_smul, ← hc b a v, ← hc a b v, Units.val_one, one_smul]

theorem comm_mul_left (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (a a' b : A) :
    e (a * a') b = e a b * e a' b := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hw : Φ b (Φ (a * a') v) ≠ 0 := by simpa using hv
  apply units_eq_of_smul_eq hw
  obtain ⟨c, h⟩ := hm a a'
  rw [← hc, h, h, hc a' b, map_smul, hc a b, map_smul, Units.val_mul]
  simp only [smul_smul]
  congr 1
  ring

theorem comm_mul_right (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) (a b b' : A) :
    e a (b * b') = e a b * e a b' := by
  rw [eq_inv_of_mul_eq_one_left (comm_swap hc a (b * b')),
    eq_inv_of_mul_eq_one_left (comm_swap hc a b), eq_inv_of_mul_eq_one_left (comm_swap hc a b'),
    comm_mul_left hm hc, mul_inv]

theorem exists_comm_eq [Finite A] [HasEnoughRootsOfUnity F (Monoid.exponent A)]
    (hm : ∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v))
    (hc : ∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v))
    (hn : ∀ a, (∀ b, e a b = 1) → a = 1) (T : Subgroup A) (χ : T →* Fˣ) :
    ∃ a, ∀ t : T, e t a = χ t := by
  let P : A →* (A →* Fˣ) :=
    MonoidHom.mk' (fun a => MonoidHom.mk' (fun b => e b a) (fun b b' => comm_mul_left hm hc b b' a))
      (fun a a' => by
        apply MonoidHom.ext
        intro b
        exact comm_mul_right hm hc b a a')
  have hinj : Function.Injective P := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply hn
    intro b
    have h1 : e b a = 1 := DFunLike.congr_fun ha b
    have h2 := comm_swap hc a b
    rwa [h1, _root_.mul_one] at h2
  haveI : Finite (A →* Fˣ) :=
    Finite.of_equiv A (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity A F).some.toEquiv.symm
  have hbij : Function.Bijective P :=
    hinj.bijective_of_nat_card_le (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A F).le
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective F T χ
  obtain ⟨a, ha⟩ := hbij.2 ψ
  refine ⟨a, fun t => ?_⟩
  rw [← hψ, ← ha]
  rfl

end GlobalTheory.HeisenbergWeightDim

namespace GlobalTheory


open HeisenbergWeightDim in
theorem heisenberg_weightSpace_finrank :
    ∀ (F : Type) [Field F] [IsAlgClosed F] (A : Type) [CommGroup A] [Finite A] (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)), (Nat.card A : F) ≠ 0 → Module.finrank F E ^ 2 = Nat.card A → (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) → (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ (T : Subgroup A) (lam : T →* (E ≃ₗ[F] E)), (∀ t : T, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v) → ∀ Wt : (T →* Fˣ) → Submodule F E, (∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v) → (⨆ χ, Wt χ = ⊤) ∧ ∀ χ, Module.finrank F (Wt χ) * Nat.card T = Module.finrank F E := by
  intro F _ _ A _ _ E _ _ _ e Φ hA hdim hm hc hn T lam hlam Wt hWt
  classical
  have hpos : 0 < Nat.card A := Nat.card_pos
  haveI : Nontrivial E := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rcases Nat.eq_zero_or_pos (Module.finrank F E) with h | h
    · rw [h] at hdim
      omega
    · exact h
  haveI : NeZero ((Nat.card A : ℕ) : F) := ⟨hA⟩
  haveI : NeZero (Nat.card A) := ⟨hpos.ne'⟩
  haveI h0 : HasEnoughRootsOfUnity F (Nat.card A) := inferInstance
  haveI hAe : HasEnoughRootsOfUnity F (Monoid.exponent A) :=
    h0.of_dvd F Group.exponent_dvd_nat_card
  haveI : HasEnoughRootsOfUnity F (Monoid.exponent T) :=
    hAe.of_dvd F (Monoid.exponent_submonoid_dvd T.toSubmonoid)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (Nat.card A)
  let ρ : Representation F T E :=
    { toFun := fun t => (lam t : E →ₗ[F] E)
      map_one' := by ext v; simp
      map_mul' := by intro s t; ext v; simp }
  obtain ⟨hfin, hint, -⟩ := finiteAbelian_weightDecomposition F (Nat.card A) ζ hpos
    (IsUnit.mk0 _ hA) hζ T (fun t => Subtype.ext (by simp)) E ρ
  have hW : (fun c : T →* Fˣ => ⨅ t, LinearMap.ker (ρ t - (c t : F) • LinearMap.id)) = Wt := by
    funext c
    ext v
    rw [hWt, FiniteAbelianWeights.mem_weightSpace_iff]
    rfl
  rw [hW] at hint
  refine ⟨hint.submodule_iSup_eq_top, ?_⟩
  have hle : ∀ χ ψ, Module.finrank F (Wt χ) ≤ Module.finrank F (Wt ψ) := by
    intro χ ψ
    obtain ⟨a, ha⟩ := exists_comm_eq hm hc hn T (ψ * χ⁻¹)
    have hmap : (Wt χ).map (Φ a : E →ₗ[F] E) ≤ Wt ψ := by
      rintro _ ⟨v, hv, rfl⟩
      rw [hWt]
      intro t
      obtain ⟨c, h⟩ := hlam t
      have h1 := (hWt χ v).1 hv t
      simp only [LinearEquiv.coe_coe]
      rw [h, hc, smul_comm, ← map_smul, ← h, h1, map_smul, smul_smul, ha, ← Units.val_mul]
      simp
    exact (LinearEquiv.finrank_map_eq (Φ a) (Wt χ)).symm.le.trans (Submodule.finrank_mono hmap)
  intro χ
  haveI := Fintype.ofFinite (T →* Fˣ)
  have h1 : Module.finrank F E = ∑ ψ, Module.finrank F (Wt ψ) := by
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap Wt) hint).finrank_eq,
      Module.finrank_directSum]
  rw [h1, Finset.sum_congr rfl (fun ψ _ => le_antisymm (hle ψ χ) (hle χ ψ)), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T F, smul_eq_mul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeisenbergWeightSpaceIrreducible
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem heisenberg_weightSpace_irreducible : ∀ (F : Type) [Field F] [IsAlgClosed F] (A : Type) [CommGroup A] [Finite A] (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E] (e : A → A → Fˣ) (Φ : A → (E ≃ₗ[F] E)), (Nat.card A : F) ≠ 0 → Module.finrank F E ^ 2 = Nat.card A → (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) → (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ (T : Subgroup A) (lam : T →* (E ≃ₗ[F] E)), (∀ t : T, ∃ c : Fˣ, ∀ v, lam t v = (c : F) • Φ t v) → ∀ Wt : (T →* Fˣ) → Submodule F E, (∀ χ v, v ∈ Wt χ ↔ ∀ t, lam t v = (χ t : F) • v) → ∀ (χ : T →* Fˣ) (U : Submodule F E), U ≤ Wt χ → (∀ h : A, (∀ t : T, e t h = 1) → ∀ v ∈ U, Φ h v ∈ U) → U = ⊥ ∨ U = Wt χ := by
  classical
  intro F _ _ A _ _ E _ _ _ e Φ hcard hdim hmul hcomm hnd T lam hlam Wt hWt χ U hU hstab
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  haveI : Nontrivial E := ⟨⟨u, 0, hu0⟩⟩

  have hel : ∀ a b c, e (a * b) c = e a c * e b c := by
    intro a b c
    obtain ⟨k, hk⟩ := hmul a b
    have h1 := hcomm (a * b) c u
    rw [hk, hk, hcomm b c u, map_smul, hcomm a c, map_smul, smul_smul, smul_smul, smul_smul] at h1
    have h2 : Φ c (Φ a (Φ b u)) ≠ 0 := fun h => hu0 (by simpa using h)
    have h3 := smul_left_injective F h2 h1
    apply Units.ext
    have hk0 : (k : F) ≠ 0 := k.ne_zero
    apply mul_left_cancel₀ hk0
    rw [Units.val_mul]
    linear_combination -h3
  have he1 : ∀ c, e 1 c = 1 := by
    intro c
    have := hel 1 1 c
    rw [_root_.mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinj : Function.Injective fun a b => (e a b : F) := by
    intro a a' h
    have : a * a'⁻¹ = 1 := by
      apply hnd
      intro b
      have hb : e a b = e a' b := Units.ext (congrFun h b)
      rw [hel, hb, ← hel, mul_inv_cancel, he1]
    exact mul_inv_eq_one.mp this
  have hli : LinearIndependent F fun a => (Φ a : E →ₗ[F] E) :=
    linearIndependent_of_comm_smul _ _ (fun a => (Φ a).injective) (fun a b v => hcomm a b v) hinj
  haveI := Fintype.ofFinite A
  have hspan : Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, ← sq, hdim, Nat.card_eq_fintype_card]
  refine le_antisymm hU fun v hv => ?_
  obtain ⟨f, hf⟩ : ∃ f : E →ₗ[F] E, f u = v := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hu0
    exact ⟨φ.smulRight v, by simp [hφ]⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span F (Set.range fun a => (Φ a : E →ₗ[F] E)))
  have hvs : v = ∑ a, c a • Φ a u := by
    rw [← hf, ← hc]; simp
  have hu := (hWt χ u).mp (hU huU)
  have hv' := (hWt χ v).mp hv
  have hlamΦ : ∀ (t : T) a, lam t (Φ a u) = ((χ t : F) * (e t a : F)) • Φ a u := by
    intro t a
    obtain ⟨k, hk⟩ := hlam t
    rw [hk, hcomm, smul_comm, ← map_smul, ← hk, hu, map_smul, smul_smul, mul_comm]
  have hvt : ∀ t : T, v = ∑ a, (c a * (e t a : F)) • Φ a u := by
    intro t
    have h1 := hv' t
    have h0 : (χ t : F) ≠ 0 := (χ t).ne_zero
    apply smul_right_injective E h0
    simp only
    rw [← h1]
    conv_lhs => rw [hvs]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hlamΦ, smul_smul, smul_smul]
    congr 1; ring
  have hT : (Fintype.card T : F) ≠ 0 := by
    intro h
    apply hcard
    rw [← Subgroup.card_mul_index T, Nat.cast_mul, Nat.card_eq_fintype_card, h, zero_mul]
  have hsum : (Fintype.card T : F) • v = ∑ a, (c a * ∑ t : T, (e t a : F)) • Φ a u := by
    have : (Fintype.card T : F) • v = ∑ _t : T, v := by
      rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [this, Finset.sum_congr rfl fun t _ => hvt t, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_smul]
  rw [← U.smul_mem_iff hT, hsum]
  refine U.sum_mem fun a _ => ?_
  by_cases ha : ∀ t : T, e t a = 1
  · exact U.smul_mem _ (hstab a ha u huU)
  · let ψ : T →* F :=
      { toFun := fun t => (e t a : F)
        map_one' := by simp [he1]
        map_mul' := fun s t => by simp [hel] }
    have hψ : ψ ≠ 1 := by
      intro h
      apply ha
      intro t
      apply Units.ext
      exact DFunLike.congr_fun h t
    have := sum_hom_units_eq_zero ψ hψ
    have h2 : ∑ t : T, (e t a : F) = 0 := this
    rw [h2, mul_zero, zero_smul]
    exact U.zero_mem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsoLimit

open ThickeningClosed

theorem isIso_of_isClosedImmersion {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f] (j : Z ⟶ X)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : pullback f (thick V (IsLocalRing.maximalIdeal V) n) ⟶ Z,
      l ≫ j = pullback.fst f (thick V (IsLocalRing.maximalIdeal V) n)) : IsIso j := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have key : ∀ x, x ∈ zeroLocusOpen j.ker := by
    intro x
    by_contra hx
    have hc : IsClosed (f '' (zeroLocusOpen j.ker)ᶜ) :=
      f.isClosedMap _ (isOpen_zeroLocusOpen _).isClosed_compl
    obtain ⟨y, hy, hy'⟩ :=
      (IsLocalRing.specializes_closedPoint (R := V) (f x)).mem_closed hc ⟨x, hx, rfl⟩
    refine hy (mem_of_thickenings _ f j h y ?_)
    rw [hy']
    exact le_rfl
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  refine le_bot_iff.1 fun U a ha ↦ ?_
  change a = 0
  refine eq_zero_of_localization a fun J hJ ↦ ?_
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem j.ker U ⟨J, hJ.isPrime⟩ (key _) ha
  exact (IsLocalization.map_eq_zero_iff J.primeCompl _ a).2 ⟨⟨s, hs⟩, hsa⟩

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Γ₁ Y : Over (Spec (CommRingCat.of V))) (p : Γ₁ ⟶ Y) [IsProper Y.hom] [IsProper p.left], (∀ e, IsIso ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)) → IsIso p := by
  intro V _ _ _ _ Γ₁ Y p _ _ h
  have hw : p.left ≫ Y.hom = Γ₁.hom := Over.w p
  let q (e : ℕ) : pullback Γ₁.hom (thick V (IsLocalRing.maximalIdeal V) e) ⟶
      pullback Y.hom (thick V (IsLocalRing.maximalIdeal V) e) :=
    ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p).left
  have hq (e : ℕ) : IsIso (q e) := by
    haveI := h e
    exact inferInstanceAs (IsIso ((Over.forget _).map
      ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)))
  have q1 (e : ℕ) : q e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ p.left := pullback.lift_fst _ _ _
  have q2 (e : ℕ) : q e ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hd : IsIso (pullback.diagonal p.left) := by
    refine isIso_of_isClosedImmersion (pullback.fst p.left p.left ≫ p.left ≫ Y.hom) _ fun n ↦ ?_
    have c := pullback.condition (f := pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (g := thick V (IsLocalRing.maximalIdeal V) n)
    have c' := pullback.condition (f := p.left) (g := p.left)
    set u := pullback.fst (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    set v := pullback.snd (pullback.fst p.left p.left ≫ p.left ≫ Y.hom)
      (thick V (IsLocalRing.maximalIdeal V) n)
    have e : pullback.lift (f := Γ₁.hom) (u ≫ pullback.fst _ _) v
          (by rw [← c, ← hw, Category.assoc]) =
        pullback.lift (f := Γ₁.hom) (u ≫ pullback.snd _ _) v
          (by rw [← c, ← hw, Category.assoc, ← reassoc_of% c']) := by
      haveI := hq n
      rw [← cancel_mono (q n)]
      apply pullback.hom_ext
      · simp only [Category.assoc, q1, pullback.lift_fst_assoc, c']
      · simp only [Category.assoc, q2, pullback.lift_snd]
    have e' := congrArg (· ≫ pullback.fst _ _) e
    simp only [pullback.lift_fst] at e'
    refine ⟨u ≫ pullback.fst _ _, ?_⟩
    apply pullback.hom_ext
    · simp
    · simp [e']
  have hm : Mono p.left := (pullback.isIso_diagonal_iff p.left).1 hd
  have hc : IsClosedImmersion p.left :=
    (IsClosedImmersion.iff_isProper_and_mono p.left).2 ⟨‹_›, hm⟩
  have hi : IsIso p.left := by
    refine isIso_of_isClosedImmersion Y.hom _ fun n ↦ ?_
    haveI := hq n
    exact ⟨inv (q n) ≫ pullback.fst _ _, by rw [Category.assoc, ← q1, IsIso.inv_hom_id_assoc]⟩
  have : IsIso ((Over.forget _).map p) := hi
  exact isIso_of_reflects_iso p (Over.forget _)

end GlobalTheory.IsoLimit
end

