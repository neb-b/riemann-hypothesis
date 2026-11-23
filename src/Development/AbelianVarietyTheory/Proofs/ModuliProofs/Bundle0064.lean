module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCechDataPullbackOfLineBundleOnOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LBPush

theorem gm_eq_one {X Z : Scheme.{0}} (κ : Z ⟶ X) [IsOpenImmersion κ] (z : Z) {U : X.Opens} (h : κ z ∈ U)
    {a : Γ(X, U)ˣ} (e : gm κ z U a = 1) : gm (𝟙 X) (κ z) U a = 1 := by
  have hU : (𝟙 X) (κ z) ∈ U := h
  unfold gm pullU at e ⊢
  rw [dite_eq_left h] at e
  rw [dite_eq_left hU]
  have e' := congrArg Units.val e
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso (κ.stalkMap z)).1
  refine ((Scheme.Hom.germ_stalkMap_apply κ U z h (a : Γ(X, U))).trans ?_).trans (map_one _).symm
  exact e'

theorem exists_unit_image {X Y : Scheme.{0}} (κ : Y ⟶ X) [IsOpenImmersion κ] (V : Y.Opens) (a : Γ(Y, V)ˣ) :
    ∃ b : Γ(X, κ ''ᵁ V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V →
      gm (r ≫ κ) z (κ ''ᵁ V) b = gm r z V a := by
  refine ⟨Units.map (κ.appIso V).inv.hom a, fun Z r z hz => ?_⟩
  have h1 : (r ≫ κ) z ∈ κ ''ᵁ V := ⟨r z, hz, rfl⟩
  unfold gm pullU
  rw [dite_eq_left hz, dite_eq_left h1]
  apply Units.ext
  refine (Scheme.Hom.germ_stalkMap_apply (r ≫ κ) (κ ''ᵁ V) z h1 _).symm.trans ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply r V z hz (a : Γ(Y, V)))
  rw [Scheme.Hom.stalkMap_comp]
  refine congrArg (r.stalkMap z) ?_
  refine (Scheme.Hom.germ_stalkMap_apply κ (κ ''ᵁ V) (r z) h1 _).trans ?_
  refine (congrArg (ConcreteCategory.hom (Y.presheaf.germ (κ ⁻¹ᵁ κ ''ᵁ V) (r z) h1))
    (Scheme.Hom.appIso_inv_app_apply κ V (a : Γ(Y, V)))).trans ?_
  exact TopCat.Presheaf.germ_res_apply' Y.presheaf _ (r z) _ _

private theorem gm_res_eq_gm {S T : Scheme.{0}} (f : T ⟶ S) (t : T) {U V : S.Opens} (hVU : V ≤ U) (a : Γ(S, U)ˣ)
    (ht : f t ∈ V) : gm f t V (res hVU a) = gm f t U a := by
  unfold gm pullU res
  rw [dite_eq_left ht, dite_eq_left (hVU ht)]
  apply Units.ext
  refine (Scheme.Hom.germ_stalkMap_apply f V t ht _).symm.trans ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply f U t (hVU ht) (a : Γ(S, U)))
  congr 1
  exact TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE hVU) (f t) ht _

private theorem units_eq_of_gm_eq {S : Scheme.{0}} {W : S.Opens} {a b : Γ(S, W)ˣ}
    (h : ∀ x, x ∈ W → gm (𝟙 S) x W a = gm (𝟙 S) x W b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext S.sheaf W
  intro x hx
  have := congrArg Units.val (h x hx)
  unfold gm pullU at this
  rw [dite_eq_left (show (𝟙 S) x ∈ W from hx)] at this
  exact this

private theorem gm_id_pullU' {S T : Scheme.{0}} (f : T ⟶ S) (t : T) (W : S.Opens) (c : Γ(S, W)ˣ) (ht : f t ∈ W) :
    gm (𝟙 T) t (f ⁻¹ᵁ W) (pullU f W c) = gm f t W c := by
  unfold gm
  rw [dite_eq_left (show (𝟙 T) t ∈ f ⁻¹ᵁ W from ht), dite_eq_left ht]
  rfl

private theorem gm_inv_moduli {S T : Scheme.{0}} (f : T ⟶ S) (t : T) (U : S.Opens) (a : Γ(S, U)ˣ) :
    gm f t U a⁻¹ = (gm f t U a)⁻¹ :=
  map_inv _ _

private theorem res_eq_mul_inv_mul_of_gm {S : Scheme.{0}} {W A B C D : S.Opens} (hA : W ≤ A) (hB : W ≤ B) (hC : W ≤ C)
    (hD : W ≤ D) (a : Γ(S, A)ˣ) (b : Γ(S, B)ˣ) (c : Γ(S, C)ˣ) (d : Γ(S, D)ˣ)
    (h : ∀ x, x ∈ W → gm (𝟙 S) x A a = gm (𝟙 S) x B b * (gm (𝟙 S) x C c)⁻¹ * gm (𝟙 S) x D d) :
    res hA a = res hB b * (res hC c)⁻¹ * res hD d := by
  apply units_eq_of_gm_eq
  intro x hx
  rw [map_mul, map_mul, gm_inv_moduli, gm_res_eq_gm (𝟙 S) x hA a hx, gm_res_eq_gm (𝟙 S) x hB b hx,
    gm_res_eq_gm (𝟙 S) x hC c hx, gm_res_eq_gm (𝟙 S) x hD d hx]
  exact h x hx

theorem exists_push : ∀ (X Y : Scheme.{0}) (ψ : Y ⟶ X) [IsOpenImmersion ψ] (L : LB Y), L.IsLB →
    ∃ M : LB X, ⨆ a, M.U a = ψ.opensRange ∧
      (∀ (a : M.ι) (x : X), x ∈ M.U a → gm (𝟙 X) x (M.U a ⊓ M.U a) (M.g a a) = 1) ∧
      (M.pull ψ).IsLB ∧ LBIso L (M.pull ψ) := by
  intro X Y ψ _ L hL
  have himg : ∀ i j, ψ ''ᵁ L.U i ⊓ ψ ''ᵁ L.U j ≤ ψ ''ᵁ (L.U i ⊓ L.U j) := by
    rintro i j x ⟨⟨y, hy, rfl⟩, ⟨y', hy', e⟩⟩
    have e' : y' = y := ψ.isOpenEmbedding.injective e
    rw [e'] at hy'
    exact ⟨y, ⟨hy, hy'⟩, rfl⟩
  choose b hb using fun i j => exists_unit_image ψ (L.U i ⊓ L.U j) (L.g i j)
  let M : LB X := ⟨L.ι, fun i => ψ ''ᵁ L.U i, fun i j => res (himg i j) (b i j)⟩
  have hcov : ∀ y : Y, ∃ i, y ∈ L.U i := by
    intro y
    have hy : y ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hy
  have hmem : ∀ (j : PUnit → L.ι) (y : Y), y ∈ (M.pull ψ).U j ↔ y ∈ L.U (j PUnit.unit) := by
    intro j y
    constructor
    · intro hy
      obtain ⟨y', hy', e⟩ := Set.mem_iInter.1 hy PUnit.unit
      rwa [ψ.isOpenEmbedding.injective e] at hy'
    · intro hy
      exact Set.mem_iInter.2 fun k => ⟨y, hy, rfl⟩
  have Gself : ∀ i y, y ∈ L.U i → gm (𝟙 Y) y (L.U i ⊓ L.U i) (L.g i i) = 1 := by
    intro i y hy
    have := congrArg (gm (𝟙 Y) y _) (hL.g_self i)
    rw [gm_res_eq_gm (𝟙 Y) y, map_one] at this
    · exact this
    · exact hy
  have Gcoc : ∀ i j k y, y ∈ L.U i → y ∈ L.U j → y ∈ L.U k →
      gm (𝟙 Y) y (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 Y) y (L.U j ⊓ L.U k) (L.g j k) =
        gm (𝟙 Y) y (L.U i ⊓ L.U k) (L.g i k) := by
    intro i j k y hi hj hk
    have := congrArg (gm (𝟙 Y) y _) (hL.cocycle i j k)
    rw [map_mul, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y] at this
    · exact this
    all_goals exact ⟨⟨hi, hj⟩, hk⟩
  have key : ∀ i j y, y ∈ L.U i → y ∈ L.U j →
      gm ψ y (M.U i ⊓ M.U j) (M.g i j) = gm (𝟙 Y) y (L.U i ⊓ L.U j) (L.g i j) := by
    intro i j y hi hj
    have := hb i j Y (𝟙 Y) y ⟨hi, hj⟩
    rw [Category.id_comp] at this
    exact (gm_res_eq_gm ψ y (himg i j) (b i j) ⟨⟨y, hi, rfl⟩, ⟨y, hj, rfl⟩⟩).trans this
  have hN : ∀ (j j' : PUnit → L.ι) y, y ∈ L.U (j PUnit.unit) → y ∈ L.U (j' PUnit.unit) →
      gm (𝟙 Y) y ((M.pull ψ).U j ⊓ (M.pull ψ).U j') ((M.pull ψ).g j j') =
        gm (𝟙 Y) y (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)) := by
    intro j j' y h1 h2
    rw [← key _ _ y h1 h2]
    unfold LB.pull LB.LinComb
    dsimp only
    rw [map_prod, Fintype.prod_unique, map_zpow, zpow_one]
    refine (gm_res_eq_gm (𝟙 Y) y _ _ ?_).trans (gm_id_pullU' ψ y (M.U (j default) ⊓ M.U (j' default)) _ ?_)
    all_goals first
      | exact ⟨(hmem j y).2 h1, (hmem j' y).2 h2⟩
      | exact ⟨⟨y, h1, rfl⟩, ⟨y, h2, rfl⟩⟩
  refine ⟨M, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨i, y, hy, rfl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact ⟨y, rfl⟩
    · rintro x ⟨y, rfl⟩
      obtain ⟨i, hi⟩ := hcov y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, hi, rfl⟩
  · rintro a x ⟨y, hy, rfl⟩
    exact gm_eq_one ψ y (U := M.U a ⊓ M.U a) ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩ ((key a a y hy hy).trans (Gself a y hy))
  · apply eq_top_iff.2
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem _ y).2 hi⟩
  · intro j
    apply units_eq_of_gm_eq
    intro y hy
    have h1 := (hmem j y).1 hy
    rw [gm_res_eq_gm (𝟙 Y) y, map_one, hN j j y h1 h1, Gself _ y h1]
    exact hy
  · intro j j' j''
    apply units_eq_of_gm_eq
    intro y hy
    have h1 := (hmem j y).1 hy.1.1
    have h2 := (hmem j' y).1 hy.1.2
    have h3 := (hmem j'' y).1 hy.2
    rw [map_mul, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, gm_res_eq_gm (𝟙 Y) y, hN j j' y h1 h2, hN j' j'' y h2 h3,
      hN j j'' y h1 h3]
    · exact Gcoc _ _ _ y h1 h2 h3
    all_goals exact hy
  · unfold LBIso LB.Iso LB.div LB.Gen.IsGen
    have hle : ∀ p : (PUnit → L.ι) × L.ι, (M.pull ψ).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2 :=
      fun p y hy => ⟨(hmem p.1 y).1 hy.1, hy.2⟩
    refine ⟨⟨fun p => res (hle p) (L.g (p.1 PUnit.unit) p.2)⟩, ?_⟩
    intro p q
    refine res_eq_mul_inv_mul_of_gm _ _ _ _ _ _ _ _ (fun y hy => ?_)
    have ha := (hmem p.1 y).1 hy.1.1
    have hi := hy.1.2
    have ha' := (hmem q.1 y).1 hy.2.1
    have hi' := hy.2.2
    have eA := gm_res_eq_gm (𝟙 Y) y (hle p) (L.g (p.1 PUnit.unit) p.2) hy.1
    have eD := gm_res_eq_gm (𝟙 Y) y (hle q) (L.g (q.1 PUnit.unit) q.2) hy.2
    have eB := hN p.1 q.1 y ha ha'
    have hG : gm (𝟙 Y) y (L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2) =
        gm (𝟙 Y) y (L.U (p.1 PUnit.unit) ⊓ L.U (q.1 PUnit.unit)) (L.g (p.1 PUnit.unit) (q.1 PUnit.unit)) *
          (gm (𝟙 Y) y (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ *
            gm (𝟙 Y) y (L.U (q.1 PUnit.unit) ⊓ L.U q.2) (L.g (q.1 PUnit.unit) q.2) := by
      rw [mul_right_comm, Gcoc _ _ _ y ha ha' hi', ← Gcoc _ _ _ y ha hi hi', mul_inv_cancel_right]
    refine eA.trans (hG.trans ?_)
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) eB.symm rfl) eD.symm

end GlobalTheory.LBPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenOfIsLocallyNoetherian
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLocus

theorem exists_idempotent {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) {u : R} (hu : u ^ n = 1) :
    ∃ e : R, IsIdempotentElem e ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), φ u = 1 ↔ φ e = 1 := by
  obtain ⟨m, hm⟩ := hn.exists_left_inv
  have h₀ : (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = 0 := by rw [geom_sum_mul, hu, sub_self]
  have h₁ : u * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    linear_combination m * h₀
  have h₂ : ∀ i : ℕ, u ^ i * (m * ∑ i ∈ Finset.range n, u ^ i) = m * ∑ i ∈ Finset.range n, u ^ i := by
    intro i
    induction i with
    | zero => rw [pow_zero, _root_.one_mul]
    | succ i ih => rw [pow_succ, _root_.mul_assoc, h₁, ih]
  refine ⟨m * ∑ i ∈ Finset.range n, u ^ i, ?_, fun R' _ φ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · show _ * _ = _
    rw [_root_.mul_assoc, Finset.sum_mul, Finset.sum_congr rfl fun i _ => h₂ i, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, ← _root_.mul_assoc, hm, _root_.one_mul]
  · have := congrArg φ hm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      _root_.mul_one, map_natCast, map_one] at this ⊢
    exact this
  · have := congrArg φ h₁
    rwa [map_mul, h, _root_.mul_one] at this

theorem isClosed_basicOpen {X : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClosed (X.basicOpen e : Set X) := by
  have : (X.basicOpen e : Set X) = (X.basicOpen (1 - e) : Set X)ᶜ := by
    ext x
    constructor
    · intro h h'
      have hx : x ∈ X.basicOpen (e * (1 - e)) := by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩
      rw [he.mul_one_sub_self, Scheme.basicOpen_zero] at hx
      exact hx
    · intro h
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (X.presheaf.germ ⊤ x trivial e) with h' | h'
      · exact (X.mem_basicOpen e x trivial).2 h'
      · exact absurd ((X.mem_basicOpen (U := ⊤) (1 - e) x trivial).2 (by rwa [map_sub, map_one])) h
  rw [this]
  exact (X.basicOpen (1 - e)).isOpen.isClosed_compl

theorem appTop_eq_one_iff {X Y : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) (h : Y ⟶ X) :
    h.appTop.hom e = 1 ↔ Set.range h ⊆ X.basicOpen e := by
  have p : h ⁻¹ᵁ X.basicOpen e = Y.basicOpen (h.appTop.hom e) := Scheme.preimage_basicOpen h e
  constructor
  · rintro H _ ⟨y, rfl⟩
    have : y ∈ h ⁻¹ᵁ X.basicOpen e := by
      rw [p, H, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    exact this
  · intro H
    have hu : IsUnit (h.appTop.hom e) := by
      refine RingedSpace.isUnit_of_isUnit_germ Y.toRingedSpace ⊤ _ fun y hy => ?_
      have : y ∈ Y.basicOpen (h.appTop.hom e) := by rw [← p]; exact H ⟨y, rfl⟩
      exact (Y.mem_basicOpen _ y hy).1 this
    exact hu.mul_left_cancel ((he.map h.appTop.hom).eq.trans (_root_.mul_one _).symm)

theorem exists_clopen_eq {X : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤))) {c c₀ : Γ(X, ⊤)ˣ}
    (hc : c ^ n = 1) (hc₀ : c₀ ^ n = 1) :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ X),
      Units.map h.appTop.hom.toMonoidHom c = Units.map h.appTop.hom.toMonoidHom c₀ ↔ Set.range h ⊆ U := by
  have hu : (c * c₀⁻¹).val ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hc, hc₀, inv_one, _root_.mul_one, Units.val_one]
  obtain ⟨e, he, H⟩ := exists_idempotent hn hu
  refine ⟨X.basicOpen e, isClosed_basicOpen he, fun Y h => ?_⟩
  rw [← appTop_eq_one_iff he, ← H, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← Units.val_eq_one]
  rfl

theorem pow_eq_one (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℕ) {T : Over S} {x y : T ⟶ P.A}
    (hx : x ^ k = 1) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have hpow : ∀ j : ℕ, WeilIs P.A P.L k (x ^ (j + 1)) y (c ^ (j + 1)) := by
    intro j
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c]; exact weilIs_mul_left hG S P k T _ _ _ _ _ ih hc
  have h := hpow k
  rw [pow_succ, hx, _root_.one_mul] at h
  have := CommutatorPairing.weilIs_unique hG P.isAb P.isLB h hc
  rwa [pow_succ, mul_eq_right] at this

theorem exists_clopen_of_weilIs (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) {T : Over S}
    {x y : T ⟶ P.A} {c c₀ : Γ(T.left, ⊤)ˣ} (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1) (hc : c ^ n = 1)
    (h₀ : WeilIs P.A P.L n x y c₀) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by
  obtain ⟨U, hU, H⟩ := exists_clopen_eq hn hc (pow_eq_one hG P n hx h₀)
  refine ⟨U, hU, fun T' h => ?_⟩
  have h₁ := CommPairing.weilIs_pull hG P.isAb P.isLB h h₀
  rw [← H]
  exact ⟨fun h₂ => CommutatorPairing.weilIs_unique hG P.isAb P.isLB h₂ h₁, fun e => e ▸ h₁⟩

theorem exists_clopen_of_lift : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A),
    x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) →
    ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), 0 < n →
      IsUnit (n : Γ(T.left, ⊤)) → x ^ n = 1 → y ^ n = 1 → c ^ n = 1 →
      ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
        WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔
          Set.range h.left ⊆ U := by
  intro hG hl S P n T x y c _ hn hx hy hc
  obtain ⟨c₀, h₀, -⟩ := CommutatorPairing.existsUnique_weilIs hG hl S P n T x y hx hy
  exact exists_clopen_of_weilIs hG P n hn hx hc h₀

theorem exists_clopen_of_isLocallyNoetherian (hL : Laws) (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (n : ℕ) (T : Over S) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ) (hn : IsUnit (n : Γ(T.left, ⊤))) (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hc : c ^ n = 1) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧ ∀ (T' : Over S) (h : T' ⟶ T),
      WeilIs P.A P.L n (h ≫ x) (h ≫ y) (Units.map (h.left.appTop).hom.toMonoidHom c) ↔ Set.range h.left ⊆ U := by
  obtain ⟨c₀, h₀, -⟩ := (hL.weil S P n T).1 x y hx hy
  exact exists_clopen_of_weilIs hL.globalFns P n hn hx hc h₀

end GlobalTheory.PairingLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LinDescent

private lemma isOpenImmersion_of_section_of_etale' {X Y : Scheme.{0}} (s : Y ⟶ X) (g : X ⟶ Y)
    [Etale g] (h : s ≫ g = 𝟙 Y) : IsOpenImmersion s := by
  have hP : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr fun _ _ f hf => by
      have : Etale f := hf
      exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))
  refine MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @Etale) s g inferInstance ?_
  rw [h]
  infer_instance

private lemma exists_mem_range_lift_of_isGaloisCover {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga]
    {ρ : Ga → (X ⟶ X)} (h : IsGaloisCover Ga ρ π) (p : ↥(pullback π π)) :
    ∃ a, p ∈ Set.range ⇑(pullback.lift (ρ a) (𝟙 X) (by rw [h.inv a, Category.id_comp]) :
      X ⟶ pullback π π) := by
  let K := AlgebraicClosure ((pullback π π).residueField p)
  let q : Spec (CommRingCat.of K) ⟶ pullback π π :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑((pullback π π).residueField p) K)) ≫ (pullback π π).fromSpecResidueField p
  obtain ⟨a, ha, -⟩ := h.fibre K (q ≫ pullback.snd π π) (q ≫ pullback.fst π π)
    (by simp only [Category.assoc, pullback.condition])
  let x : ↥(Spec (CommRingCat.of K)) := show PrimeSpectrum K from IsLocalRing.closedPoint K
  refine ⟨a, (q ≫ pullback.snd π π) x, ?_⟩
  have e : (q ≫ pullback.snd π π) ≫ pullback.lift (ρ a) (𝟙 X) (by rw [h.inv a, Category.id_comp]) = q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact ha
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  have hq : q x = p := by
    have hx : q x ∈ Set.range ((pullback π π).fromSpecResidueField p) :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rw [Scheme.range_fromSpecResidueField] at hx
    exact Set.mem_singleton_iff.mp hx
  calc _ = ((q ≫ pullback.snd π π) ≫ pullback.lift (ρ a) (𝟙 X)
        (by rw [h.inv a, Category.id_comp])) x := (Scheme.Hom.comp_apply _ _ _).symm
    _ = q x := by rw [e]
    _ = p := hq

theorem locTransitive_of_isGaloisCover {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga]
    {ρ : Ga → (X ⟶ X)} (h : IsGaloisCover Ga ρ π) : LocTransitive ρ π := by
  intro Z g₁ g₂ hg z
  let φ : Z ⟶ pullback π π := pullback.lift g₁ g₂ hg
  obtain ⟨c, hc⟩ := exists_mem_range_lift_of_isGaloisCover h (φ z)
  let gr : X ⟶ pullback π π := pullback.lift (ρ c) (𝟙 X) (by rw [h.inv c, Category.id_comp])
  have : Etale π := h.etale
  have : IsOpenImmersion gr :=
    isOpenImmersion_of_section_of_etale' gr (pullback.snd π π) (pullback.lift_snd _ _ _)
  let U : Z.Opens := φ ⁻¹ᵁ gr.opensRange
  have hr : Set.range (U.ι ≫ φ) ⊆ Set.range gr := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact v.2
  let lw := IsOpenImmersion.lift gr (U.ι ≫ φ) hr
  have hw : lw ≫ gr = U.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨c, U.toScheme, U.ι, inferInstance, ⟨z, hc⟩, rfl, ?_⟩
  have h1 : U.ι ≫ g₁ = lw ≫ ρ c := by
    have e := congrArg (· ≫ pullback.fst π π) hw
    simp only [Category.assoc, gr, φ, pullback.lift_fst] at e
    exact e.symm
  have h2 : U.ι ≫ g₂ = lw := by
    have e := congrArg (· ≫ pullback.snd π π) hw
    simp only [Category.assoc, gr, φ, pullback.lift_snd, Category.comp_id] at e
    exact e.symm
  rw [h1, h2]

theorem exists_descent_of_isGaloisCover :
    ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (L : LB X), IsGaloisCover Ga ρ π → L.IsLB → ∀ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a)))) → ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  intro X Y π Ga _ ρ L hG hL u hu hc
  have : Finite Ga := hG.finite
  have : IsFinite π := hG.fin
  have : Etale π := hG.etale
  have : Surjective π := hG.onto
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ ρ c := by
    intro k _ _ r a b hab
    obtain ⟨d, -, hd⟩ := hG.fibre k r (r ≫ ρ a) (by rw [Category.assoc, hG.inv])
    exact (hd a rfl).trans (hd b hab.symm).symm
  exact exists_descent_of_galois hL hG.one (fun a c => (hG.mul a c).symm) hG.inv
    (locTransitive_of_isGaloisCover hG) hfree hu hc

end GlobalTheory.LinDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeAndRelDimOfOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem of_isPullback_cover (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {S X : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {Z : I → Scheme.{0}} {p : X ⟶ S}
    {q : ∀ i, Z i ⟶ (U i).toScheme} {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι)
    (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  have hr := (isPullback_morphismRestrict p (U i)).flip
  rw [← IsPullback.isoIsPullback_hom_snd _ _ hr (h i)]
  exact (MorphismProperty.cancel_left_of_respectsIso Q _ _).2 (hq i)

theorem isCommMonObj_of_cover {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    [GrpObj A] {G : ∀ i, Over (U i).toScheme} [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}
    (h : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (hc : ∀ i, IsCommMonObj (G i)) : IsCommMonObj A := by
  refine (isCommMonObj_iff_isMulCommutative A).2 fun T => ⟨⟨fun x y => ?_⟩⟩
  refine over_ext hU fun i T' r => ?_
  have := hc i
  rw [MonObj.comp_mul, MonObj.comp_mul]
  obtain ⟨a, ha⟩ := exists_lift (h i).1 (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift (h i).1 (r ≫ y)
  ext1
  rw [(h i).2 T' a b _ _ ha hb, (h i).2 T' b a _ _ hb ha, mul_comm a b]

theorem isAbelianScheme_and_relDim_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ((∀ i, IsAbelianScheme (G i)) → IsAbelianScheme A) ∧ ∀ g : ℕ, (∀ i, SmoothOfRelativeDimension g (G i).hom) → SmoothOfRelativeDimension g A.hom := by
  intro S I U A _ G _ ψ hU h
  refine ⟨fun hab => ?_, fun g hg => ?_⟩
  · constructor
    · exact isCommMonObj_of_cover hU h fun i => (hab i).comm
    · exact @of_isPullback_cover @Smooth (HasRingHomProperty.instIsZariskiLocalAtTarget @Smooth) _ _ _ _ hU _ _ _ _
        (fun i => (h i).1) fun i => (hab i).smooth
    · exact of_isPullback_cover @IsProper hU (fun i => (h i).1) fun i => (hab i).proper
    · refine ⟨?_⟩
      exact of_isPullback_cover (geometrically (ConnectedSpace ·)) hU (fun i => (h i).1)
        fun i => (hab i).geomConnected.geometrically_connectedSpace
  · exact @of_isPullback_cover (@SmoothOfRelativeDimension g)
      (HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension g)) _ _ _ _ hU _ _ _ _
      (fun i => (h i).1) hg

end GlobalTheory.CoverGlue
end

