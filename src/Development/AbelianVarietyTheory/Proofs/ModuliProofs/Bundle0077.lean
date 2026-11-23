module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedPartialLineBundles
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PartialBundleGlue

theorem iso_isGen_iff {X : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) :
    w.IsGen ↔ ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a → x ∈ M.U a' → x ∈ L.U b → x ∈ L.U b' →
      gm (𝟙 X) x (M.U a ⊓ L.U b) (w.s (a, b)) =
        gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
          gm (𝟙 X) x (M.U a' ⊓ L.U b') (w.s (a', b')) := by
  have key : ∀ (x : X) (a a' : M.ι) (b b' : L.ι), x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b') →
      gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b')) ((LB.div M L).g (a, b) (a', b')) =
        gm (𝟙 X) x (M.U a ⊓ M.U a') (M.g a a') * (gm (𝟙 X) x (L.U b ⊓ L.U b') (L.g b b'))⁻¹ := by
    intro x a a' b b' hm
    show gm (𝟙 X) x _ (res _ (M.g a a') * (res _ (L.g b b'))⁻¹) = _
    rw [map_mul, map_inv, gm_res (𝟙 X) x _ hm, gm_res (𝟙 X) x _ hm]
  constructor
  · intro h x a a' b b' ha ha' hb hb'
    have hm : x ∈ M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b') := ⟨⟨ha, hb⟩, ha', hb'⟩
    have := congrArg (gm (𝟙 X) x (M.U a ⊓ L.U b ⊓ (M.U a' ⊓ L.U b'))) (h (a, b) (a', b'))
    rw [← key x a a' b b' hm]
    exact (gm_res (𝟙 X) x _ hm _).symm.trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 X) x _ hm _))))
  · rintro h ⟨a, b⟩ ⟨a', b'⟩
    apply unit_ext
    intro x hx
    have := h x a a' b b' hx.1.1 hx.2.1 hx.1.2 hx.2.2
    rw [← key x a a' b b' hx] at this
    exact (gm_res _ x _ hx _).trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

theorem pull_isGen_of {X S : Scheme.{0}} {L : LB X} {e : S ⟶ X} (r : (L.pull e).Gen)
    (h : ∀ (x : S) (a b : L.ι), e x ∈ L.U a → e x ∈ L.U b →
      gm (𝟙 S) x ((L.pull e).U fun _ => a) (r.s fun _ => a) =
        gm e x (L.U a ⊓ L.U b) (L.g a b) * gm (𝟙 S) x ((L.pull e).U fun _ => b) (r.s fun _ => b)) :
    r.IsGen := by
  intro J J'
  obtain ⟨a, rfl⟩ : ∃ a, J = fun _ => a := ⟨J PUnit.unit, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b, J' = fun _ => b := ⟨J' PUnit.unit, rfl⟩
  apply unit_ext
  intro x hx
  have ha : e x ∈ L.U a := mem_pull.1 hx.1
  have hb : e x ∈ L.U b := mem_pull.1 hx.2
  have eg : gm (𝟙 S) x ((L.pull e).U (fun _ => a) ⊓ (L.pull e).U (fun _ => b))
      ((L.pull e).g (fun _ => a) (fun _ => b)) = gm e x (L.U a ⊓ L.U b) (L.g a b) := by
    show gm (𝟙 S) x _ (∏ _k : PUnit, (res _ (pullU e _ (L.g a b))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res (𝟙 S) x _ hx _).trans (gm_pull (𝟙 S) e x (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)
  rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, eg]
  exact h x a b ha hb

theorem exists_glue : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (I : Type) (U : I → S.Opens) (M : I → LB X), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → iSup U = ⊤ → (∀ i, ⨆ a, (M i).U a = p ⁻¹ᵁ U i) → (∀ i, ∀ (a : (M i).ι) (x : X), x ∈ (M i).U a → gm (𝟙 X) x ((M i).U a ⊓ (M i).U a) ((M i).g a a) = 1) → (∀ i, ∃ r : ((M i).pull e).Gen, r.IsGen) → (∀ i j, LBIso (M i) (M j)) → ∃ L : LB X, L.IsLB ∧ (∃ r : (L.pull e).Gen, r.IsGen) ∧ ∀ i, LBIso (M i) L := by
  intro X S p e I U M hep hrig hU hM hself hr hiso
  choose r hr using hr
  choose w hw hn using fun i j => _root_.GlobalTheory.BundleNormalise.exists_iso_normalised X S p e (U i) (U j) (M i) (M j) (r i) (r j) hep (hM i) (hM j)
    (hr i) (hr j) (hiso j i)
  have hc : ∀ i j k (y : X) a b c, y ∈ (M i).U a → y ∈ (M j).U b → y ∈ (M k).U c →
      gm (𝟙 X) y ((M i).U a ⊓ (M j).U b) ((w i j).s (a, b)) *
        gm (𝟙 X) y ((M j).U b ⊓ (M k).U c) ((w j k).s (b, c)) =
        gm (𝟙 X) y ((M i).U a ⊓ (M k).U c) ((w i k).s (a, c)) := by
    intro i j k
    refine _root_.GlobalTheory.PartialCocycle.cocycle_of_rigid X S p e (U i) (U j) (U k) (M i) (M j) (M k) (w i j) (w j k) (w i k) hep hrig
      (hM i) (hM j) (hM k) (hw i j) (hw j k) (hw i k) ?_
    intro x a b c ha hb hc
    have h₁ := hn i j x a b ha hb
    have h₂ := hn j k x b c hb hc
    have h₃ := hn i k x a c ha hc
    rw [h₁, h₂, ← _root_.mul_assoc] at h₃
    exact mul_right_cancel h₃
  let L : LB X := ⟨Σ i, (M i).ι, fun q => (M q.1).U q.2, fun q q' => (w q.1 q'.1).s (q.2, q'.2)⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ⟨⟨fun J => (r (J PUnit.unit).1).s fun _ => (J PUnit.unit).2⟩, ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p x ∈ iSup U by rw [hU]; trivial)
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ a, (M i).U a by rw [hM i]; exact hi)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, a⟩, ha⟩
  · rintro ⟨i, a⟩
    apply unit_ext
    intro x hx
    rw [map_one]
    exact (gm_res (𝟙 X) x _ hx _).trans (mul_eq_left.1 (hc i i i x a a a hx hx hx))
  · rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    apply unit_ext
    intro x hx
    rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    exact hc i j k x a b c hx.1.1 hx.1.2 hx.2
  · apply pull_isGen_of
    rintro x ⟨i, a⟩ ⟨j, b⟩ ha hb
    exact hn i j x a b ha hb
  · intro i
    refine ⟨⟨fun q => (w q.1.1 i).s (q.1.2, q.2)⟩, (iso_isGen_iff _).2 ?_⟩
    rintro x ⟨j, b⟩ ⟨j', b'⟩ a a' hb hb' ha ha'
    have h₁ := hc j j' i x b b' a hb hb' ha
    have h₂ := (iso_isGen_iff (w j' i)).1 (hw j' i) x b' b' a a' hb' hb' ha ha'
    rw [hself j' b' x hb', _root_.one_mul] at h₂
    rw [h₂, ← _root_.mul_assoc] at h₁
    exact h₁.symm

end GlobalTheory.PartialBundleGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.RigidLinearisation

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      (val u r z J * (val u' r z J)⁻¹).val = gs r z ⊤ c := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, fun Z r z J hJ => ?_⟩
  rw [← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res r z le trivial _)).symm.trans (gs_unit r z ⊤ trivial _).symm

theorem gs_one {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) : gs f y ⊤ (1 : Γ(X, ⊤)) = 1 := by
  rw [gs_eq _ y ⊤ trivial, map_one, map_one]

theorem gs_pow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (c : Γ(X, ⊤)) (n : ℕ) : gs f y ⊤ (c ^ n) = gs f y ⊤ c ^ n := by
  rw [gs_eq _ y ⊤ trivial, gs_eq _ y ⊤ trivial, map_pow, map_pow]

theorem exists_good' {X Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem val_eq_of_rigid {X Y S : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    (e : S ⟶ Y) (he : ∀ c : Γ(Y, ⊤), (e.app ⊤).hom c = 1 → c = 1)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨c, hc⟩ := exists_ratio hM hF hu hu'
  have c1 : c = 1 := he c (fn_ext (V := ⊤) fun y _ => by
    obtain ⟨I, hI⟩ := exists_good' hM y
    have := hc _ e y I hI
    rw [h y I hI, mul_inv_cancel] at this
    refine (gs_pull (𝟙 S) e y ⊤ trivial c).trans ?_
    rw [Category.id_comp, ← this]
    exact (gs_one (𝟙 S) y).symm)
  have := hc Z r z J hJ
  rw [c1, gs_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem exists_gen_of_iso {Y : Scheme.{0}} (L : LB Y) (τ : Y ⟶ Y) (h : LBIso L (L.pull τ)) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), t.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j ≤ (L.pull τ).U (fun _ => j 1) ⊓ L.U (j 0) :=
    fun j y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy 1), Set.mem_iInter.1 hy 0⟩
  refine ⟨⟨fun j => (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  have v : ∀ j : Fin 2 → L.ι, y ∈ LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j →
      gm (𝟙 Y) y (LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j) (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹ =
        (gw w (𝟙 Y) y (j 1) (j 0))⁻¹ := fun j hj =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res (𝟙 Y) y (le j) hj _))
  refine (v j hj).trans (Eq.trans ?_ (congrArg (_ * ·) (v j' hj')).symm)
  rw [hp Y (𝟙 Y) y (j 1) (j' 1) (j 0) (j' 0) (Set.mem_iInter.1 hj 1) (Set.mem_iInter.1 hj' 1)
    (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0), trF, Fin.prod_univ_two]
  show _ = gm (𝟙 Y ≫ 𝟙 Y) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 Y ≫ τ) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) * _
  rw [Category.id_comp (𝟙 Y), zpow_one, zpow_neg_one, mul_inv, mul_inv, inv_inv, mul_comm (_⁻¹) (gm (𝟙 Y) y _ _)]

theorem exists_normalised {X Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (p : Y ⟶ X) (e : X ⟶ Y) (he : e ≫ p = 𝟙 X)
    (ρ : X ⟶ X) (τ : Y ⟶ Y) (hτ : e ≫ τ = ρ ≫ e) (r : (L.pull e).Gen) (hr : r.IsGen) (h : LBIso L (L.pull τ)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (b : Z ⟶ X) (z : Z) (J), Good L z J →
        val u (b ≫ e) z J = val r b z J * (val r (b ≫ ρ) z J)⁻¹ := by
  obtain ⟨t, ht⟩ := exists_gen_of_iso L τ h
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := ![𝟙 Y, τ]) (ε' := ![1, -1]) (fun U _ k => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fintype.prod_unique,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.assoc, hτ, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (p ≫ e))))
      (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ r p) (LB.invGen L _ _ (LB.pullGen L _ _ r (p ≫ ρ)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _))))
  refine ⟨u, hu, fun Z b z J hJ => ?_⟩
  have e₁ : (b ≫ e) ≫ p = b := by rw [Category.assoc, he, Category.comp_id]
  rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ, val_pull hJ,
    ← Category.assoc (b ≫ e) p e, ← Category.assoc (b ≫ e) p ρ, e₁, mul_inv_cancel, _root_.one_mul]

theorem exists_const {k : Type} [Field k] [IsAlgClosed k] {F : Scheme.{0}} [IsIntegral F] (q : F ⟶ Sp k)
    (c : Γ(F, ⊤)) {n : ℕ} (hn : n ≠ 0) (hc : c ^ n = 1) : ∃ a : Γ(Sp k, ⊤), (q.app ⊤).hom a = c := by
  let f : k →+* Γ(F, ⊤) := (q.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hs : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Splits := IsAlgClosed.splits _
  have hm : (Polynomial.X ^ n - Polynomial.C 1 : Polynomial k).Monic := Polynomial.monic_X_pow_sub_C _ hn
  have e := congrArg (Polynomial.eval₂ f c) (hs.eq_prod_roots_of_monic hm)
  rw [Polynomial.eval₂_multiset_prod, Multiset.map_map] at e
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, map_one, hc, sub_self,
    Polynomial.eval₂_one] at e
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 e.symm)
  simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at ha
  exact ⟨_, (sub_eq_zero.1 ha).symm⟩

theorem exists_linearisation : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left) (ρ : Γ →* Aut X) (τ : Γ →* Aut P.left) (L : LB P.left), e ≫ P.hom = 𝟙 X → GeometricallyIntegral P.hom → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → (∀ g, (τ g).asIso.hom ≫ P.hom = P.hom ≫ (ρ g).asIso.hom ∧ e ≫ (τ g).asIso.hom = (ρ g).asIso.hom ≫ e) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst P.hom x ≫ (τ g).asIso.hom = pullback.fst P.hom x) → L.IsLB → (∃ r : (L.pull e).Gen, r.IsGen) → (∀ g, LBIso L (L.pull (τ g).asIso.hom)) → ∃ u : ∀ g, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 P.left, (τ g).asIso.hom] ![1, -1]), (∀ g, (u g).IsGen) ∧ (∀ g h, LB.Gen.Corr L _ _ _ _ (u (h * g)) (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).asIso.hom))) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ P.left) g, y ≫ (τ g).asIso.hom = y → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u g) y) (LB.oneGen L) := by
  intro Γ _ _ X P e ρ τ L he hgi hrig hcomm hfix hL ⟨r, hr⟩ hiso
  choose u hu hn using fun g => exists_normalised hL P.hom e he (ρ g).asIso.hom (τ g).asIso.hom (hcomm g).2 r hr (hiso g)
  have rig : ∀ c : Γ(P.left, ⊤), (e.app ⊤).hom c = 1 → c = 1 := fun c hc =>
    hrig ⊤ c le_top (by
      have : e.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ le_top = e.app ⊤ := (e.app_eq_appLE (U := ⊤)).symm
      rw [this]; exact hc)
  have τm : ∀ g h, (τ (h * g)).asIso.hom = (τ g).asIso.hom ≫ (τ h).asIso.hom := fun g h => by rw [map_mul]; rfl
  have ρm : ∀ g h, (ρ (h * g)).asIso.hom = (ρ g).asIso.hom ≫ (ρ h).asIso.hom := fun g h => by rw [map_mul]; rfl
  have coc : ∀ g h (Z : Scheme.{0}) (s : Z ⟶ P.left) (z : Z) (J), Good L z J → val (u (h * g)) s z J =
      val (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).asIso.hom)) s z J := fun g h =>
    val_eq_of_rigid hL (fun U _ k => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, τm, Category.comp_id]
        simp) e rig (hu _)
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hu g) (DVR.pullGen_isGen _ _ _ _ (hu h) _)) (fun y J hJ => by
        have a₁ := hn (h * g) X (𝟙 X) y J hJ
        have a₂ := hn g X (𝟙 X) y J hJ
        have a₃ := hn h X (ρ g).asIso.hom y J hJ
        simp only [Category.id_comp] at a₁ a₂
        rw [val_mul hJ, val_pull hJ, (hcomm g).2, a₁, a₂, a₃, ρm]
        simp)
  refine ⟨u, hu, fun g h => corr_of_val hL fun y J hJ => coc g h _ _ y J hJ, fun k _ _ y g hy => ?_⟩
  have hx : (y ≫ P.hom) ≫ (ρ g).asIso.hom = y ≫ P.hom := by
    rw [Category.assoc, ← (hcomm g).1, ← Category.assoc, hy]
  have hf := hfix k _ g hx
  have : IsIntegral (pullback P.hom (y ≫ P.hom)) :=
    hgi.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  obtain ⟨c, hc⟩ := exists_ratio hL (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ k => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hf, Category.comp_id]
      simp)
    (DVR.pullGen_isGen _ _ _ _ (hu g) (pullback.fst P.hom (y ≫ P.hom))) (u' := LB.oneGen L)
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.one_mul _)).symm)
  have hc' : ∀ (Z : Scheme.{0}) (s : Z ⟶ pullback P.hom (y ≫ P.hom)) (z : Z) (J), Good L z J →
      (val (u g) (s ≫ pullback.fst _ _) z J).val = gs s z ⊤ c := fun Z s z J hJ => by
    rw [← hc Z s z J hJ, val_pull hJ, val_one, inv_one, _root_.mul_one]
  have pw : ∀ (Z : Scheme.{0}) (s : Z ⟶ P.left) (z : Z) (J), Good L z J → s ≫ (τ g).asIso.hom = s →
      val (u g) s z J ^ orderOf g = 1 := fun Z s z J hJ hs => by
    have one : val (u 1) s z J = 1 := by
      have := coc 1 1 Z s z J hJ
      rw [val_mul hJ, val_pull hJ, _root_.mul_one, show s ≫ (τ 1).asIso.hom = s by rw [map_one]; exact Category.comp_id s] at this
      exact mul_eq_left.1 this.symm
    have all : ∀ n : ℕ, val (u (g ^ n)) s z J = val (u g) s z J ^ n := fun n => by
      induction n with
      | zero => rw [pow_zero, pow_zero, one]
      | succ n ih => rw [pow_succ, coc g (g ^ n) Z s z J hJ, val_mul hJ, val_pull hJ, hs, ih, pow_succ']
    rw [← all, pow_orderOf_eq_one, one]
  have cn : c ^ orderOf g = 1 := fn_ext fun z _ => by
    obtain ⟨J, hJ⟩ := exists_good' hL z
    rw [gs_pow, gs_one, ← hc' _ _ z J hJ, ← Units.val_pow_eq_pow_val,
      pw _ _ z J hJ (by rw [Category.assoc, hf]), Units.val_one]
  obtain ⟨a, ha⟩ := exists_const (pullback.snd P.hom (y ≫ P.hom)) c (orderOf_pos g).ne' cn
  have sec : ∀ (s : Sp k ⟶ pullback P.hom (y ≫ P.hom)) (z : Sp k), s ≫ pullback.snd _ _ = 𝟙 _ →
      gs s z ⊤ c = gs (𝟙 _) z ⊤ a := fun s z hs => by
    rw [← ha, ← hs]
    exact gs_pull s _ z ⊤ trivial a
  refine corr_of_val hL fun z J hJ => Units.ext ?_
  have b₁ := hc' _ (pullback.lift y (𝟙 _) (Category.id_comp _).symm) z J hJ
  have b₂ := hc' _ (pullback.lift ((y ≫ P.hom) ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp])) z J hJ
  rw [sec _ z (pullback.lift_snd _ _ _), pullback.lift_fst] at b₁ b₂
  rw [hn g _ _ z J hJ, hx, mul_inv_cancel] at b₂
  rw [val_pull hJ, Category.id_comp, val_one, b₁, b₂]

end GlobalTheory.RigidLinearisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRetractionNearOfUniquePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem exists_smul_mem_range_of_unique_point (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.FormallyUnramified R B] (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K)
    (y : B →+* K) (hy : y.comp (algebraMap R B) = x) (hu : ∀ z : B →+* K, z.comp (algebraMap R B) = x → z = y) :
    ∃ f : R, f ∉ RingHom.ker x ∧ ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b := by
  let _ : Algebra R K := x.toAlgebra
  let yA : B →ₐ[R] K := { y with commutes' := fun r => RingHom.congr_fun hy r }
  let φ : K ⊗[R] B →ₐ[K] K :=
    Algebra.TensorProduct.lift (Algebra.ofId K K) yA (fun _ _ => Commute.all _ _)
  have hall : ∀ ψ : K ⊗[R] B →ₐ[K] K, ∀ (a : K) (b : B), ψ (a ⊗ₜ[R] b) = a * y b := by
    intro ψ a b
    have hz : ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hu
      ext r
      exact ((ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    have h1 : ψ ((1 : K) ⊗ₜ[R] b) = y b := by
      have := RingHom.congr_fun hz b
      simpa using this
    have h2 : a ⊗ₜ[R] b = a • ((1 : K) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul']
      simp
    rw [h2, map_smul, h1, _root_.smul_eq_mul]
  have huniq : ∀ ψ : K ⊗[R] B →ₐ[K] K, ψ = φ := by
    intro ψ
    refine AlgHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [hall ψ, hall φ]
    | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht]
  have hsurj := algebraMap_surjective_of_unramified_of_unique_point K (K ⊗[R] B) φ huniq
  set N : Submodule R B := LinearMap.range (Algebra.linearMap R B) with hN
  have hone : N.mkQ (1 : B) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨1, by simp⟩
  have hzero : ∀ t : K ⊗[R] (B ⧸ N), t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rfl
    | tmul a c =>
      obtain ⟨b, rfl⟩ := N.mkQ_surjective c
      obtain ⟨c', hc'⟩ := hsurj (a ⊗ₜ[R] b)
      rw [← LinearMap.lTensor_tmul, ← hc', Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul, hone,
        TensorProduct.tmul_zero]
    | add s t hs ht => rw [hs, ht, add_zero]
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hns : p ∉ Module.support R (B ⧸ N) := by
    intro h
    have hnt := nontrivial_tensor_of_mem_support R (B ⧸ N) K p rfl h
    obtain ⟨s, t, hst⟩ := hnt.exists_pair_ne
    exact hst ((hzero s).trans (hzero t).symm)
  rw [Module.mem_support_iff_of_finite] at hns
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.mp hns
  refine ⟨f, hfp, fun b => ?_⟩
  have hfb : f • N.mkQ b = 0 := Module.mem_annihilator.mp hf _
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hfb
  obtain ⟨a, ha⟩ := hfb
  exact ⟨a, by rw [← Algebra.smul_def, ← ha, Algebra.linearMap_apply]⟩

theorem exists_retraction_away (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) (f : R)
    (hf : ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b) :
    ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f := by
  choose a ha using hf
  set g : Localization.Away f := IsLocalization.Away.invSelf f with hg
  have hfg : loc f f * g = 1 := IsLocalization.Away.mul_invSelf f
  have ha_zero : a 0 = 0 := hinj (by simp only [ha, MulZeroClass.mul_zero, map_zero])
  have ha_one : a 1 = f := hinj (by simp only [ha, _root_.mul_one])
  have ha_add : ∀ b c, a (b + c) = a b + a c := fun b c => hinj (by simp only [ha, map_add (f := _)]; ring)
  have ha_mul : ∀ b c, f * a (b * c) = a b * a c := fun b c => hinj (by simp only [ha, map_mul]; ring)
  have ha_alg : ∀ c, a (algebraMap R B c) = f * c := fun c => hinj (by simp only [ha, map_mul])
  have h_one : loc f (a 1) * g = 1 := by rw [ha_one, hfg]
  have h_mul : ∀ b c, loc f (a (b * c)) * g = loc f (a b) * g * (loc f (a c) * g) := by
    intro b c
    have h := congrArg (loc f) (ha_mul b c)
    rw [map_mul, map_mul] at h
    linear_combination (-(loc f (a (b * c)) * g)) * hfg + g * g * h
  have h_zero : loc f (a 0) * g = 0 := by rw [ha_zero, map_zero, MulZeroClass.zero_mul]
  have h_add : ∀ b c, loc f (a (b + c)) * g = loc f (a b) * g + loc f (a c) * g := by
    intro b c
    rw [ha_add, map_add (f := _), add_mul]
  let r : B →+* Localization.Away f :=
    { toFun := fun b => loc f (a b) * g
      map_one' := h_one
      map_mul' := h_mul
      map_zero' := h_zero
      map_add' := h_add }
  refine ⟨r, ?_⟩
  · ext c
    show loc f (a (algebraMap R B c)) * g = loc f c
    rw [ha_alg, map_mul]
    linear_combination (loc f c) * hfg

theorem exists_retraction_near_of_unique_point :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.FormallyUnramified R B] (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K), RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f ∧ ∀ (T : Type) [CommRing T] (x : Localization.Away f →+* T) (y : B →+* T), y.comp (algebraMap R B) = x.comp (loc f) → y = x.comp r := by
  intro R B _ _ _ _ _ P hD hP q₀ hq₀
  obtain ⟨K, _, _, x, hker, y, hy, hu⟩ := hP q₀ hq₀
  obtain ⟨f, hfk, hfB⟩ := exists_smul_mem_range_of_unique_point R B K x y hy hu
  have hinj : Function.Injective (algebraMap R B) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    refine hD a fun p hp _ => ?_
    obtain ⟨K', _, _, x', hker', y', hy', -⟩ := hP p hp
    rw [← hker', RingHom.mem_ker, ← hy', RingHom.comp_apply, ha, map_zero]
  obtain ⟨r, hr⟩ := exists_retraction_away R B hinj f hfB
  refine ⟨f, hker ▸ hfk, r, hr, fun T _ x' y' hxy => ?_⟩
  ext b
  obtain ⟨a, ha⟩ := hfB b
  have h1 : y' (algebraMap R B a) = x' (loc f a) := RingHom.congr_fun hxy a
  have h2 : y' (algebraMap R B f) = x' (loc f f) := RingHom.congr_fun hxy f
  have h3 : loc f a = loc f f * r b := by
    rw [← RingHom.congr_fun hr a, ← RingHom.congr_fun hr f, RingHom.comp_apply, RingHom.comp_apply, ha, map_mul]
  have hU : IsUnit (x' (loc f f)) := (IsLocalization.Away.algebraMap_isUnit f).map x'
  apply hU.mul_left_cancel
  rw [RingHom.comp_apply, ← map_mul, ← h3, ← h1, ha, map_mul, h2]

end GlobalTheory.ZM.NearBuild
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def RigAlong {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (ε : G' ⟶ G) (L : RigLB G) (L' : RigLB G') (w : LB.Iso L'.L (L.L.pull ε.left)) : Prop :=
  w.IsGen ∧ PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig (𝟙 _)

variable {R : Type} [CommRing R] [IsDomain R]

def SameUnif {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G' G : Over (Sp R)}
    [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (ε : G' ≅ G)
    (U : UnifPre I D A G) (U' : UnifPre I D A G') : Prop :=
  U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom ∧
    ∃ w : LB.Iso U'.LG.L (U.LG.L.pull ε.hom.left), RigAlong ε.hom U.LG U'.LG w ∧ ∀ e : ℕ,
      (U'.gt e).q = (Over.pullback (thick R I e)).map ε.hom ≫ (U.gt e).q ∧
      (∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ ((U'.gt e).t χ)
        (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (thick R I e)).map ε.hom).left)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
        (jL' : U'.LG.L.ι), (U'.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM →
        ε.hom.left ((fstG I e G').left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
        gw (U'.w e) r z jM (fun _ => jL') =
          gw (U.w e) (r ≫ ((Over.pullback (thick R I e)).map ε.hom).left) z jM (fun _ => jL) *
            gw w (r ≫ (fstG I e G').left) z jL jL'

def IsIdPull {D : DegPre R} (hD : IsPullDeg (RingHom.id R) D D) : Prop :=
  (∀ x, hD.xe x = x) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ ∧
    ∀ (Y : Scheme.{0}) (f : Y ⟶ D.P.A.left) (y : Y) (j k : D.P.L.ι), f y ∈ D.P.L.U j → f y ∈ D.P.L.U k →
      gw hD.w f y j k = gm f y _ (D.P.L.g j k)

theorem rigAlong_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) :
    RigAlong (𝟙 G) L L (isoPullId (idIso L.L) rfl) := by
  have he : eSec G ≫ (𝟙 G : G ⟶ G).left = 𝟙 _ ≫ eSec G := by simp
  exact ⟨(isGen_iff _).2 (isoPullId_pgen (idIso_isGen L.isLB) rfl),
    (maps_iff _ _ (fun _ => eSec G) _ L.rig L.rig (𝟙 _) _ (rigPull_le _ _ he L.L) (fun _ => rfl)).1
      (isoPullId_maps (idIso_maps L) rfl rfl he)⟩

end GlobalTheory.TorsionFormCompare
end
end

