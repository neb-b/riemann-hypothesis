module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeRTensorOfForallDual
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KuennethOne

section General

open TopologicalSpace TensorProduct

theorem lid_rTensor_lTensor {R C A B : Type} [CommRing R] [AddCommGroup C] [Module R C]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (l : C →ₗ[R] R) (f : B →ₗ[R] A)
    (w : C ⊗[R] B) : TensorProduct.lid R A (l.rTensor A (f.lTensor C w)) =
      f (TensorProduct.lid R B (l.rTensor B w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem apply_lid_rTensor {R C B : Type} [CommRing R] [AddCommGroup C] [Module R C]
    [AddCommGroup B] [Module R B] (l : C →ₗ[R] R) (f : B →ₗ[R] R) (w : C ⊗[R] B) :
    f (TensorProduct.lid R B (l.rTensor B w)) = l (TensorProduct.rid R C (f.lTensor C w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

variable {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
  (H : IsPullback p q iX iY) {I : Type} {V : I → Z.Opens} {φ : ∀ a b, Γ(Z, V a ⊓ V b)}

include H

theorem isAffineOpen_prod [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
  have : IsAffine _ := isAffineOpen_top S
  have : IsAffine _ := hU
  have : IsAffine _ := hW
  exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top
    rfl).isoPullback.hom

theorem exists_splits_preimage [IsAffine S] (hR : IsField Γ(S, ⊤)) [CompactSpace X]
    (hX : ∀ U U' : X.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hY : ∀ U U' : Y.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hiY : Function.Surjective iY.appTop.hom)
    {y : S ⟶ Y} (hy : y ≫ iY = 𝟙 S) {s : X ⟶ Z} (hs : s ≫ p = 𝟙 X) (hs' : s ≫ q = iX ≫ y)
    (W₀ : Y.affineOpens) (hW₀ : ⊤ ≤ y ⁻¹ᵁ W₀.1)
    (hV : ⨆ a, V a = ⊤) (hφ : IsCocycle V φ) (ρ : ∀ a, Γ(X, s ⁻¹ᵁ V a))
    (hρ : ∀ a b, (s.app (V a ⊓ V b)).hom (φ a b) =
      rs (s.preimage_mono inf_le_left) (ρ a) - rs (s.preimage_mono inf_le_right) (ρ b))
    (W : Y.affineOpens) : ∃ τ, Splits V φ (q ⁻¹ᵁ W.1) τ := by
  obtain ⟨I₀, hI₀, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact ((⊤ : X.Opens) : Set X) by simpa using isCompact_univ)
  have := hI₀.to_subtype
  let U : I₀ → X.Opens := fun i => i.1.1
  have hU : ∀ i, IsAffineOpen (U i) := fun i => i.1.2
  have hUtop : iSup U = ⊤ := by rw [e, iSup_subtype]
  let U₂ : I₀ × I₀ → X.Opens := fun k => U k.1 ⊓ U k.2
  have hU₂ : ∀ k, IsAffineOpen (U₂ k) := fun k => hX _ _ (hU _) (hU _)
  have l1 : ∀ k : I₀ × I₀, p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.1 := fun k => p.preimage_mono inf_le_left
  have l2 : ∀ k : I₀ × I₀, p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.2 := fun k => p.preimage_mono inf_le_right
  choose σ hσ using fun (i : I₀) (j : Y.affineOpens) =>
    exists_splits_of_isAffineOpen hV hφ (isAffineOpen_prod H (hU i) j.2)
  choose c hc using fun (j : Y.affineOpens) (k : I₀ × I₀) =>
    exists_isDiff hV (hσ k.1 j) (hσ k.2 j) (P := p ⁻¹ᵁ U₂ k ⊓ q ⁻¹ᵁ j.1)
      (inf_le_inf_right _ (l1 k)) (inf_le_inf_right _ (l2 k))
  choose z hz using fun j : Y.affineOpens => MM_surj H hU₂ j.2 (c j)
  have hcompat : ∀ (j k : Y.affineOpens), ∃ w,
      (rsA iY (inf_le_left : j.1 ⊓ k.1 ≤ j.1)).toLinearMap.lTensor _ (z j) -
        (rsA iY inf_le_right).toLinearMap.lTensor _ (z k) - (dlt iX U).rTensor _ w = 0 := by
    intro j k
    have hW' := hY _ _ j.2 k.2
    have m1 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1 := q.preimage_mono inf_le_left
    have m2 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1 := q.preimage_mono inf_le_right
    choose d hd using fun i : I₀ => exists_isDiff hV (hσ i j) (hσ i k)
      (P := p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1)) (inf_le_inf_left _ m1) (inf_le_inf_left _ m2)
    obtain ⟨w, hw⟩ := MM_surj H hU hW' d
    refine ⟨w, MM_inj H hU₂ hW' _ fun m => ?_⟩
    rw [map_sub, map_sub, MM_lTensor, MM_lTensor, MM_dlt]
    have a1 := congrArg (rs (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m1)) (hz j m)
    have a2 := congrArg (rs (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m2)) (hz k m)
    have a3 := congrArg (rs (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l1 m))) (hw m.1)
    have a4 := congrArg (rs (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l2 m))) (hw m.2)
    rw [rs_MM] at a1 a2 a3 a4
    rw [a1, a2, a3, a4]
    refine loc V (by rw [hV]; exact le_top) _ _ fun a => ?_
    have b1 := hc j m a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_left _ m1)) inf_le_right
    have b2 := hc k m a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_left _ m2)) inf_le_right
    have b3 := hd m.1 a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_right _ (l1 m))) inf_le_right
    have b4 := hd m.2 a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_right _ (l2 m))) inf_le_right
    simp only [map_sub, map_zero, rs_rs]
    linear_combination b1 - b2 - b3 + b4
  have hN : ∀ (N : X.Opens), N ≤ s ⁻¹ᵁ (p ⁻¹ᵁ N ⊓ q ⁻¹ᵁ W₀.1) := by
    intro N
    rw [s.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hs, hs']
    exact le_inf le_rfl (le_top.trans (iX.preimage_mono hW₀))
  obtain ⟨x, hx⟩ := pull_coboundary hV s ρ hρ (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W₀.1)
    (fun i => σ i W₀) (fun i => hσ i W₀) U (fun i => hN _)
  have hz₀ : TensorProduct.rid _ _ ((evA y hy W₀.1 hW₀).toLinearMap.lTensor _ (z W₀)) =
      dlt iX U x := by
    funext m
    refine (section_MM H hy hs hs' U₂ W₀.1 hW₀ m _ inf_le_left inf_le_right (hN _) (z W₀)).symm.trans ?_
    rw [hz W₀ m]
    exact hx m.1 m.2 _ _ _ _ (hc W₀ m) _ inf_le_left inf_le_right _
  have hl : ∀ l : (∀ k, Fn iX (U₂ k)) →ₗ[Γ(S, ⊤)] Γ(S, ⊤), l ∘ₗ dlt iX U = 0 →
      TensorProduct.lid _ _ (l.rTensor _ (z W)) = 0 := by
    intro l hl
    let b : ∀ j : Y.affineOpens, Fn iY j.1 := fun j => TensorProduct.lid _ _ (l.rTensor _ (z j))
    obtain ⟨β, hβ⟩ := glue ⊤ (fun j : Y.affineOpens => j.1) (fun _ => le_top)
      (iSup_affineOpens_eq_top Y).ge b (by
        intro j k
        obtain ⟨w, hw⟩ := hcompat j k
        have := congrArg (fun t => TensorProduct.lid _ _ (l.rTensor _ t)) hw
        simp only [map_sub, map_zero] at this
        rw [lid_rTensor_lTensor, lid_rTensor_lTensor, ← LinearMap.rTensor_comp_apply, hl] at this
        simp only [LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero, sub_zero] at this
        exact sub_eq_zero.mp this)
    obtain ⟨r, rfl⟩ := hiY β
    have hb : ∀ j : Y.affineOpens, b j = algebraMap Γ(S, ⊤) (Fn iY j.1) r := by
      intro j
      refine (hβ j).symm.trans ?_
      have : iY.appTop = iY.appLE ⊤ ⊤ le_top := iY.app_eq_appLE (U := ⊤)
      rw [this]
      exact rs_appLE iY _ _ r
    have hr : r = 0 := by
      have h1 := apply_lid_rTensor l (evA y hy W₀.1 hW₀).toLinearMap (z W₀)
      rw [hz₀, show l (dlt iX U x) = 0 from LinearMap.congr_fun hl x] at h1
      have h2 : evA y hy W₀.1 hW₀ (b W₀) = 0 := h1
      rwa [hb, AlgHom.commutes] at h2
    have := hb W
    rwa [hr, map_zero] at this
  obtain ⟨w, hw⟩ := mem_range_rTensor_of_forall_dual hR (dlt iX U) (z W) hl
  refine splits_glue (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W.1) (fun i => σ i W) (fun i => hσ i W)
    (fun i => MM H U W.1 i _ inf_le_left inf_le_right w) ?_ _ ?_
  · intro i k a M hi hk ha
    have hM : M ≤ p ⁻¹ᵁ U₂ (i, k) ⊓ q ⁻¹ᵁ W.1 := by
      refine le_inf ?_ (hi.trans inf_le_right)
      rw [p.preimage_inf]
      exact le_inf (hi.trans inf_le_left) (hk.trans inf_le_left)
    have b1 := hc W (i, k) a M hM ha
    rw [← hz W (i, k), rs_MM, ← hw, MM_dlt] at b1
    rw [rs_MM, rs_MM]
    exact b1.symm
  · rw [← iSup_inf_eq, ← p.preimage_iSup, hUtop]
    exact le_inf le_top le_rfl

theorem exists_splits_top [IsAffine S] [Flat iY] [CompactSpace X] [QuasiSeparatedSpace X]
    (hY : ∀ U U' : Y.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hiX : Function.Bijective iX.appTop.hom) {t : Y ⟶ Z} (ht : t ≫ q = 𝟙 Y)
    (hV : ⨆ a, V a = ⊤) (ρ : ∀ a, Γ(Y, t ⁻¹ᵁ V a))
    (hρ : ∀ a b, (t.app (V a ⊓ V b)).hom (φ a b) =
      rs (t.preimage_mono inf_le_left) (ρ a) - rs (t.preimage_mono inf_le_right) (ρ b))
    (hτ : ∀ W : Y.affineOpens, ∃ τ, Splits V φ (q ⁻¹ᵁ W.1) τ) : ∃ χ, Splits V φ ⊤ χ := by
  choose τ hτ using hτ
  have hN : ∀ N : Y.Opens, N ≤ t ⁻¹ᵁ (q ⁻¹ᵁ N) := by
    intro N
    rw [← Scheme.Hom.comp_preimage, ht]
    exact le_rfl
  have hN' : ∀ N : Y.Opens, N ≤ (𝟙 Y : Y ⟶ Y) ⁻¹ᵁ N := fun N => le_rfl
  obtain ⟨x, hx⟩ := pull_coboundary hV t ρ hρ (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ
    (fun j => j.1) (fun j => hN _)
  refine splits_glue (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ
    (fun j => (q.appLE j.1 _ le_rfl).hom (x j)) ?_ ⊤ ?_
  · intro j k a M hj hk ha
    have hW' := hY _ _ j.2 k.2
    have m1 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1 := q.preimage_mono inf_le_left
    have m2 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1 := q.preimage_mono inf_le_right
    obtain ⟨e, he⟩ := exists_isDiff hV (hτ j) (hτ k) m1 m2
    have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := j.1 ⊓ k.1) (UX := ⊤)
      (UY := q ⁻¹ᵁ (j.1 ⊓ k.1)) le_top le_top (by simp)).1
      (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _) hW'
        (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ))
    have : IsIso (iX.appLE ⊤ ⊤ le_top) := by
      have e : iX.appTop = iX.appLE ⊤ ⊤ le_top := iX.app_eq_appLE (U := ⊤)
      rw [← e]
      exact (ConcreteCategory.isIso_iff_bijective _).mpr hiX
    have hiso := po.isIso_inr_of_isIso
    obtain ⟨u, hu⟩ := (ConcreteCategory.bijective_of_isIso
      (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl)).2 e
    have hu' : (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl).hom u = e := hu
    have h1 := hx j k _ m1 m2 e he (j.1 ⊓ k.1) inf_le_left inf_le_right (hN _)
    rw [← hu', appLE_appLE t q _ ht _ _ (hN' _), id_appLE, rs_self] at h1
    have hM : M ≤ q ⁻¹ᵁ (j.1 ⊓ k.1) := by rw [q.preimage_inf]; exact le_inf hj hk
    have h2 := he a M hM ha
    rw [← hu', h1] at h2
    simp only [map_sub, appLE_rs, rs_appLE] at h2 ⊢
    exact h2.symm
  · rw [← q.preimage_iSup, iSup_affineOpens_eq_top]
    exact le_top

end General

theorem isAffineOpen_inf_of_isSeparated {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S)
    [IsSeparated f] (U U' : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') :
    IsAffineOpen (U ⊓ U') := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  exact hU.inf hU'

theorem kuenneth_injective :
    ∀ (K : Type) [Field K] (X Y : Over (Spec (CommRingCat.of K))) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → Function.Bijective X.hom.appTop.hom → Function.Bijective Y.hom.appTop.hom → ∀ (I : Type) (V : I → (X ⊗ Y).left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ((X ⊗ Y).left, V a ⊓ V b), (∀ a b d, ((X ⊗ Y).left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b)).op).hom (φ a b) + ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d)).op).hom (φ b d) = ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d)).op).hom (φ a d)) → (∃ ψ : ∀ a, Γ(X.left, (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a), ∀ a b, ((lift (𝟙 X) (toUnit X ≫ y₀)).left.app (V a ⊓ V b)).hom (φ a b) = (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → (∃ ψ : ∀ a, Γ(Y.left, (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a), ∀ a b, ((lift (toUnit Y ≫ x₀) (𝟙 Y)).left.app (V a ⊓ V b)).hom (φ a b) = (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → ∃ ψ : ∀ a, Γ((X ⊗ Y).left, V a), ∀ a b, φ a b = ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) - ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_right).op).hom (ψ b) := by
  intro K _ X Y x₀ y₀ sX qX sY qY bX bY I V hV φ hφ ⟨ρX, hρX⟩ ⟨ρY, hρY⟩
  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    IsPullback.of_hasPullback X.hom Y.hom
  have hR : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := (quasiSeparated_iff_quasiSeparatedSpace X.hom).mp inferInstance
  have : Flat Y.hom := inferInstance
  have hco : IsCocycle V φ := by
    intro a b d N ha hb hd
    have := congrArg (rs (le_inf (le_inf ha hb) hd)) (hφ a b d)
    rw [map_add (f := _)] at this
    exact (congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm.trans (this.trans (rs_rs _ _ _))
  let y : Spec (CommRingCat.of K) ⟶ Y.left := y₀.left
  have hy : y ≫ Y.hom = 𝟙 _ := Over.w y₀
  have hs : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (fst X Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hs' : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (snd X Y).left = X.hom ≫ y := by
    rw [← Over.comp_left, lift_snd]; rfl
  have ht : (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ≫ (snd X Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Y.left.affineOpens, ⊤ ≤ y ⁻¹ᵁ W₀.1 := by
    have : y default ∈ ⨆ W : Y.left.affineOpens, W.1 := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine ⟨W, fun z _ => ?_⟩
    rw [Subsingleton.elim z default]
    exact hW
  obtain ⟨χ, hχ⟩ := exists_splits_top H (isAffineOpen_inf_of_isSeparated Y.hom) bX ht hV ρY hρY
    (exists_splits_preimage H hR (isAffineOpen_inf_of_isSeparated X.hom)
      (isAffineOpen_inf_of_isSeparated Y.hom) bY.2 hy hs hs' W₀ hW₀ hV hco ρX hρX)
  refine ⟨fun a => rs (le_inf le_top le_rfl) (χ a), fun a b => ?_⟩
  have := hχ a b (V a ⊓ V b) le_top inf_le_left inf_le_right
  rw [rs_self] at this
  exact this.trans (congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm

end GlobalTheory.KuennethOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtendRig

theorem isRegularRing_of_isLocalization {B : Type} [CommRing B] [IsRegularRing B]
    (M : Submonoid B) (R : Type) [CommRing R] [Algebra B R] [IsLocalization M R] :
    IsRegularRing R := by
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing M R inferInstance
  rw [isRegularRing_iff]
  intro q hq
  have h : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap B R)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (q.comap (algebraMap B R)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap B R))) (Localization.AtPrime q)).toRingEquiv

theorem isRegularRing_of_isDiscreteValuationRing (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] : IsRegularRing V :=
  have : IsDedekindDomain V := IsPrincipalIdealRing.isDedekindDomain V
  inferInstance

theorem isLocalization_away_of_irreducible (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    {π : V} (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K)
    (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
    inferInstance
  intro a ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hπ
  exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

theorem isOpenImmersion_etaK (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] :
    IsOpenImmersion (etaK V K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isLocalization_away_of_irreducible V K hπ
  exact IsOpenImmersion.of_isLocalization π

theorem isRegularRing_stalk
    (hreg : ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B]
      [Algebra.Smooth V B], IsRegularRing B)
    (V : Type) [CommRing V] [IsRegularRing V] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V))
    [Smooth f] (x : X) : IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hs : (f.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have : IsRegularRing Γ(Spec (CommRingCat.of V), ⊤) :=
    IsRegularRing.of_ringEquiv
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
  algebraize [(f.appLE ⊤ U le_top).hom]
  have : IsRegularRing Γ(X, U) := hreg Γ(Spec (CommRingCat.of V), ⊤) Γ(X, U)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _

theorem extend_exists :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B], IsRegularRing B) → (∀ (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R], UniqueFactorizationMonoid R) → (∀ (X Y : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB → ∃ L' : LB X, L'.IsLB ∧ ∃ φ : LB.Iso (L'.pull j) L, φ.IsGen) → Semi.extend_existsSt.{0} := by
  intro hint hreg hufd hext V _ _ _ K _ _ _ G _ _ _ _ _ _ eA _ L hL _ _
  have hV : IsRegularRing V := isRegularRing_of_isDiscreteValuationRing V
  have : GeometricallyIntegral G.hom := hint _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have := isOpenImmersion_etaK V K
  have hj : IsOpenImmersion (jA V K G) := inferInstance
  have hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x) := fun x =>
    have := isRegularRing_stalk hreg V G.hom x
    hufd _
  obtain ⟨L', hL', φ, hφ⟩ := hext G.left _ (jA V K G) hj hst L hL
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := V) L' hL' (K := PUnit)
    (fun _ => eSec G) (fun _ => 1)
  exact ⟨⟨L', e, hL', he⟩, φ, hφ⟩

end GlobalTheory.ExtendRig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem isRegularLocalRing_atPrime_of_etale' (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (h : IsRegularLocalRing (Localization.AtPrime (q.under R))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have hlo : q.LiesOver (q.under R) := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hmax : (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q).mp inferInstance).2
  have hsf : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank := by
    have heq : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) := by
      rw [← hmax, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq]
    rw [heq]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsLocalRing.maximalIdeal _).fg_of_isNoetherianRing
  have hht : (q.under R).height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under R) q]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank : WithBot ℕ∞) := by
        exact_mod_cast hsf
    _ = ringKrullDim (Localization.AtPrime (q.under R)) := h.spanFinrank_maximalIdeal
    _ = ((q.under R).height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R) _
    _ ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ = ringKrullDim (Localization.AtPrime q) :=
        (IsLocalization.AtPrime.ringKrullDim_eq_height q _).symm

theorem isRegularRing_of_etale (R S : Type*) [CommRing R] [IsRegularRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  exact isRegularRing_iff.mpr fun q _ => isRegularLocalRing_atPrime_of_etale' R S q inferInstance

theorem isRegularRing_of_smooth :
    ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B],
      IsRegularRing B := by
  intro V B _ _ _ _ _
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing V B
  refine isRegularRing_iff.mpr fun Q _ => ?_
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := V) (p := Q)
  have hT : IsRegularRing (Localization.Away f) :=
    isRegularRing_of_etale (MvPolynomial (Fin n) V) (Localization.Away f)
  have disj : Disjoint (Submonoid.powers f : Set B) (Q : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let Q' := Q.map (algebraMap B (Localization.Away f))
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime Q') Q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f)
      (Localization.AtPrime Q') Q'
    exact (IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› disj).symm
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q') (Localization.AtPrime Q)).toRingEquiv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace GlobalTheory.AbLaw.MulN

theorem isMonHom_mulA {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom (mulA A n) := by
  induction n with
  | zero =>
    change IsMonHom (𝟙 A ^ 0)
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    change IsMonHom (𝟙 A ^ (n + 1))
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift (mulA A n) (𝟙 A) ≫ μ[A]))

theorem isPullback_baseChange {S T : Scheme.{0}} (t : T ⟶ S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom t) ((Over.pullback t).map f).left f.left
      (pullback.fst Y.hom t) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom t) (v₂₂ := Y.hom) (h₃₁ := t) ?_ ?_
    (IsPullback.of_hasPullback Y.hom t)
  · have h1 : ((Over.pullback t).map f).left ≫ pullback.snd Y.hom t = pullback.snd X.hom t :=
      pullback.lift_snd _ _ _
    rw [h1, Over.w f]
    exact IsPullback.of_hasPullback X.hom t
  · exact (pullback.lift_fst _ _ _).symm

theorem surjective_of_geomFibres {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Surjective ((Over.pullback t).map f).left) : Surjective f.left := by
  refine ⟨fun y => ?_⟩
  let K := AlgebraicClosure (Y.left.residueField y)
  let u : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := u ≫ Y.hom
  have hs := h K t
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t := pullback.lift u (𝟙 _) (by simp [t])
  obtain ⟨x, hx⟩ := ((Over.pullback t).map f).left.surjective (v p)
  refine ⟨pullback.fst X.hom t x, ?_⟩
  have e := (isPullback_baseChange t f).w
  have e1 : f.left (pullback.fst X.hom t x) =
      pullback.fst Y.hom t (((Over.pullback t).map f).left x) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  rw [e1, hx, ← Scheme.Hom.comp_apply]
  have : v ≫ pullback.fst Y.hom t = u := pullback.lift_fst _ _ _
  rw [this]
  exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)

theorem mulA_finite_flat_surjective_etale :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left) → (∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ f : A ⟶ A, IsMonHom f → IsFinite f.left → Flat f.left ∧ Surjective f.left) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFiniteType Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left) → (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ), IsUnit (n : Γ(S, ⊤)) → FormallyUnramified (mulA G n).left) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left) := by
  intro hfin hK hfib hunr S _ P n hn
  have hc := P.isAb.comm
  have hsm := P.isAb.smooth
  have hf := hfin S P n hn
  have hm := isMonHom_mulA P.A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map (mulA P.A n)).left ∧
        Surjective ((Over.pullback t).map (mulA P.A n)).left := fun K _ _ t =>
    hK K _ (TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_baseChange t _) hf)
  have hflat : Flat (mulA P.A n).left :=
    hfib S _ _ _ inferInstance inferInstance hf fun K _ _ t => (hgeo K t).1
  refine ⟨hf, hflat, surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2, fun hu => ?_⟩
  have := hunr S P.A n hu
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  exact Etale.of_formallyUnramified_of_flat _

end GlobalTheory.AbLaw.MulN
end

