module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusDescendFlatBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.FlatSec
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AmplePoint

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem exists_of_mem_map [Algebra R R'] {A A' : Type} [CommRing A] [CommRing A'] [Algebra R A] (p : A →+* A')
    (s' : R' →+* A') (e : R' ⊗[R] A ≃+ A') (he : ∀ c v, e (c ⊗ₜ v) = s' c * p v) (N : Ideal A) {y : A'}
    (hy : y ∈ N.map p) : ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = y := by
  suffices h : ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R), e ((N.restrictScalars R).subtype.lTensor R' x) = r * y by
    simpa using h 1
  refine Submodule.span_induction (p := fun y _ => ∀ r, ∃ x : R' ⊗[R] (N.restrictScalars R),
    e ((N.restrictScalars R).subtype.lTensor R' x) = r * y) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨v, hv, rfl⟩ r
    obtain ⟨t, rfl⟩ := e.surjective r
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c a => exact ⟨c ⊗ₜ ⟨a * v, N.mul_mem_left a hv⟩, by simp [he, mul_assoc]⟩
    | add a b ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨x', hx'⟩ := hb
      exact ⟨x + x', by rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), add_mul]⟩
  · exact fun r => ⟨0, by simp⟩
  · intro a b _ _ ha hb r
    obtain ⟨x, hx⟩ := ha r
    obtain ⟨x', hx'⟩ := hb r
    exact ⟨x + x', by rw [map_add (f := _), map_add (f := _), hx, hx', mul_add]⟩
  · intro a b _ hb r
    obtain ⟨x, hx⟩ := hb (r * a)
    exact ⟨x, by rw [hx, smul_eq_mul, mul_assoc]⟩

def vanIdeal (W U : X.Opens) : Ideal Γ(X, W) where
  carrier := {v | X.basicOpen v ≤ U}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => (X.basicOpen_add_le a b).trans (sup_le ha hb)
  smul_mem' := fun c a ha => by
    change X.basicOpen (c * a) ≤ U
    rw [Scheme.basicOpen_mul]
    exact inf_le_right.trans ha

theorem exists_pow_mem (π : X' ⟶ X) [IsAffineHom π] {W : X.Opens} (hW : IsAffineOpen W) (U : X.Opens)
    (t : Γ(X', π ⁻¹ᵁ W)) (ht : X'.basicOpen t ≤ π ⁻¹ᵁ U) : ∃ m, t ^ m ∈ (vanIdeal W U).map (π.app W).hom := by
  have hW' := hW.preimage π
  change t ∈ ((vanIdeal W U).map (π.app W).hom).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hP, hp⟩
  by_contra h
  let z : Spec Γ(X', π ⁻¹ᵁ W) := ⟨P, hp⟩
  have key : ∀ s : Γ(X', π ⁻¹ᵁ W), hW'.fromSpec z ∈ X'.basicOpen s ↔ s ∉ P := fun s => by
    change z ∈ hW'.fromSpec ⁻¹ᵁ X'.basicOpen s ↔ _
    rw [hW'.fromSpec_preimage_basicOpen]
    rfl
  have hz := (key t).2 h
  obtain ⟨v, hv, hzv⟩ := hW.exists_basicOpen_le (V := U) ⟨π (hW'.fromSpec z), ht hz⟩ (X'.basicOpen_le t hz)
  refine (key ((π.app W).hom v)).1 ?_ (hP (Ideal.mem_map_of_mem _ hv))
  rw [← Scheme.preimage_basicOpen]
  exact hzv

theorem exists_sec_mem (g : R →+* R') (hg : g.Flat) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (M : LB X) (hM : M.IsLB) {α : Type} [Fintype α]
    (W : α → X.Opens) (j : α → M.ι) (hA : ∀ a, IsAffineOpen (W a)) (hW : ∀ a, W a ≤ M.U (j a))
    (hc : ∀ y : X, ∃ a, y ∈ W a) (N : ∀ a, Ideal Γ(X, W a)) (σ : LB.Sec (M.pull π))
    (hσ : ∀ a, rs X' (le_pull M π (hW a)) (σ.f fun _ => j a) ∈ (N a).map (π.app (W a)).hom)
    (z : X') (hz : z ∈ nonzeroLocus σ) :
    ∃ u : M.Sec, π z ∈ nonzeroLocus u ∧ ∀ a, rs X (hW a) (u.f (j a)) ∈ N a := by
  let _ : Algebra R R' := g.toAlgebra
  have : Module.Flat R R' := hg
  let _ : ∀ U : X.Opens, Algebra R Γ(X, U) := fun U => (cst f U).toAlgebra
  choose e he using fun a => exists_equiv_of_isPushout (R := R) (π.app (W a)) (cst f' (π ⁻¹ᵁ W a))
    (isPushout_app hg H (hA a).isCompact (hA a).isQuasiSeparated)
  choose e' he' using fun p : α × α => exists_equiv_of_isPushout (R := R) (π.app (W p.1 ⊓ W p.2))
    (cst f' (π ⁻¹ᵁ (W p.1 ⊓ W p.2))) (isPushout_app hg H
      (QuasiSeparatedSpace.inter_isCompact _ _ (W p.1).isOpen (hA p.1).isCompact (W p.2).isOpen (hA p.2).isCompact)
      (IsQuasiSeparated.of_quasiSeparatedSpace _))
  let d : (∀ a, (N a).restrictScalars R) →ₗ[R] (∀ p : α × α, Γ(X, W p.1 ⊓ W p.2)) :=
    { toFun := fun v p => rs X inf_le_left (v p.1).1 -
        rs X (inf_le_inf (hW p.1) (hW p.2)) (M.g (j p.1) (j p.2)).val * rs X inf_le_right (v p.2).1
      map_add' := fun v w => funext fun p => by
        simp only [Pi.add_apply, Submodule.coe_add, map_add (f := _)]; ring
      map_smul' := fun r v => funext fun p => by
        simp only [Pi.smul_apply, Submodule.coe_smul, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, rs_cst,
          RingHom.id_apply]; ring }
  choose x hxe using fun a => exists_of_mem_map (π.app (W a)).hom (cst f' (π ⁻¹ᵁ W a)) (e a) (he a) (N a) (hσ a)
  have hx : ∀ {n : ℕ} {c : Fin n → R'} {v : Fin n → ∀ a, (N a).restrictScalars R},
      (∀ a, x a = ∑ i, AddEquiv.refl _ (c i ⊗ₜ v i a)) →
      ∀ a z, π z ∈ W a → gs (𝟙 X') z _ (σ.f fun _ => j a) =
        ∑ i, gs (𝟙 X') z ⊤ (cst f' ⊤ (c i)) * gs π z _ (v i a).1 := fun {n c v} h a z hz => by
    have h' := congrArg (gs (𝟙 X') z (π ⁻¹ᵁ W a)) (hxe a).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [h a, map_sum, AddEquiv.refl_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply, he] at h'
    rw [gs_comb f' π _ z hz] at h'
    exact (gs_res (𝟙 X') z _ hz _).symm.trans h'
  obtain ⟨n, c, v, hv, hd⟩ := exists_comb_ker (fun a => AddEquiv.refl _) e' d x
    (fun n c v h p => fn_ext fun z hz => by
      simp only [he']
      rw [gs_comb f' π _ z hz, LBGerm.gs_zero (𝟙 X') z _ hz]
      have h₁ := gs_pull_trans σ z (hW _ hz.1) (hW _ hz.2)
      rw [hx h p.1 z hz.1, hx h p.2 z hz.2, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h₁
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h₁
      refine (congrArg _ (gs_diff (hW p.1) (hW p.2) (v i p.1).1 (v i p.2).1 π z hz)).trans ?_
      ring)
  choose u hu using fun i => exists_sec_of_refinement hM W j hW hc (fun a => (v i a).1) fun y a b ha hb => by
    have h := congrArg (gs (𝟙 X) y (W a ⊓ W b)) (congrFun (hd i) (a, b))
    exact sub_eq_zero.1 ((gs_diff (hW a) (hW b) (v i a).1 (v i b).1 (𝟙 X) y ⟨ha, hb⟩).symm.trans
      (h.trans (LBGerm.gs_zero (𝟙 X) y _ ⟨ha, hb⟩)))
  have hu' : ∀ i a, rs X (hW a) ((u i).f (j a)) = (v i a).1 := fun i a => fn_ext fun y hy => by
    rw [gs_res (𝟙 X) y _ hy, hu i y (j a) a (hW a hy) hy, gm_self hM (𝟙 X) y (hW a hy), Units.val_one,
      _root_.one_mul]
  obtain ⟨a, ha⟩ := hc (π z)
  have h₁ := (mem_nonzeroLocus_iff_isUnit σ (k := fun _ => j a) (mem_pull.2 (hW a ha))).1 hz
  replace h₁ := hx hv a z ha ▸ h₁
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum h₁
  refine ⟨u i, (mem_nonzeroLocus_iff_pull (u i) π z (hW a ha)).2 ?_, fun b => hu' i b ▸ (v i b).2⟩
  rw [← gs_res π z (hW a) ha]
  exact (congrArg (fun w => IsUnit (gs π z _ w)) (hu' i a)).mpr (isUnit_of_mul_isUnit_right hi)

def chartPullPullPow (L : LB X) (f : X' ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull f) (lbPow (L.pull f) n) (𝟙 X') where
  idx J := fun _ _ => J PUnit.unit PUnit.unit
  le _ _ hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    have h₁ := mem_pull.1 hJ
    have h₂ := mem_pull.1 hJ'
    refine (gm_pull_g (lbPow L n) f (𝟙 X') y J J' hJ hJ').trans (Eq.symm ?_)
    refine ((chartPullPowPull L f n).g y _ _ (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₁)))
      (mem_powChart.2 (mem_pull.2 (mem_powChart.1 h₂)))).trans ?_
    rw [Category.id_comp]
    rfl

theorem exists_affine_locus : ∀ (R R' : Type) [CommRing R] [CommRing R'] (ρ : R →+* R'), ρ.Flat → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), QuasiCompact q → QuasiSeparated q → ∀ (L : LB X), L.IsLB → ∀ (x' : ↥(Limits.pullback q (spMap ρ))), (∃ n, 1 ≤ n ∧ ∃ s : (lbPow (L.pull (pullback.fst q (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) → ∃ n, 1 ≤ n ∧ ∃ s : (lbPow L n).Sec, pullback.fst q (spMap ρ) x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  rintro R R' _ _ ρ hρ X q _ _ L hL x' ⟨n, hn, s, hs, ha⟩
  have H := IsPullback.of_hasPullback q (spMap ρ)
  generalize pullback.snd q (spMap ρ) = q' at H
  have hπ : IsAffineHom (pullback.fst q (spMap ρ)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q (spMap ρ)).flip inferInstance
  generalize pullback.fst q (spMap ρ) = π at *
  generalize Limits.pullback q (spMap ρ) = X' at *
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated q
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated π
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := π x') trivial
  obtain ⟨φ, hφ, hxφ⟩ := ha.exists_basicOpen_le (V := π ⁻¹ᵁ U) ⟨x', hx⟩ hs
  obtain ⟨k, hk, t, ht⟩ := exists_nonzeroLocus_eq_basicOpen (LB.isLB_pull hL π) s φ
  obtain ⟨α, _, W, J, hWa, hW, hc⟩ : ∃ (α : Type) (_ : Fintype α) (W : α → X.Opens) (J : α → PUnit → L.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ powChart L (J a)) ∧ ∀ y : X, ∃ a, y ∈ W a :=
    exists_finite_affine_refinement (isLB_lbPow hL 0)
  have le : ∀ a, π ⁻¹ᵁ W a ≤ powChart (L.pull π) (fun _ _ => J a PUnit.unit) := fun a y hy =>
    mem_powChart.2 (mem_pull.2 (mem_powChart.1 (hW a hy)))
  choose m hm using fun a => exists_pow_mem π (hWa a) U (resG X' (le a) (powFn t _)) fun y hy => by
    have hy₁ : y ∈ π ⁻¹ᵁ W a := X'.basicOpen_le _ hy
    have h := (LBGerm.isUnit_gs_iff (𝟙 X') y _ hy₁ _).2 hy
    exact hφ (ht.le ((mem_nonzeroLocus_iff_powFn t (le a hy₁)).2
      ((congrArg IsUnit (gs_res (𝟙 X') y (le a) hy₁ _)).mp h)))
  let K := Finset.univ.sup m + 1
  have hK : 1 ≤ K := Nat.le_add_left _ _
  obtain ⟨u, hxu, hu⟩ := exists_sec_mem ρ hρ q π q' H (lbPow L (n * k * K)) (isLB_lbPow hL _) W J hWa hW hc
    (fun a => vanIdeal (W a) U) (chartSec (chartPullPullPow L π _) (secPow t K)) (fun a => by
      have e : rs X' (le_pull (lbPow L (n * k * K)) π (hW a))
          ((chartSec (chartPullPullPow L π _) (secPow t K)).f fun _ => J a) = resG X' (le a) (powFn t _) ^ K :=
        fn_ext fun y hy => by
          refine (gs_res (𝟙 X') y _ hy _).trans ((gs_chartSec _ _ (𝟙 X') y _
            (le_pull (lbPow L (n * k * K)) π (hW a) hy)).trans ?_)
          rw [Category.comp_id, LBGerm.gs_pow (𝟙 X') y _ hy, gs_res (𝟙 X') y _ hy]
          exact LBGerm.gs_pow (𝟙 X') y _ (le a hy) _ _
      rw [e]
      exact Ideal.pow_mem_of_pow_mem _ (hm a) ((Finset.le_sup (f := m) (Finset.mem_univ a)).trans (Nat.le_succ _)))
    x' (by
      rw [nonzeroLocus_chartSec_id (chartPullPullPow L π _) _ fun y I hI => ⟨fun _ _ => I PUnit.unit PUnit.unit,
        mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hI)))⟩, nonzeroLocus_secPow t hK, ht]
      exact hxφ)
  have hle : nonzeroLocus u ≤ U := fun y hy => by
    obtain ⟨a, hya⟩ := hc y
    refine (show X.basicOpen _ ≤ U from hu a) ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hya _).1 ?_)
    exact (congrArg IsUnit (gs_res (𝟙 X) y (hW a) hya _)).mpr ((mem_nonzeroLocus_iff_isUnit u (hW a hya)).1 hy)
  have h := isAffineOpen_nonzeroLocus_inf (isLB_lbPow hL _) u hU
  rw [inf_eq_left.2 hle] at h
  exact ⟨_, Nat.mul_pos (Nat.mul_pos hn hk) hK, u, hxu, h⟩

end GlobalTheory.AmplePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSymmetricLineBundleGrpScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymAmple

open GlobalTheory.CechPic

theorem exists_isAmpleLB_symm (S : Scheme.{0}) (G : Over S) [GrpObj G] (M₀ : LB G.left) (h₀ : IsAmpleLB M₀) :
    ∃ M : LB G.left, IsAmpleLB M ∧ LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M := by
  set i : G.left ⟶ G.left := (GrpObj.inv : G ⟶ G).left with hi_def
  have hii : i ≫ i = 𝟙 G.left := by
    rw [hi_def, ← Over.comp_left, GrpObj.inv_comp_inv G, Over.id_left]
  have : IsIso i := ⟨⟨i, hii, hii⟩⟩
  have hL := h₀.isLB
  have h₁ : IsAmpleLB (M₀.pull i) := h₀.pull_of_isAffineHom i
  let M : LB G.left := LB.LinComb M₀ (K := Fin 2) ![𝟙 G.left, i] ![1, 1]
  have hM : M.IsLB := LB.isLB_linComb hL _ _
  have hc : cls M hM = cls M₀ hL + GlobalTheory.CechPic.pull i (cls M₀ hL) := by
    rw [cls_linComb hL]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_zsmul, pull_id]
  refine ⟨M, h₀.tensor h₁ hM ?_, ?_⟩
  · have hd₁ := LB.isLB_div hM hL
    have hd₂ := LB.isLB_div hd₁ (pull_isLB hL i)
    refine (cls_eq_zero_iff hd₂).1 ?_
    rw [cls_div hd₁ (pull_isLB hL i), cls_div hM hL, hc, cls_pull hL]
    abel
  · refine (cls_eq_iff (pull_isLB hM i) hM).1 ?_
    rw [cls_pull hM, hc, map_add (f := _), ← pull_comp, hii, pull_id]
    exact add_comm _ _

end GlobalTheory.SymAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMap
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem smul_mem_map_eq_zero {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {i : R} (hi : i ∈ I) {x : B} (hx : x ∈ I.map (algebraMap R B)) : i • x = 0 := by
  rw [Algebra.smul_def]
  have h : algebraMap R B i * x ∈ I.map (algebraMap R B) * I.map (algebraMap R B) :=
    Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hi) hx
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  simpa using h

theorem exists_isSig : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)), ∃ σ : R₁ ⊗[R₀] B₀ →+ B, α.IsSig p σ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have hm : b - b' ∈ I.map (algebraMap R B) := (hker _).1 (by rw [map_sub, h, sub_self])
    have := smul_mem_map_eq_zero hI (α.mem y) hm
    rwa [smul_sub, sub_eq_zero] at this
  let s : B₀ → B := Function.surjInv hp
  have hs' : ∀ b₀, p (s b₀) = b₀ := Function.surjInv_eq hp
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b₀ ↦ α.k y • s b₀) (by
      intro b₀ b₀'
      rw [← smul_add]
      exact key y _ _ (by rw [map_add (f := _), hs', hs', hs'])))
    (by
      intro y y'
      ext b₀
      simp [add_smul])
  refine ⟨TensorProduct.liftAddHom f ?_, ?_⟩
  · intro r₀ y b₀
    obtain ⟨r, rfl⟩ := hπ r₀
    change α.k (π r • y) • s b₀ = α.k y • s (π r • b₀)
    rw [α.smul, mul_comm, mul_smul]
    exact key y _ _ (by rw [hs, hs', hs'])
  · intro y b
    change α.k y • s (p b) = α.k y • b
    exact key y _ _ (hs' _)

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRawDegenerationDataInjective
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PsiRing GlobalTheory.StrictPull GlobalTheory.ModelData GlobalTheory.DegPull

namespace GlobalTheory.BaseChangeDeg

theorem exists_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsNoetherianRing R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → ∃ (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X), IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β ∧ v.IsGen ∧ (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) ∧ GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v ∧ GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) := by
  intro R₁ _ _ R₂ _ _ _ σ D₁ gam hgam
  let P' : PolAV (Spec (CommRingCat.of R₂)) :=
    { A := (Over.pullback (spMap σ)).obj D₁.P.A
      isAb := TLinPf.isAb_pullback (spMap σ) D₁.P.A D₁.P.isAb
      g := D₁.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback D₁.P.A (spMap σ)).1 D₁.P.smoothDim
      L := D₁.P.L.pull (pullback.fst D₁.P.A.hom (spMap σ))
      isLB := pull_isLB D₁.P.isLB _
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback D₁.P.A (spMap σ)) D₁.P.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback D₁.P.A (spMap σ)) D₁.P.sym
      ample := by
        haveI := D₁.P.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback D₁.P.isLB D₁.P.ample (IsPullback.of_hasPullback D₁.P.A.hom (spMap σ))
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB D₁.P.isLB (pullback.fst D₁.P.A.hom (spMap σ)))
        exact kTriv_pull (isGrpPullback_pullback D₁.P.A (spMap σ)) D₁.P.isLB (pull_isLB D₁.P.isLB _) ((isGen_iff w).1 hw) D₁.P.ktriv }
  let F := pullback.fst D₁.P.A.hom (spMap σ)
  have gp : IsGrpPullback P'.A D₁.P.A (spMap σ) F := isGrpPullback_pullback D₁.P.A (spMap σ)
  obtain ⟨w, hw, -⟩ := exists_strict D₁.P.isLB F
  have hF := gp.1
  have hw' := (isGen_iff w).1 hw
  have hE : eSec P'.A ≫ F = spMap σ ≫ eSec D₁.P.A := (cubeMapOf gp).e_comm
  obtain ⟨rig, hrig, Hrig⟩ := exists_pmaps hw' D₁.P.isLB P'.isLB (K := PUnit) (φ' := fun _ => eSec P'.A)
    (φ := fun _ => eSec D₁.P.A) (ε := fun _ => 1) (spMap σ) (fun _ => hE) D₁.rig D₁.rig_gen
  obtain ⟨cub⟩ := nonempty_cubical_pull gp D₁.cub ⟨P'.L, rig, P'.isLB, hrig⟩ hw'
  obtain ⟨sym, hsym, hsr⟩ := exists_sym_pull gp D₁.P.isLB P'.isLB hw' D₁.sym D₁.sym_gen D₁.sym_rig
  obtain ⟨c, hc⟩ : ∃ c : D₁.X → (𝟙_ (Over (Spec (CommRingCat.of R₂))) ⟶ P'.A), ∀ x,
      (c x).left ≫ F = spMap σ ≫ (D₁.c x).left :=
    ⟨fun x => Over.homMk (hF.lift (spMap σ ≫ (D₁.c x).left) (𝟙 _) (by
      rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _)) (hF.lift_snd _ _ _),
      fun x => hF.lift_fst _ _ _⟩
  have cadd : ∀ a b, c (a + b) = padd P'.A (c a) (c b) := fun a b => by
    refine Over.OverMorphism.ext (hF.hom_ext ?_ (by rw [Over.w, Over.w]))
    have u : (toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R₂)))).hom ≫ spMap σ))).left = spMap σ :=
      Category.id_comp _
    have m := gp.2 _ (c a) (c b) (toUnit _ ≫ D₁.c a) (toUnit _ ≫ D₁.c b)
      (by rw [hc, Over.comp_left, u]) (by rw [hc, Over.comp_left, u])
    rw [← MonObj.comp_mul, Over.comp_left, u] at m
    rw [hc, D₁.c_add]
    exact m
  have hK : jK R₂ ≫ spMap σ = spMap gam ≫ jK R₁ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact (hgam r).symm
  have hx : ∀ x, ptK (c x) ≫ F = spMap gam ≫ D₁.xK x := fun x => by
    show (jK R₂ ≫ (c x).left) ≫ F = spMap gam ≫ jK R₁ ≫ (D₁.c x).left
    refine (Category.assoc _ _ _).trans ((congrArg (jK R₂ ≫ ·) (hc x)).trans ?_)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (D₁.c x).left) hK)).trans (Category.assoc _ _ _)
  choose psi hpsi vpsi using fun x => exists_pmaps hw' D₁.P.isLB P'.isLB (K := PUnit)
    (φ' := fun _ => ptK (c x)) (φ := fun _ => D₁.xK x) (ε := fun _ => -1) (spMap gam) (fun _ => hx x)
    (D₁.psi x) (D₁.psi_gen x)
  let D' : DegPre R₂ :=
    { P := P', rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D₁.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  exact ⟨D', F, w, AddEquiv.refl _, gp, hw, hc, Hrig, vpsi⟩

end GlobalTheory.BaseChangeDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenLeOfAppEqOneOfIsClosedImmersionAl
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion :
    ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (Y' : X'.Opens), IsAffineOpen Y' →
    ∀ (N : X'.Opens), (∀ z : Z', i' z ∈ Y' → i' z ∈ N) →
    ∃ b : Γ(X', Y'), (i'.app Y').hom b = 1 ∧ X'.basicOpen b ≤ N := by
  intro X' Z' i' _ Y' hY N hN
  classical
  let K : Ideal Γ(X', Y') :=
    { carrier := {f | X'.basicOpen f ≤ N}
      add_mem' hf hg := (X'.basicOpen_add_le _ _).trans (sup_le hf hg)
      zero_mem' := by simp
      smul_mem' c f hf := by
        change X'.basicOpen (c * f) ≤ N
        rw [Scheme.basicOpen_mul]
        exact inf_le_right.trans hf }
  have hmem (z : Spec Γ(X', Y')) (f : Γ(X', Y')) :
      hY.fromSpec z ∈ X'.basicOpen f ↔ f ∉ z.asIdeal := by
    change z ∈ hY.fromSpec ⁻¹ᵁ X'.basicOpen f ↔ _
    rw [hY.fromSpec_preimage_basicOpen]
    rfl
  have hJ : RingHom.ker (i'.app Y').hom ⊔ K = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ h
    let z : Spec Γ(X', Y') := ⟨m, hm.isPrime⟩
    have hyY : hY.fromSpec z ∈ Y' := hY.range_fromSpec.le ⟨z, rfl⟩
    by_cases hy : hY.fromSpec z ∈ Set.range i'
    · obtain ⟨w, hw⟩ := hy
      have hwN : hY.fromSpec z ∈ N := hw ▸ hN w (hw ▸ hyY)
      obtain ⟨f, hfN, hf⟩ := hY.exists_basicOpen_le (V := N) ⟨_, hwN⟩ hyY
      exact (hmem z f).mp hf (hJm (Ideal.mem_sup_right hfN))
    · have h1 : hY.fromSpec z ∉ (i'.ker.support : Set X') := by
        rw [Scheme.Hom.support_ker, i'.isClosedEmbedding.isClosed_range.closure_eq]
        exact hy
      have h2 : hY.fromSpec z ∉ X'.zeroLocus (U := Y') (i'.ker.ideal ⟨Y', hY⟩ : Set Γ(X', Y')) :=
        fun h ↦ h1 ((i'.ker.coe_support_inter ⟨Y', hY⟩).ge ⟨h, hyY⟩).1
      rw [Scheme.mem_zeroLocus_iff] at h2
      push_neg at h2
      obtain ⟨a, ha, hya⟩ := h2
      have ha' : a ∈ RingHom.ker (i'.app Y').hom := by
        rw [Scheme.Hom.ker_apply] at ha
        exact ha
      exact (hmem z a).mp hya (hJm (Ideal.mem_sup_left ha'))
  have h1 : (1 : Γ(X', Y')) ∈ RingHom.ker (i'.app Y').hom ⊔ K := hJ ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  refine ⟨b, ?_, hb⟩
  have ha0 : (i'.app Y').hom a = 0 := ha
  calc (i'.app Y').hom b = (i'.app Y').hom (a + b) := by rw [map_add (f := _), ha0, zero_add]
    _ = 1 := by rw [hab, map_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierLocusOverDenseOpenBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DivStart

theorem exists_locus_over_dense_open : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ (U : (Sp R).Opens) (c : Pic (A.hom ⁻¹ᵁ U ⊔ V).toScheme), (U : Set (Sp R)).Nonempty ∧ IsLocus c ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
  intro R _ _ _ _ A _ hA V hV hsurj
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsLocallyNoetherian (Sp R) := inferInstance
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : A.left.IsSeparated := ⟨by rw [← terminal.comp_from A.hom]; infer_instance⟩
  let s₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  obtain ⟨x₀, hx₀, -⟩ := hsurj s₀
  obtain ⟨W₀, hVW, hufd, c₀, hc₀⟩ := GlobalTheory.FactorialLocus.exists_isLocus A.left V hV ⟨x₀, hx₀⟩
  have hfib : ∀ x, A.hom x = s₀ → x ∈ W₀ := fun x hx =>
    hufd x (GlobalTheory.GenericFibreFactorial.ufd_stalk_of_generic R A.left A.hom x (by rw [hx]))
  obtain ⟨U, -, hsU, hUW⟩ := GlobalTheory.Tube.exists_affine_preimage_le A.left (Sp R) A.hom s₀ W₀ hfib
  have hle : A.hom ⁻¹ᵁ U ⊔ V ≤ W₀ := sup_le hUW hVW
  refine ⟨U, GlobalTheory.CechPic.pull (A.left.homOfLE hle) c₀, ⟨s₀, hsU⟩, ?_⟩
  have h := GlobalTheory.LocusPull.isLocus_pull (A.left.homOfLE hle) hc₀
  convert h using 1
  ext x
  change (A.hom ⁻¹ᵁ U ⊔ V).ι x ∈ V ↔ W₀.ι (A.left.homOfLE hle x) ∈ V
  rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]

end GlobalTheory.DivStart
end

