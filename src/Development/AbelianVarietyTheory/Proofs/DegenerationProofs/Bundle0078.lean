module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCutByInvariantRatiosField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.KerCut

theorem hom_ext_of_appLE {X Y : Scheme.{0}} (V : X.Opens) (hV : IsAffineOpen V) (f g : Y ⟶ X)
    (hf : ⊤ ≤ f ⁻¹ᵁ V) (hg : ⊤ ≤ g ⁻¹ᵁ V) (e : f.appLE V ⊤ hf = g.appLE V ⊤ hg) : f = g := by
  have : IsAffine V.toScheme := hV
  have r : ∀ (f : Y ⟶ X), ⊤ ≤ f ⁻¹ᵁ V → ∃ f' : Y ⟶ V.toScheme, f = f' ≫ V.ι := by
    intro f hf
    refine ⟨IsOpenImmersion.lift V.ι f ?_, (IsOpenImmersion.lift_fac _ _ _).symm⟩
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hf (show y ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨f', ef⟩ := r f hf
  obtain ⟨g', eg⟩ := r g hg
  rw [← GlobalTheory.FunDescent.res_comp_appTop V f' f ef, ← GlobalTheory.FunDescent.res_comp_appTop V g' g eg] at e
  have : f' = g' := by
    apply ext_of_isAffine
    ext x
    obtain ⟨y, rfl⟩ := (GlobalTheory.FunDescent.res_bijective V).2 x
    exact congrArg (fun ψ => ψ.hom y) e
  rw [ef, eg, this]

theorem appLE_appLE_apply {X Y Z : Scheme.{0}} (k : Z ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (W : Y.Opens)
    (h : W ≤ q ⁻¹ᵁ V) (h' : ⊤ ≤ k ⁻¹ᵁ W) (p : Z ⟶ X) (e : k ≫ q = p) (h'' : ⊤ ≤ p ⁻¹ᵁ V) (v : Γ(X, V)) :
    (k.appLE W ⊤ h').hom ((q.appLE V W h).hom v) = (p.appLE V ⊤ h'').hom v := by
  subst e
  rw [← Scheme.Hom.appLE_comp_appLE k q V W ⊤ h h']
  rfl

end GlobalTheory.ZJ.KerCut

namespace GlobalTheory.ZJ

theorem Charts.kerIs_of_torus : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H) (a) (j : Fin d → C.I), GeometricallyConnected H.hom → C.Torus c i → C.Based c a j → C.KerIs a j i := by
  intro K _ H _ _ _ _ _ C d c i a j hc hT hB
  obtain ⟨B, _, q, -, hq, -, -, -, hP, hV⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hT
  obtain ⟨V, hW, hVa, hu⟩ := hV a
  have one_mem : ∀ Y : Over (Sp K), ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a := by
    intro Y y _
    exact hB.1 (show (toUnit Y).left y ∈ (⊤ : (Sp K).Opens) from trivial)
  refine ⟨⟨fun {Y} s t e => hP.hom_ext e (toUnit_unique _ _)⟩, fun Y k => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨h, h₁, hr⟩
    have key : k ≫ q = (1 : Y ⟶ H) ≫ q := by
      apply Over.OverMorphism.ext
      have m : ∀ g : Y ⟶ H, ⊤ ≤ g.left ⁻¹ᵁ C.W a → ⊤ ≤ (g ≫ q).left ⁻¹ᵁ V := by
        intro g hg
        rw [hW] at hg
        exact hg
      refine KerCut.hom_ext_of_appLE V hVa _ _ (m k h) (m 1 h₁) ?_
      ext v
      have hv := hT.gen a _ ((hu _).2 ⟨v, rfl⟩)
      have eq := RingHom.eqOn_set_closure (f := (k.left.appLE _ ⊤ h).hom)
        (g := ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom) (by
          rintro u (⟨w, rfl⟩ | ⟨j', hj', rfl⟩)
          · exact (KerCut.appLE_appLE_apply _ _ _ _ _ _ Y.hom (Over.w k) le_rfl w).trans
              (KerCut.appLE_appLE_apply _ _ _ _ _ _ Y.hom (Over.w _) le_rfl w).symm
          · exact hr j' hj') hv
      exact (KerCut.appLE_appLE_apply _ _ _ _ _ _ _ rfl (m k h) v).symm.trans
        (eq.trans (KerCut.appLE_appLE_apply _ _ _ _ _ _ _ rfl (m 1 h₁) v))
    have w : k ≫ q = toUnit Y ≫ η[B] := by
      rw [key, MonObj.one_comp]
      rfl
    exact ⟨hP.lift _ _ w, (hP.lift_fst _ _ w).symm⟩
  · rintro ⟨t, rfl⟩
    have h' := hT.stable a Y t 1 (one_mem Y)
    have hr := fun j' hj' => hT.inv a j' hj' Y t 1 (one_mem Y) h'
    revert h' hr
    rw [_root_.mul_one]
    intro h' hr
    refine ⟨h', one_mem Y, fun j' hj' => ?_⟩
    rw [hr j' hj', charUnit_zero_val, map_one, _root_.one_mul]
  · intro Y t n h h₁
    have := hT.wt a (j n) n (hB.2 n).1 Y t 1 h₁
    rw [_root_.mul_one] at this
    exact this h

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.BasisBaseChange

open GlobalTheory.FieldBaseChange

section Algebra

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']

theorem basis_map_of_basis {φ : R →+* R'} (f : M →ₛₗ[φ] M') {I J : Type} [Fintype I] [Fintype J]
    (b : J → M) (β : I → M) (hb : ∀ s, ∃! a : J → R, s = ∑ j, a j • b j)
    (hβ : ∀ s, ∃! a : I → R, s = ∑ i, a i • β i)
    (hf : ∀ s, ∃! a : J → R', s = ∑ j, a j • f (b j)) (s : M') : ∃! a : I → R', s = ∑ i, a i • f (β i) := by
  classical
  choose u hu _ using fun i => hb (β i)
  choose w hw _ using fun j => hβ (b j)
  have huw : ∀ i i', ∑ j, u i j * w j i' = if i = i' then 1 else 0 := fun i => by
    have h1 : β i = ∑ i', (∑ j, u i j * w j i') • β i' := by
      conv_lhs => rw [hu i]
      simp only [Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [← Finset.smul_sum, ← hw j]
    have h2 : β i = ∑ i', (if i = i' then (1 : R) else 0) • β i' := by simp
    exact congrFun ((hβ (β i)).unique h1 h2)
  have fβ : ∀ a : I → R', ∑ i, a i • f (β i) = ∑ j, (∑ i, a i * φ (u i j)) • f (b j) := fun a => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.smul_sum, hu i, map_sum]
    simp only [map_smulₛₗ, ← hu i]
  have fb : ∀ c : J → R', ∑ j, c j • f (b j) = ∑ i, (∑ j, c j * φ (w j i)) • f (β i) := fun c => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.smul_sum, hw j, map_sum]
    simp only [map_smulₛₗ, ← hw j]
  have back : ∀ (a : I → R') i', ∑ j, (∑ i, a i * φ (u i j)) * φ (w j i') = a i' := fun a i' => by
    simp only [Finset.sum_mul, _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← Finset.mul_sum, ← map_sum, huw]
    simp [apply_ite φ]
  obtain ⟨c, hc, hcu⟩ := hf s
  refine ⟨_, hc.trans (fb c), fun a ha => funext fun i => ?_⟩
  rw [← hcu _ (ha.trans (fβ a)), back]

end Algebra

theorem isLin_iff {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp R) {H : LB Y} {I : Type} [Fintype I]
    (s : I → SecOver p H) (a : I → R) (t : SecOver p H) : IsLin p s a t ↔ t = ∑ i, a i • s i := by
  have e : ∀ l, chartFun p H l (∑ i, a i • s i) = ∑ i, a i • chartFun p H l (s i) := fun l =>
    (map_sum (chartLin p H l) _ _).trans rfl
  exact ⟨fun h => SecOver.ext _ _ fun l => (h l).trans (e l).symm, fun h l => (congrArg (chartFun p H l) h).trans (e l)⟩

theorem basis_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {A : Over (Sp R)}
    {L : LB A.left} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : K → (A.left ⟶ A.left)) (ε : K → ℤ) {m : ℕ}
    (b : Fin m → SecOver A.hom (LB.LinComb L ψ ε))
    (hb : IsSecBasis (T := Over.mk (spMap φ)) (A := A) _
      (fun i => DVR.pullSec L ψ ε (b i) (snd (Over.mk (spMap φ)) A).left))
    {B : Scheme.{0}} {pB : B ⟶ Sp R'} {π : B ⟶ A.left} (H : IsPullback π pB A.hom (spMap φ))
    {ψ' : K → (B ⟶ A.left)} (hψ : ∀ k, ψ' k = π ≫ ψ k) (s : SecOver pB (LB.LinComb L ψ' ε)) :
    ∃! a : Fin m → R', s = ∑ i, a i • pullOver L ε H.w hψ (b i) := by
  let T : Over (Sp R) := Over.mk (spMap φ)
  let p : (T ⊗ A).left ⟶ Sp R' := (fst T A).left
  let q : (T ⊗ A).left ⟶ A.left := (snd T A).left
  have H' : IsPullback q p A.hom (spMap φ) := (IsPullback.of_hasPullback (spMap φ) A.hom).flip
  let e := H.isoIsPullback _ _ H'
  have e1 : e.hom ≫ q = π := H.isoIsPullback_hom_fst _ _ H'
  have e2 : e.hom ≫ p = pB ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_hom_snd _ _ H'
  have e3 : e.inv ≫ π = q := H.isoIsPullback_inv_fst _ _ H'
  have e4 : e.inv ≫ pB = p ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_inv_snd _ _ H'
  have f1 : ∀ k, ψ' k = e.hom ≫ (q ≫ ψ k) := fun k => by rw [hψ, ← e1, Category.assoc]
  have f2 : ∀ k, q ≫ ψ k = e.inv ≫ ψ' k := fun k => by rw [hψ, ← e3, Category.assoc]
  let F := pullOver L ε e2 (φ := fun k => q ≫ ψ k) f1
  let G := pullOver L ε e4 (φ' := fun k => q ≫ ψ k) f2
  let b' : Fin m → SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε) := fun i => DVR.pullSec L ψ ε (b i) q
  have FG : ∀ t, F (G t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver e4 f2 _ _ hJ, Category.assoc, e.hom_inv_id, Category.comp_id]
  have GF : ∀ t, G (F t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e4 f2 _ _ hJ, sval_pullOver e2 f1 _ _ hJ, Category.assoc, e.inv_hom_id, Category.comp_id]
  have Fb : ∀ i, F (b' i) = pullOver L ε H.w hψ (b i) := fun i => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver H.w hψ _ _ hJ]
    exact (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.assoc, e1])
  have hb' : ∀ t : SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε), ∃! a : Fin m → R', t = ∑ i, a i • b' i := by
    intro t
    obtain ⟨r, hr, hu⟩ := hb t
    have e : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i)) = r i := fun i => Iso.hom_inv_id_apply _ _
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i), (isLin_iff p _ _ _).1 fun j => ?_,
      fun a ha => ?_⟩
    · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
      simp only [constFn, e]
      rfl
    · have := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (a i)) ((isLin_iff p _ _ _).2 ha)
      funext i
      rw [← this]
      exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R')) (a i)).symm
  have Fs : ∀ a : Fin m → R', F (∑ i, a i • b' i) = ∑ i, a i • pullOver L ε H.w hψ (b i) := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, Fb, RingHom.id_apply]
  obtain ⟨a, ha, hu⟩ := hb' (G s)
  refine ⟨a, ?_, fun a' ha' => hu a' ?_⟩
  · show s = _
    rw [← Fs, ← ha, FG]
  · show G s = _
    rw [ha', ← Fs, GF]

theorem basis_pullback : DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (N : ℕ), 1 ≤ N → ∀ (α : D.X) (R' : Type) [CommRing R'] (φ : R →+* R') (B : Scheme.{0}) (pB : B ⟶ Sp R') (π : B ⟶ D.P.A.left), IsPullback π pB D.P.A.hom (spMap φ) → ∀ (I : Type) [Fintype I] (β : I → D.SecB N α), IsBasisB D β → ∀ b : LB.Sec (LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε N)), ∃! a : I → R', IsLin pB (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π) a b := by
  intro hT R _ _ _ _ D N hN α R' _ φ B pB π H I _ β hβ s
  have hL := D.P.isLB
  obtain ⟨m, b, -, hb⟩ := hT R D N hN α
  have H₀ : IsPullback (𝟙 D.P.A.left) D.P.A.hom D.P.A.hom (spMap (RingHom.id R)) := by
    have : spMap (RingHom.id R) = 𝟙 _ := by simp [spMap]
    rw [this]
    exact IsPullback.id_horiz _
  have hψ₀ : ∀ k, D.famφB α k = 𝟙 _ ≫ D.famφB α k := fun k => (Category.id_comp _).symm
  have h0 := basis_of_isPullback (RingHom.id R) hL (D.famφB α) (DegPre.famε N) b
    (hb R (RingHom.id R) _ fun _ _ => rfl) H₀ hψ₀
  have e0 : ∀ i, pullOver D.P.L (DegPre.famε N) H₀.w hψ₀ (b i) = b i := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H₀.w hψ₀ _ _ hJ).trans (by rw [Category.comp_id])
  simp only [e0] at h0
  have hψ : ∀ k, (fun i => π ≫ D.famφB α i) k = π ≫ D.famφB α k := fun _ => rfl
  have h1 := basis_of_isPullback φ hL (D.famφB α) (DegPre.famε N) b (hb R' φ _ fun _ _ => rfl) H hψ
  have h2 := basis_map_of_basis (pullOver D.P.L (DegPre.famε N) H.w hψ) b β h0
    (fun t => (existsUnique_congr fun a => isLin_iff D.P.A.hom β a t).1 (hβ t)) h1 s
  have e1 : ∀ i, pullOver D.P.L (DegPre.famε N) H.w hψ (β i) =
      DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H.w hψ _ _ hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm
  simp only [e1] at h2
  exact (existsUnique_congr fun a => isLin_iff pB _ a s).2 h2

end GlobalTheory.ZH.BasisBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationEqPolarFormOfWeightZeroMax
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ValLat

theorem norm_le_of_hasSum {I C : Type} [NormedAddCommGroup C] [IsUltrametricDist C] {f : I → C} {a : C}
    (h : HasSum f a) {r : ℝ} (hr : 0 ≤ r) (hf : ∀ x, ‖f x‖ ≤ r) : ‖a‖ ≤ r := by
  rw [← h.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr hf

theorem le_norm_of_hasSum {I C : Type} [NormedAddCommGroup C] [IsUltrametricDist C] {f : I → C} {a : C}
    (h : HasSum f a) {b : I} (hf : ∀ x, x ≠ b → ‖f x‖ < ‖f b‖) : ‖f b‖ ≤ ‖a‖ := by
  rcases (norm_nonneg (f b)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  obtain ⟨r, hr0, hrb, hr⟩ : ∃ r, 0 ≤ r ∧ r < ‖f b‖ ∧ ∀ x, x ≠ b → ‖f x‖ ≤ r := by
    have ht := (tendsto_zero_iff_norm_tendsto_zero.1 h.summable.tendsto_cofinite_zero).eventually
      (gt_mem_nhds (half_pos h0))
    have hfin : {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖}.Finite :=
      (Filter.eventually_cofinite.1 ht).subset fun x hx => not_lt.2 hx.2
    rcases Set.eq_empty_or_nonempty {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖} with he | he
    · refine ⟨‖f b‖ / 2, by positivity, half_lt_self h0, fun x hx => ?_⟩
      by_contra hc
      exact (Set.eq_empty_iff_forall_notMem.1 he x) ⟨hx, (not_le.1 hc).le⟩
    · obtain ⟨y, hy, hm⟩ := Set.exists_max_image _ (fun x => ‖f x‖) hfin he
      refine ⟨‖f y‖, norm_nonneg _, hf y hy.1, fun x hx => ?_⟩
      by_cases hc : ‖f b‖ / 2 ≤ ‖f x‖
      · exact hm x ⟨hx, hc⟩
      · exact (not_le.1 hc).le.trans hy.2
  have h1 := norm_le_of_hasSum (h.update b 0) hr0 fun x => by
    rcases eq_or_ne x b with rfl | hx
    · simpa using hr0
    · rw [Function.update_of_ne hx]; exact hr x hx
  by_contra hc
  have h2 := IsUltrametricDist.norm_add_le_max a (-(0 - f b + a))
  rw [norm_neg, show a + -(0 - f b + a) = f b by abel] at h2
  exact h2.not_gt (max_lt (not_le.1 hc) (h1.trans_lt hrb))

theorem main : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ) (g N : ℕ) (J : Type) (cls : J → X) (p : ℕ) [Fact p.Prime] (w : J → PadicAlgCl p) (ν : X →+ ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → Module.finrank ℤ X ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → (∀ i, Short q N (cls i)) → Ser q N cls w ν → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ m, ∀ α, ν α = QuadraticMap.polar q m α := by
  intro X _ _ _ q g N J cls p _ w ν hq hg hN _ ⟨t, κ, hκ, hsum, hcls, hsz⟩ ⟨i₀, hi₀, hmax⟩
  have hQ := GlobalTheory.posDef_realExt_of_tendsto q hq
  have hN0 : (0 : ℝ) < N := lt_trans (by positivity) hN
  obtain ⟨m, hm⟩ := ClassMin.exists_global_min (ClassMin.realExtension_eq_realExt q ▸ hQ) ν one_pos
  simp only [div_one] at hm
  let ν' : X →+ ℝ := ν + (QuadraticMap.polarBilin q m).toAddMonoidHom
  have hν' : ∀ x, ν' x = ν x + QuadraticMap.polar q m x := fun x => rfl
  by_cases h0 : ν' = 0
  · refine ⟨-m, fun α => ?_⟩
    have := hν' α
    rw [h0] at this
    rw [QuadraticMap.polar_neg_left]
    simp only [AddMonoidHom.zero_apply] at this
    linarith
  exfalso
  obtain ⟨α, -, h1, h2⟩ := ClassMin.exists_shifted_lt_of_le (N := (N : ℤ)) hg hQ (by exact_mod_cast hN) h0
    fun y => by
      have := hm (m + y)
      rw [map_add ν] at this
      rw [hν', QuadraticMap.polar]
      linarith
  simp only [natCast_zsmul, Int.cast_natCast] at h1 h2
  have hshift : ∀ x, q (x + N • m) / N + ν (x + N • m) = q x / N + ν' x + N * (q m + ν m) := fun x => by
    have e := ClassMin.map_add_zsmul q x m (N : ℤ)
    rw [natCast_zsmul] at e
    rw [e, hν', map_add (f := _), map_nsmul, nsmul_eq_mul, QuadraticMap.polar_comm q m x]
    push_cast
    field_simp
    ring
  obtain ⟨i, hi⟩ := (hsz (α + N • m)).2
  obtain ⟨u, hu⟩ := hcls (α + N • m) i (by
    rw [← norm_pos_iff, hi]; positivity)
  have hA : ‖t (α + N • m) i‖ ≤ ‖w i‖ := le_norm_of_hasSum (f := fun x => t x i) (hsum i) fun x hx => by
    by_cases hz : t x i = 0
    · rw [hz, norm_zero, hi]; positivity
    obtain ⟨v, hv⟩ := hcls x i hz
    have e : x = α + N • (v - u) + N • m := by
      rw [hv, add_right_comm, hu, smul_sub]; abel
    have h3 := h1 (v - u) fun h => hx (by rw [e, h, smul_zero, add_zero])
    refine ((hsz x).1 i).trans_lt ?_
    rw [hi]
    refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) hκ
    have e1 := hshift (α + N • (v - u))
    rw [← e] at e1
    have e2 := hshift α
    rw [sub_div, sub_div]
    linarith
  have hB : ‖w i₀‖ ≤ κ * Real.exp (-(N * (q m + ν m))) := norm_le_of_hasSum (hsum i₀) (by positivity) fun x => by
    by_cases hz : t x i₀ = 0
    · rw [hz, norm_zero]; positivity
    obtain ⟨v, hv⟩ := hcls x i₀ hz
    refine ((hsz x).1 i₀).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hκ.le)
    have e := ClassMin.shifted_zsmul (Q := q) (N := (N : ℤ)) (by exact_mod_cast hN0.ne') ν v
    simp only [natCast_zsmul, Int.cast_natCast] at e
    rw [hv, hi₀, zero_add, map_zero, sub_zero, e]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (hm v) hN0.le)
  have hC := (hA.trans (hmax i)).trans hB
  rw [hi] at hC
  have hD := Real.exp_le_exp.1 (le_of_mul_le_mul_left hC hκ)
  have h3 := h2 (m - u)
  have e : α + N • (m - u) = cls i := by
    rw [smul_sub, ← add_sub_assoc, hu]; abel
  rw [e] at h3
  have e2 := hshift α
  rw [sub_div] at hD
  linarith

end GlobalTheory.ZH.ValLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeilPairingLabelledTorsionUniformTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH

theorem weilIs_uTest : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u x hx a b c hc
  have hpos : (S.r * S.N) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  have hζ : IsUnit S.ζ := S.prim.isUnit hpos
  obtain ⟨c₀, hc₀⟩ := (hζ.pow (S.r * S.N * (eStd S.g _ a b).val)).map (algebraMap o S.R)
  have H := ρ.weil a b c₀ hc₀
  have hf : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap u.fac)
    exact (Spec.map_comp (CommRingCat.ofHom u.yK)
      (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p)))).symm
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk (spMap y₀) ((Category.comp_id _).trans hf.symm)
  have H' := CommPairing.weilIs_pull hL.globalFns ρ.P.isAb ρ.P.isLB h H
  have e : Units.map h.left.appTop.hom.toMonoidHom (unitOn c₀) = unitOn c := by
    refine Units.ext ?_
    refine (congrArg (fun q => q.hom c₀.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y₀))).symm.trans ?_
    show (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom (y₀ c₀.val) =
      (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom c.val
    rw [hc, hc₀]
  rw [e] at H'
  exact (weilIs_grpPullback_of_comm' _ _ ρ.P.A u.A.A (spMap u.yK) u.φ ρ.P.L u.A.L ρ.P.isLB u.A.isLB u.cart u.lb
    (TFK (R := u.V) (PadicAlgCl p)) _ (x a) (x b) (h ≫ ρ.pt a) (h ≫ ρ.pt b) (unitOn c) (hx a).symm (hx b).symm).2 H'

end GlobalTheory.ZH
end
end

