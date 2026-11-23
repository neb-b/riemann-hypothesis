module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0081
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulDetSpanSupLeDetSpanLattice
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.DetColon

variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ}

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
private lemma exterior_form_eq_zero_of_two_mem_span_singleton {ι : Type*} [DecidableEq ι]
    (f : V [⋀^ι]→ₗ[F] F) (u : V) (w : ι → V) {i k : ι} (hik : i ≠ k)
    (hi : w i ∈ Submodule.span (𝓞 F) {u}) (hk : w k ∈ Submodule.span (𝓞 F) {u}) :
    f w = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hi
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hk
  by_cases hb0 : algebraMap (𝓞 F) F b = 0
  · have hwk : w k = 0 := by
      rw [← hb, ← algebraMap_smul F b u, hb0, zero_smul]
    exact f.map_coord_zero k hwk
  · have hwi : w i = (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k := by
      rw [← ha, ← hb, ← algebraMap_smul F a u, ← algebraMap_smul F b u, smul_smul,
        div_mul_cancel₀ _ hb0]
    have hfw : f w = f (Function.update w i
        ((algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k)) := by
      rw [← hwi, Function.update_eq_self]
    rw [hfw, f.map_update_smul]
    have h0 : f (Function.update w i (w k)) = 0 :=
      f.map_eq_zero_of_eq (Function.update w i (w k)) (i := i) (j := k)
        (by simp [Function.update_of_ne hik.symm]) hik
    rw [h0, smul_zero]

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
private lemma multilinear_mem_span_of_entry_mem_span_singleton {ι : Type*} [DecidableEq ι]
    (f : V [⋀^ι]→ₗ[F] F) (N : Submodule (𝓞 F) V) (u : V) (s : Finset ι) :
    ∀ (i : ι) (w : ι → V), i ∉ s → w i ∈ Submodule.span (𝓞 F) {u} → (∀ j ∉ s, w j ∈ N) →
      (∀ j ∈ s, w j ∈ N ⊔ Submodule.span (𝓞 F) {u}) →
      f w ∈ Submodule.span (𝓞 F) {y | ∃ v : ι → V, (∀ j, v j ∈ N) ∧ y = f v} := by
  induction s using Finset.induction_on with
  | empty =>
    intro i w _ _ hN _
    exact Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩
  | @insert k s hks ih =>
    intro i w his hi hN hs
    have hik : i ≠ k := fun h => his (h ▸ Finset.mem_insert_self k s)
    have his' : i ∉ s := fun h => his (Finset.mem_insert_of_mem h)
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))
    have hsplit : f w = f (Function.update w k n) + f (Function.update w k z) := by
      rw [← f.map_update_add, hnz, Function.update_eq_self]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · refine ih i _ his' ?_ ?_ ?_
      · rwa [Function.update_of_ne hik]
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self]
          exact hn
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)
    · rw [exterior_form_eq_zero_of_two_mem_span_singleton f u _ hik
        (by rwa [Function.update_of_ne hik]) (by rw [Function.update_self]; exact hz)]
      exact Submodule.zero_mem _

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
private lemma smul_multilinear_mem_span {ι : Type*} [DecidableEq ι] (f : V [⋀^ι]→ₗ[F] F)
    (N : Submodule (𝓞 F) V) (u : V) (π : 𝓞 F) (hπ : π • u ∈ N) (s : Finset ι) :
    ∀ w : ι → V, (∀ j ∉ s, w j ∈ N) → (∀ j ∈ s, w j ∈ N ⊔ Submodule.span (𝓞 F) {u}) →
      π • f w ∈ Submodule.span (𝓞 F) {y | ∃ v : ι → V, (∀ j, v j ∈ N) ∧ y = f v} := by
  induction s using Finset.induction_on with
  | empty =>
    intro w hN _
    exact Submodule.smul_mem _ π (Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩)
  | @insert k s hks ih =>
    intro w hN hs
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))
    have hsplit : f w = f (Function.update w k n) + f (Function.update w k z) := by
      rw [← f.map_update_add, hnz, Function.update_eq_self]
    rw [hsplit, smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · refine ih _ ?_ ?_
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self]
          exact hn
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have key : π • f (Function.update w k (a • u)) = f (Function.update w k ((π * a) • u)) := by
        rw [mul_smul, ← algebraMap_smul F π (a • u), f.map_update_smul, algebraMap_smul]
      rw [key]
      refine multilinear_mem_span_of_entry_mem_span_singleton f N u s k _ hks ?_ ?_ ?_
      · rw [Function.update_self]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self, mul_comm, mul_smul]
          exact N.smul_mem a hπ
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)


open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
theorem _root_.GlobalTheory.DetColon.smul_detSpan_sup_le :
    ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
      [IsScalarTower (𝓞 F) F V] (d : ℕ) (b : Module.Basis (Fin d) F V) (N : Submodule (𝓞 F) V)
      (u : V) (π : 𝓞 F), π • u ∈ N →
      ∀ y ∈ Submodule.span (𝓞 F)
          {y | ∃ v : Fin d → V, (∀ i, v i ∈ N ⊔ Submodule.span (𝓞 F) {u}) ∧ y = b.det v},
        π • y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N) ∧ y = b.det v} := by
  intro F V _ _ _ _ _ _ d b N u π hπ y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact smul_multilinear_mem_span b.det N u π hπ Finset.univ v
      (fun j hj => absurd (Finset.mem_univ j) hj) (fun j _ => hv j)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx

end GlobalTheory.DetColon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTrivSqZeroExtIsPushout
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem pinch_main : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap (algebraMap R B) ≫ x → ∃! z₀ : Sp (TrivSqZeroExt R M) ⟶ X, spMap (TrivSqZeroExt.fstHom R R M).toRingHom ≫ z₀ = x ∧ spMap β ≫ z₀ = z := by
  intro R _ B M _ _ _ _ _ _ _ _ _ _ β hβ X x z hxz
  let T := Sp (TrivSqZeroExt R M)
  let i : Sp R ⟶ T := spMap (TrivSqZeroExt.fstHom R R M).toRingHom
  let j : Sp (TrivSqZeroExt B M) ⟶ T := spMap β
  have hcov0 := fun q => exists_basicOpen_inl (M := M) x q
  have EO := _root_.GlobalTheory.Pinch.exists_extend_basicOpen R B M β hβ X x z hxz
  have UO := _root_.GlobalTheory.PinchUniq.uniq R B M β hβ X x
  have RES : ∀ {Y' : Scheme.{0}} (f' : Y' ⟶ T) {V V' : T.Opens} (h : V' ≤ V) (g : V.toScheme ⟶ X) (w : Y' ⟶ X),
      f'.resLE V _ le_rfl ≫ g = (f' ⁻¹ᵁ V).ι ≫ w → f'.resLE V' _ le_rfl ≫ T.homOfLE h ≫ g = (f' ⁻¹ᵁ V').ι ≫ w := by
    intro Y' f' V V' h g w hg
    have e : f'.resLE V' _ le_rfl ≫ T.homOfLE h = Y'.homOfLE (f'.preimage_mono h) ≫ f'.resLE V _ le_rfl := by
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
    rw [reassoc_of% e, hg, Scheme.homOfLE_ι_assoc]
  let Idx := {p : Γ(T, ⊤) × X.affineOpens // i ⁻¹ᵁ T.basicOpen p.1 ≤ x ⁻¹ᵁ p.2.1}
  have hcov : TopologicalSpace.IsOpenCover (fun p : Idx => T.basicOpen p.1.1) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro q _
    obtain ⟨s, U, hq, hle⟩ := hcov0 q
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(s, U), hle⟩, hq⟩
  let 𝒰 := T.openCoverOfIsOpenCover _ hcov
  choose g hg using fun p : Idx => EO p.1.1 p.1.2 p.2
  have hc : ∀ a b : Idx, pullback.fst (𝒰.f a) (𝒰.f b) ≫ g a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ g b := by
    intro a b
    have hP := isPullback_opens_inf (T.basicOpen a.1.1) (T.basicOpen b.1.1)
    change pullback.fst (T.basicOpen a.1.1).ι (T.basicOpen b.1.1).ι ≫ g a =
      pullback.snd (T.basicOpen a.1.1).ι (T.basicOpen b.1.1).ι ≫ g b
    rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    refine UO _ (a.1.1 * b.1.1) (T.basicOpen_mul _ _).symm a.1.2 ((i.preimage_mono inf_le_left).trans a.2) _ _
      (RES i _ _ x (hg a).1) (RES i _ _ x (hg b).1) ?_
    rw [RES j _ _ z (hg a).2, RES j _ _ z (hg b).2]
  let z₀ := 𝒰.glueMorphisms g hc
  have hz₀ : ∀ a : Idx, (T.basicOpen a.1.1).ι ≫ z₀ = g a := fun a => 𝒰.ι_glueMorphisms g hc a
  have hi : i ≫ z₀ = x := by
    have hcovR : TopologicalSpace.IsOpenCover (fun p : Idx => i ⁻¹ᵁ T.basicOpen p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
    refine Scheme.Cover.hom_ext ((Sp R).openCoverOfIsOpenCover _ hcovR) _ _ fun a => ?_
    change (i ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ i ≫ z₀ = (i ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ x
    rw [← (hg a).1, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι i (le_rfl), Category.assoc]
  have hj : j ≫ z₀ = z := by
    have hcovA : TopologicalSpace.IsOpenCover (fun p : Idx => j ⁻¹ᵁ T.basicOpen p.1.1) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
    refine Scheme.Cover.hom_ext ((Sp (TrivSqZeroExt B M)).openCoverOfIsOpenCover _ hcovA) _ _ fun a => ?_
    change (j ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ j ≫ z₀ = (j ⁻¹ᵁ T.basicOpen a.1.1).ι ≫ z
    rw [← (hg a).2, ← hz₀ a, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι j (le_rfl), Category.assoc]
  refine ⟨z₀, ⟨hi, hj⟩, fun z₁ ⟨h1, h2⟩ => ?_⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun a => ?_
  change (T.basicOpen a.1.1).ι ≫ z₁ = (T.basicOpen a.1.1).ι ≫ z₀
  rw [hz₀ a]
  refine UO _ a.1.1 rfl a.1.2 a.2 _ _ ?_ (hg a).1 ?_
  · rw [Scheme.Hom.resLE_comp_ι_assoc, h1]
  · rw [Scheme.Hom.resLE_comp_ι_assoc, h2, (hg a).2]

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementSecondPolynomial
section
noncomputable section

namespace GlobalTheory.SplitTransfer

section Abstract

open Formalism.UG GlobalTheory.PRep

theorem heckeVec_indicator {G V ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {x : V} (hx : x ∈ fixed ρ K) {S : Set G} (hm : ∀ g ∈ S, ∀ k ∈ K, g * k ∈ S) (R : Finset ι)
    (g : ι → G) (hR : ∀ i ∈ R, g i ∈ S) (hR' : ∀ y ∈ S, ∃! i, i ∈ R ∧ (g i)⁻¹ * y ∈ K) :
    GlobalTheory.LFun.heckeVec ρ K (Set.indicator S 1) x = ∑ i ∈ R, ρ (g i) x := by
  classical
  have hinj : Set.InjOn (fun i : ι => (g i : G ⧸ K)) R := fun γ hγ δ hδ e =>
    (hR' _ (hR δ hδ)).unique ⟨hγ, QuotientGroup.eq.1 e⟩ ⟨hδ, by simp⟩
  rw [GlobalTheory.LFun.heckeVec, finsum_eq_sum_of_support_subset (s := R.image fun i : ι => (g i : G ⧸ K)),
    Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (g γ)
    rw [hk, Set.indicator_of_mem (hm _ (hR γ hγ) k k.2), map_mul, Module.End.mul_apply,
      GlobalTheory.LGrp.mem_fixed.1 hx _ k.2]
    simp
  · intro c hc
    have : c.out ∈ S := by
      by_contra h0
      exact hc (by simp [h0])
    obtain ⟨γ, ⟨h1, h2⟩, -⟩ := hR' _ this
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, h1, (QuotientGroup.eq.2 h2).trans c.out_eq'⟩)

end Abstract


open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.InertHeckeEigen Formalism.UG GlobalTheory.PRep GlobalTheory.DefU in
theorem heckeVec_eq_of_isCompAlong {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {U : Submodule ℂ (UA L n → ℂ)} (hU : IsAutRepU U) (w : HeightOneSpectrum (𝓞 L)) {H X : Type} [Group H]
    [AddCommGroup X] [Module ℂ X] {K : Subgroup H} (hK : IsCommensurated K) (p : locU n w →* H)
    (hp : Function.Surjective p) (σ : Representation ℂ H X) (hcomp : IsCompAlong U (locU n w) p σ) {h : H → ℂ}
    (hh : h ∈ Hecke ℂ K) {lam : ℂ} (hsat : ∀ v ∈ fixed σ K, v ≠ 0 → GlobalTheory.LFun.heckeVec σ K h v = lam • v)
    {φ : UA L n → ℂ} (hφ : φ ∈ U) (hfix : ∀ x : locU n w, p x ∈ K → RU L n x.val φ = φ) :
    GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) φ = lam • φ := by
  have hfin : {c : locU n w ⧸ K.comap p | h (p c.out) ≠ 0}.Finite :=
    finite_support_comp p hp hh.1 (Formalism.UG.P.finite_support_cosets hK hh.2)
  have hS : ∀ c : locU n w ⧸ K.comap p, (fun x => h (p x)) c.out ≠ 0 → c ∈ hfin.toFinset :=
    fun c hc => hfin.mem_toFinset.2 hc
  let T : (UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    ∑ c ∈ hfin.toFinset, h (p c.out) • (RU L n) (c.out : UA L n)
  have hT : ∀ x, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) (K.comap p) (fun x => h (p x)) x
      = T x := fun x => by
    rw [heckeVec_eq_sum _ _ _ _ hS x]
    simp [T, LinearMap.sum_apply]
  let Z : Submodule ℂ (UA L n → ℂ) :=
    fixed ((RU L n).comp (locU n w).subtype) (K.comap p) ⊓ LinearMap.ker (T - lam • LinearMap.id)
  have hZ' : ∀ x, x ∈ Z ↔ (∀ k ∈ K.comap p, RU L n (k : UA L n) x = x) ∧ T x = lam • x := fun x => by
    simp only [Z, Submodule.mem_inf, GlobalTheory.LGrp.mem_fixed, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  let π : AutSub L n := ⟨U, hU⟩
  obtain ⟨hσirr, f, hf0, hfm, hf⟩ := hcomp
  have hirr : Representation.IsIrreducible (σ.comp p) := by
    obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσirr
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
    obtain ⟨x, rfl⟩ := hp g
    exact hY x v hv
  let F : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints L n w
  have htop := (_root_.GlobalTheory.CuspRep.CompUniq.isotypic (UA L n) (locU n w) π.V X X π.rep (locU n w).subtype (σ.comp p) (σ.comp p)
    π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  let fi : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype) → X →ₗ[ℂ] (UA L n → ℂ) :=
    fun i => U.subtype ∘ₗ i.toLinearMap
  have hfi : ∀ i g u, fi i ((σ.comp p) g u) = (RU L n).comp (locU n w).subtype g (fi i u) := fun i g u =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining (σ.comp p) (π.rep.comp (locU n w).subtype) i g u)
  have hmem : φ ∈ ⨆ i, LinearMap.range (fi i) := by
    have : φ ∈ (⨆ i : Representation.IntertwiningMap (σ.comp p) (π.rep.comp (locU n w).subtype),
        LinearMap.range i.toLinearMap).map U.subtype := by
      rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
    simp only [fi, LinearMap.range_comp]
    rwa [Submodule.map_iSup] at this
  have hZ : ∀ i v, (∀ k ∈ (K.comap p : Set (locU n w)), (σ.comp p) k v = v) → fi i v ∈ Z := by
    intro i v hv
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]; exact Z.zero_mem
    have hvK : v ∈ fixed σ K := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      obtain ⟨x, rfl⟩ := hp k
      exact hv x hk
    refine (hZ' _).2 ⟨fun k hk => (hfi i k v).symm.trans (congrArg (fi i) (hv k hk)), ?_⟩
    have e2 := heckeVec_comp_surj p hp hh.1 σ hvK
    rw [heckeVec_eq_sum _ _ _ _ hS] at e2
    rw [hsat v hvK hv0] at e2
    rw [← hT (fi i v), heckeVec_eq_sum _ _ _ _ hS]
    calc _ = fi i (∑ c ∈ hfin.toFinset, h (p c.out) • (σ.comp p) c.out v) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_smul, hfi]
      _ = lam • fi i v := by rw [e2, map_smul]
  have hZK : ∀ z ∈ Z, ∀ k ∈ (K.comap p : Set (locU n w)), (RU L n).comp (locU n w).subtype k z = z :=
    fun z hz k hk => ((hZ' z).1 hz).1 k hk
  have hφZ := mem_of_mem_iSup ((RU L n).comp (locU n w).subtype) (σ.comp p) hirr fi hfi _ Z hZ hZK φ
    (fun k hk => hfix k hk) hmem
  rw [hT]
  exact ((hZ' φ).1 hφZ).2

end GlobalTheory.SplitTransfer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTransfer

theorem heckeVec_divInd {D : D7} [IsCMField D.host.E] {V : HSp D}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {j : UA D.host.E V.rank ≃ₜ* GA D V} {h₀ : GA D V} (hT : IsTransfer V θ j h₀)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {φ : UA D.host.E V.rank → ℂ}
    (hφ : ∀ x ∈ KP V.rank P, RU D.host.E V.rank x φ = φ) {d : List ℤ} {R : Finset (GA D V)}
    (hR : GlobalTheory.Hk3.SphOp V P d R) :
    GlobalTheory.LFun.heckeVec ((RU D.host.E V.rank).comp (locU V.rank P).subtype)
      ((GlobalTheory.LFun.KGL P (n := V.rank)).comap ((cLoc P).comp (locU V.rank P).subtype))
      (fun x => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) φ =
      ∑ γ ∈ R, RU D.host.E V.rank ((cj j h₀).symm γ) φ := by
  classical
  obtain ⟨h1, h2⟩ := hT.2.2.2.2.2.2.2 P d R hR
  let g : GA D V → locU V.rank P := fun γ =>
    if h : (cj j h₀).symm γ ∈ locU V.rank P then ⟨_, h⟩ else 1
  have hg : ∀ γ ∈ R, (g γ : UA D.host.E V.rank) = (cj j h₀).symm γ := fun γ hγ => by
    simp only [g, dif_pos (h1 γ hγ).1]
  have e : (fun x : locU V.rank P => divInd (Ov D.host.E P) d (((cLoc P).comp (locU V.rank P).subtype) x)) =
      Set.indicator {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)} 1 := by
    funext x
    by_cases hx : HasDiv (Ov D.host.E P) d (cLoc P x.val)
    · rw [Set.indicator_of_mem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_mem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
    · rw [Set.indicator_of_notMem (s := {x : locU V.rank P | HasDiv (Ov D.host.E P) d (cLoc P x.val)}) hx]
      exact Set.indicator_of_notMem (s := {g | HasDiv (Ov D.host.E P) d g}) hx _
  rw [e, heckeVec_indicator (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hφ k.val ⟨k.2, hk⟩) ?_ R g ?_ ?_]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [← hg γ hγ]
    rfl
  · intro x hx k hk
    have := GlobalTheory.SphGal.hasDiv_mul_mul hx (one_mem _) hk
    rw [one_mul] at this
    change HasDiv _ d (cLoc P (x.val * k.val))
    rw [map_mul]
    exact this
  · intro γ hγ
    change HasDiv _ d (cLoc P (g γ).val)
    rw [hg γ hγ]
    exact (h1 γ hγ).2
  · intro y hy
    obtain ⟨γ, ⟨a1, a2⟩, a3⟩ := h2 y.val y.2 hy
    refine ⟨γ, ⟨a1, ?_⟩, fun δ hδ => a3 δ ⟨hδ.1, ?_⟩⟩
    · change cLoc P ((g γ).val⁻¹ * y.val) ∈ GlobalTheory.LFun.KGL P (n := V.rank)
      rw [hg γ a1]
      exact a2.2
    · rw [← hg δ hδ.1]
      exact ⟨((g δ)⁻¹ * y).2, hδ.2⟩

end GlobalTheory.SplitTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SchAConj

open GlobalTheory.WeilM
open scoped Classical

def conjSchwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := star (f x)
  smooth' := Complex.conjLIE.toContinuousLinearEquiv.contDiff.comp f.smooth'
  decay' := by
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have h := Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (f : V → ℂ) x n
    have e : (fun x => star (f x)) = (Complex.conjLIE : ℂ → ℂ) ∘ (f : V → ℂ) := rfl
    show ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => star (f x)) x‖ ≤ C
    rw [e, h]
    exact hC x

theorem conjSchwartz_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSchwartz f x = star (f x) := rfl

theorem star_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AF F) → ℂ), Φ ∈ schA F κ → (fun x => star (Φ x)) ∈ schA F κ := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, hg, rfl⟩ := hΨ
    refine Submodule.subset_span ⟨conjSchwartz f, fun y => star (g y), ⟨hg.1.comp star, ?_⟩, ?_⟩
    · exact hg.2.comp_left (g := star) (star_zero ℂ)
    · funext x
      simp [pureA, conjSchwartz_apply, star_mul']
  | zero =>
    convert (schA F κ).zero_mem using 1
    funext x; simp
  | add Ψ Ψ' _ _ h h' =>
    have := (schA F κ).add_mem h h'
    convert this using 1
    funext x; simp [star_add]
  | smul c Ψ _ h =>
    have := (schA F κ).smul_mem (star c) h
    convert this using 1
    funext x; simp [star_mul']

end GlobalTheory.SchAConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZeroDimSupportEulerCharStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zero_dim_support_euler_char : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (F : Y.Modules) [IsFiniteQC F], suppDim F ≤ 0 → ∀ j : ℤ, (GlobalTheory.hdim k (GlobalTheory.twistZ F L j) 0 : ℤ) = GlobalTheory.chi k F := by
  first | exact @GlobalTheory.HSCore.hdim_zero_twistZ_eq_chi_of_suppDim_le_zero | exact GlobalTheory.HSCore.hdim_zero_twistZ_eq_chi_of_suppDim_le_zero | (intros; apply GlobalTheory.HSCore.hdim_zero_twistZ_eq_chi_of_suppDim_le_zero <;> assumption)
end

