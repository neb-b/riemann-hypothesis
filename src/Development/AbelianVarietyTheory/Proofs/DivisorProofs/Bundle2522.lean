module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedClosurePointFibreSquare
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_closure_pair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (q₁ q₂ : Sp K ⟶ Y.X), q₁ ≫ Y.str = q₂ ≫ Y.str → ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (p₁ p₂ : Z ⟶ Y.X) (h : p₁ ≫ Y.str = p₂ ≫ Y.str) (ζ : Sp K ⟶ Z), IsClosedImmersion (Limits.pullback.lift p₁ p₂ h) ∧ ζ ≫ p₁ = q₁ ∧ ζ ≫ p₂ = q₂ ∧ ζ (IsLocalRing.closedPoint K) = genericPoint Z := by
  intro F _ Y K _ q₁ q₂ hq
  let ξ : Sp K ⟶ Limits.pullback Y.str Y.str := Limits.pullback.lift q₁ q₂ hq
  let x := ξ (IsLocalRing.closedPoint K)
  let i := GlobalTheory.MixHt.cloι x
  have hw : (i ≫ Limits.pullback.fst Y.str Y.str) ≫ Y.str = (i ≫ Limits.pullback.snd Y.str Y.str) ≫ Y.str := by
    rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  have hl : Limits.pullback.lift _ _ hw = i := by
    apply Limits.pullback.hom_ext
    · exact Limits.pullback.lift_fst _ _ _
    · exact Limits.pullback.lift_snd _ _ _
  have : IsReduced (Sp K) := inferInstanceAs (IsReduced (Spec _))
  have hr : Set.range ξ ⊆ Set.range i := by
    rintro _ ⟨a, rfl⟩
    have ha : a = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    exact ⟨genericPoint _, by rw [ha, GlobalTheory.MixHt.cloι_genericPoint]⟩
  have hk : i.ker ≤ ξ.ker := ker_le_ker_of_range_subset_of_isReduced i ξ hr
  let ζ := IsClosedImmersion.lift i ξ hk
  have hζ : ζ ≫ i = ξ := IsClosedImmersion.lift_fac _ _ _
  refine ⟨GlobalTheory.MixHt.clo x, inferInstance, i ≫ Limits.pullback.fst _ _, i ≫ Limits.pullback.snd _ _, hw, ζ, ?_, ?_, ?_, ?_⟩
  · rw [hl]; infer_instance
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_fst _ _ _
  · rw [← Category.assoc, hζ]; exact Limits.pullback.lift_snd _ _ _
  · apply i.isClosedEmbedding.injective
    refine (Scheme.Hom.comp_apply ζ i _).symm.trans ?_
    rw [hζ, GlobalTheory.MixHt.cloι_genericPoint]

end GlobalTheory.FlagPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularLocalModelGraphOfPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

theorem GlobalTheory.GraphLocal.exists_locModel_graph : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin (k + 1) → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k + 1 ∧
    (∀ e ∈ E.ring, algebraMap (K ⊗[ℂ] κ') L (e ⊗ₜ 1) ∈ Q) ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1) = q * (z 0 : L) ^ E.ord g) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M ⊔ Ideal.span {z 0}) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) =
        ((q : L) * (z 0 : L) ^ E.formOrd (dForm (algebraMap ℂ K) x)) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO' hz hcompat hC hfrac E hER hcentre
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ _
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨zR, hzR⟩ := _root_.GlobalTheory.GraphLocal.exists_trBasis_lift k R π hfrac hz
  obtain ⟨𝔭, h𝔭⟩ := Ideal.nonempty_minimalPrimes (GlobalTheory.T.placeGraphIdealTensor_ne_top (κ' := κ') R π ρ E hcompat hC hfrac hER hcentre)
  haveI : 𝔭.IsPrime := h𝔭.1.1
  have hle : graphIdeal E R π ρ ≤ 𝔭 := h𝔭.1.2
  have hQ : IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor E 𝔭 hO'
  letI := hQ.isLocalRing
  have hmax := GlobalTheory.T.graphIdeal_localization_maximalIdeal_eq_span (L := L) k R π ρ E hER t zR 𝔭 hO' hcompat hC hfrac hcentre ht hzR h𝔭
  have hdim := GlobalTheory.T.ringKrullDim_localization_graphIdeal_minimalPrime (L := L) k R π ρ E 𝔭 hO' hcompat hC hfrac hER hcentre hz h𝔭
  have hz0 : ((toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0) : locAt (L := L) 𝔭) : L) =
      algebraMap (K ⊗[ℂ] κ') L ((t : K) ⊗ₜ 1) := by
    simp [gens]
  refine ⟨locAt (L := L) 𝔭, hQ, fun i => toQ 𝔭 (gens E R π ρ hER t zR i), hmax, hdim, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact (toQ (L := L) 𝔭 ⟨e ⊗ₜ 1, tmul_mem (A := placeAlg E) he 1⟩).2
  · intro g hg
    rw [hz0]
    exact GlobalTheory.T.exists_isUnit_mul_zpow_uniformiser_tmul E 𝔭 t hinj ht g hg
  · intro b hb
    refine ⟨toQ 𝔭 ⟨1 ⊗ₜ b, tmul_mem (one_mem (placeAlg E)) b⟩, isUnit_toQ 𝔭 hinj ?_, rfl⟩
    intro h
    apply one_notMem 𝔭
    have h2 := 𝔭.mul_mem_right ⟨(1 : K) ⊗ₜ b⁻¹, tmul_mem (one_mem (placeAlg E)) b⁻¹⟩ h
    convert h2 using 1
    apply Subtype.ext
    simp [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hb, Algebra.TensorProduct.one_def]
  · intro l a b hs
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, isUnit_toQ 𝔭 hinj (GlobalTheory.T.sum_tmul_notMem_prime_of_graph_image_ne_zero R π ρ E 𝔭 hle hER l a b ⟨_, hw⟩ rfl hs), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  · intro M l a b hJ
    have hw : ∑ i, (a i : K) ⊗ₜ[ℂ] b i ∈ tens (κ' := κ') (placeAlg E) :=
      Subalgebra.sum_mem _ fun i _ => tmul_mem (hER _ (a i).2) (b i)
    refine ⟨toQ 𝔭 ⟨_, hw⟩, by simp [map_sum], ?_⟩
    have h1 := GlobalTheory.T.graphJets_mem_pow_sup_uniformiser R π ρ E 𝔭 t hle ht hcompat hC hfrac hER hcentre M l a b ⟨_, hw⟩ rfl hJ
    have h2 := Ideal.mem_map_of_mem (toQ (L := L) 𝔭) h1
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h2
    have h3 : Ideal.map (toQ (L := L) 𝔭) 𝔭 ^ M ⊔ Ideal.span {toQ (L := L) 𝔭 ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩} ≤
        IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ^ M ⊔
          Ideal.span {toQ (L := L) 𝔭 (gens E R π ρ hER t zR 0)} :=
      sup_le_sup (Ideal.pow_right_mono (map_le_maximalIdeal 𝔭 hinj) M) le_rfl
    exact h3 h2
  · obtain ⟨y, q, hy, hq, e⟩ := GlobalTheory.T.exists_freeGenerator_topForms_tensorLocalization_order n k' x τ' E 𝔭 t hQ.const_mem hx hτ hO' ht
    refine ⟨y, q, hy, hq, ?_⟩
    rw [hz0]
    exact e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedValueAtOrigin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.OrigValExists

theorem mem_of_closed {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (U : X.Opens)
    (h : f (closedPoint R) ∈ U) (z : Sp R) : f z ∈ U := by
  have : f ⁻¹ᵁ U = ⊤ := (closedPoint_mem_iff (f ⁻¹ᵁ U)).1 h
  show z ∈ f ⁻¹ᵁ U
  rw [this]; trivial

theorem exists_stalkOf {R : Type} [CommRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (U : X.Opens)
    (h : ∀ z, f z ∈ U) (a : Γ(X, U)) : ∃ r : R, ∀ z, gs f z U a = stalkOf z r := by
  have hle : (⊤ : (Sp R).Opens) ≤ f ⁻¹ᵁ U := fun z _ => h z
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Sp R).presheaf.map (homOfLE hle).op).hom ((f.app U).hom a)), fun z => ?_⟩
  rw [gs_eq f z U (h z)]
  have e : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x :=
    fun x => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply x
  refine Eq.trans ?_ (congrArg ((Sp R).presheaf.germ ⊤ z trivial).hom (e _)).symm
  exact (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE hle) z trivial _).symm

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (α : D.X)

theorem unit_fam_zero : unitW D.P.A ≫ D.famφB α 0 = idW R ≫ eSec D.P.A :=
  (Category.comp_id _).trans (Category.id_comp _).symm

theorem unit_fam_one : unitW D.P.A ≫ D.famφB α 1 = unitW D.P.A ≫ D.famφB α 2 := by
  change η[D.P.A].left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = η[D.P.A].left ≫ (toUnit D.P.A ≫ D.c α).left
  rw [← Over.comp_left, ← Over.comp_left]; congr 1
  simp only [padd, comp_lift_assoc, Category.comp_id]
  have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Sp R)))) (η[D.P.A] ≫ toUnit D.P.A ≫ D.c α)
  rwa [Category.id_comp] at this

theorem unit_fam_three : unitW D.P.A ≫ D.famφB α 3 = idW R ≫ eSec D.P.A := by
  refine Eq.trans ?_ (Category.id_comp _).symm
  change η[D.P.A].left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = η[D.P.A].left
  rw [← Over.comp_left]; congr 1
  rw [← Category.assoc, Subsingleton.elim (η[D.P.A] ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

theorem trF_unit (k : ℕ) (z : Sp R) (J I : (Sp R ⟶ D.P.A.left) → D.P.L.ι) :
    trF (L := D.P.L) (D.famφB α) (DegPre.famε k) (unitW D.P.A) z (fun i => J (unitW D.P.A ≫ D.famφB α i))
      (fun i => I (unitW D.P.A ≫ D.famφB α i)) =
    trF (L := D.P.L) (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) (idW R) z (fun _ => J (idW R ≫ eSec D.P.A))
      (fun _ => I (idW R ≫ eSec D.P.A)) ^ k := by
  let h : (Sp R ⟶ D.P.A.left) → ((Sp R).presheaf.stalk z)ˣ :=
    fun ψ => gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U (I ψ)) (D.P.L.g (J ψ) (I ψ))
  show ∏ i, h (unitW D.P.A ≫ D.famφB α i) ^ DegPre.famε k i = (∏ _i : PUnit, h (idW R ≫ eSec D.P.A) ^ (1 : ℤ)) ^ k
  rw [Fin.prod_univ_four, unit_fam_zero, unit_fam_one, unit_fam_three, Fintype.prod_unique]
  generalize h (idW R ≫ eSec D.P.A) = A
  generalize h (unitW D.P.A ≫ D.famφB α 2) = B
  show A ^ ((k : ℤ) - 1) * B ^ (1 : ℤ) * B ^ (-1 : ℤ) * A ^ (1 : ℤ) = (A ^ (1 : ℤ)) ^ k
  rw [zpow_sub_one, zpow_natCast, zpow_neg, zpow_one, zpow_one, mul_inv_cancel_right, inv_mul_cancel_right]

end GlobalTheory.Mum.OrigValExists

namespace GlobalTheory.Mum
open OrigValExists

theorem exists_origVal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (k : ℕ) (α : D.X) (b : D.SecB k α), ∃ v : R, OrigVal D b v := by
  intro R _ _ _ D k α b
  obtain ⟨I, hI₀, -⟩ := exists_good D.P.L D.P.isLB (Z := Sp R) (closedPoint R) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have hI : ∀ z, Good D.P.L z I := fun z ψ => mem_of_closed ψ _ (hI₀ ψ) z
  obtain ⟨a, ha⟩ := exists_stalkOf (unitW D.P.A) _ (fun z => (hI z).mem (D.famφB α) (unitW D.P.A))
    (b.f (fun i => I (unitW D.P.A ≫ D.famφB α i)))
  obtain ⟨u, hu⟩ := exists_stalkOf (idW R) _ (fun z => (hI z).mem (K := PUnit) (fun _ => eSec D.P.A) (idW R))
    ((D.rig.s (fun _ => I (idW R ≫ eSec D.P.A)))⁻¹).val
  refine ⟨a * u ^ k, fun z J hJ => ?_⟩
  have e₁ : sval b (unitW D.P.A) z J = _ * sval b (unitW D.P.A) z I :=
    sec_trans b (unitW D.P.A) z (hJ.mem _ _) ((hI z).mem _ _)
  have e₂ : val D.rig (idW R) z J = _ * val D.rig (idW R) z I :=
    gen_trans D.rig_gen (idW R) z (hJ.mem _ _) ((hI z).mem _ _)
  have e₃ : sval b (unitW D.P.A) z I = stalkOf z a := ha z
  have e₄ : stalkOf z u = ((val D.rig (idW R) z I)⁻¹).val :=
    (hu z).symm.trans ((gs_unit (idW R) z _ ((hI z).mem (K := PUnit) (fun _ => eSec D.P.A) (idW R)) _).trans
      (congrArg Units.val (map_inv _ _)))
  rw [e₁, e₂, e₃, trF_unit, map_mul, map_pow, e₄]
  generalize trF (K := PUnit) _ _ _ _ _ _ = A
  generalize val D.rig (idW R) z I = B
  rw [_root_.mul_assoc, ← mul_pow, ← Units.val_mul, _root_.mul_comm A B, inv_mul_cancel_left, Units.val_pow_eq_pow_val, _root_.mul_comm]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDifferenceOneCochain
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem isSec_pull {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (n : ℕ) (b : Fn0 A)
    {D : Type} [CommRing D] [Algebra R D] {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (x : Pt A D) (s : RootFn A D) (hs : IsSec n b x s) :
    IsSec n b (D := D') (spOver φ ≫ x) (fun E _ _ ψ z ↦ s E (ψ.comp φ) z) := by
  refine ⟨?_, ?_⟩
  · intro E _ _ E' _ _ α β z hz
    have hz' : z ^ n = spOver (α.comp φ) ≫ x := by rw [hz, ← spOver_comp, Category.assoc]
    exact hs.1 E E' (α.comp φ) β z hz'
  · intro E _ _ α z w hz hw
    have hz' : z ^ n = spOver (α.comp φ) ≫ x := by rw [hz, ← spOver_comp, Category.assoc]
    exact hs.2 E (α.comp φ) z w hz' hw

theorem exists_isSecDiff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∃ u : Fn1 A, IsSecDiff n S u := by
  intro R _ A _ _ n hR b _ S hS
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D),
      let x' : Pt A D' := spOver φ ≫ x
      ∃ e : D', ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E)
        (z : Pt A E), z ^ n = spOver ψ ≫ spOver φ ≫ x →
          S D' x' E ψ z - S D x E (ψ.comp φ) z = ψ e := by
    intro D _ _ D' _ _ φ x x'
    exact (isSec_sub_existsUnique R A n hR b D' x' (S D' x')
      (fun E _ _ ψ z ↦ S D x E (ψ.comp φ) z) (hS D' x')
      (isSec_pull n b φ x (S D x) (hS D x))).exists
  refine ⟨fun D _ _ D' _ _ φ x ↦ Classical.choose (key D D' φ x), ?_⟩
  intro D _ _ D' _ _ φ x E _ _ ψ z hz
  exact (Classical.choose_spec (key D D' φ x) E ψ z hz).symm

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open GlobalTheory.ArInt

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.Mix.exists_sec_bc : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ), (∀ x, IsIso (j.stalkMap x)) → ∀ (M : MLine p (τ.comp (algebraMap k K))) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), j (genericPoint G) = genericPoint X → ∃ (s' : (M.bc hp.w τ).B.Sec) (hs' : genericPoint G ∈ nonzeroLocus s'), nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s ∧ (∀ x, (divOfSec (M.bc hp.w τ).φ.isLB s' hs').mult x = (divOfSec M.φ.isLB s hs).mult (j x)) ∧ ∀ y, (M.bc hp.w τ).logSec s' y = M.logSec s (bcPt hp.w τ y) := by
  intro k K _ _ _ _ X G _ _ _ _ p q j hp τ hiso M s hs hj
  let s' : (M.bc hp.w τ).B.Sec := Cartier.secPull s j
  have hnz : nonzeroLocus s' = j ⁻¹ᵁ nonzeroLocus s := Cartier.nonzeroLocus_secPull s j
  have hs' : genericPoint G ∈ nonzeroLocus s' := by
    rw [hnz]
    show j (genericPoint G) ∈ nonzeroLocus s
    rw [hj]
    exact hs
  refine ⟨s', hs', hnz, fun x => ?_, fun y => ?_⟩
  · have := hiso x
    let e : X.presheaf.stalk (j x) ≃+* G.presheaf.stalk x :=
      (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    have hc : Order.coheight x = Order.coheight (j x) := by
      have := ringKrullDim_eq_of_ringEquiv e
      rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
      exact_mod_cast this.symm
    by_cases h1 : Order.coheight x = 1
    swap
    · rw [not_not.1 (mt CartierDiv.coheight_eq_one_of_mult_ne_zero h1),
        not_not.1 (mt CartierDiv.coheight_eq_one_of_mult_ne_zero (hc ▸ h1))]
    obtain ⟨i, hi⟩ := Geo.Tor.exists_chart M.φ.isLB (j x)
    have h₁ : x ∈ (M.bc hp.w τ).B.U fun _ => i := Set.mem_iInter.2 fun _ => hi
    rw [mult_divOfSec h1 h₁, mult_divOfSec (hc ▸ h1) hi]
    have hg : G.presheaf.germ _ x h₁ (s'.f fun _ => i) =
        j.stalkMap x (X.presheaf.germ _ _ hi (s.f i)) := by
      rw [Scheme.Hom.germ_stalkMap_apply]
      exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hg]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_map_ringEquiv e _)
  · have hy := mem_pick M.φ.isLB (bcPt hp.w τ y)
    have hy' : y ∈ ptsIn q τ ((M.bc hp.w τ).B.U fun _ => pick M.φ.isLB (bcPt hp.w τ y)) := by
      exact mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hy)
    have e1 : secVal q τ s' (fun _ => pick M.φ.isLB (bcPt hp.w τ y)) y =
        secVal p (τ.comp (algebraMap k K)) s (pick M.φ.isLB (bcPt hp.w τ y)) (bcPt hp.w τ y) := by
      exact (ev_res (Cartier.pull_U M.B j _).le hy' _).trans (valR_comp y.1 j _ _).symm
    simp only [MLine.logSec]
    rw [Weight.nsq_eq _ (secVal_mem s') hy', e1]
    simp [MLine.bc, Weight.linComb, Weight.nsq]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingClosedFibreOfThreeLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ClosedFibreBpf

theorem thick_zero_apply (R : Type) [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) :
    thick R (maximalIdeal R) 0 z = closedPoint R := by
  show (Spec.map _).base z = _
  rw [Spec.map_base]
  apply PrimeSpectrum.ext
  show Ideal.comap _ z.asIdeal = maximalIdeal R
  symm
  apply (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (by
    haveI := z.isPrime
    exact Ideal.IsPrime.ne_top inferInstance)
  intro a ha
  show _ ∈ z.asIdeal
  have : (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) a = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; simpa using ha
  rw [show (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))).hom a = 0 from this]
  exact z.asIdeal.zero_mem

theorem exists_sec_ne_zero_at : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ k : ℕ, 3 ≤ k → ∀ y : (thickObj R (maximalIdeal R) 0 G).left, ∃ (s : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  intro R _ _ _ hB D A G _ _ hG U k hk y
  obtain ⟨σ, j, hx⟩ := _root_.GlobalTheory.Mum.exists_secB_zero_mem_basicOpen R hB D k (by omega) ((U.gt 0).pG.left y) (by
    have h := congrArg (fun f => f.base y) (Over.w (U.gt 0).pG)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    exact h.trans (thick_zero_apply R _))
  obtain ⟨s, f, hf0, hfα, hexp⟩ := _root_.GlobalTheory.Mum.LeadZero.exists_expandsAt_lead_zero R hB D A G hG U k (by omega) σ
  obtain ⟨i, hi⟩ := _root_.GlobalTheory.Mum.ExpandNonzero.nonzero_of_expandsAt_zero R D A G U.toUnifPre k s f hexp hfα y ⟨j, by
    subst hf0
    rw [← Scheme.preimage_basicOpen]
    exact hx⟩
  exact ⟨s, i, hi⟩

end GlobalTheory.Mum.ClosedFibreBpf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPointwiseOneCocycleOpenCoverStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pointwiseOneCocycle_openCover :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u →
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
          ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
            (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'),
            Sm (D := E) W (spOver ψ ≫ x) →
              σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) :=
  @GlobalTheory.PtExt.CocSec.exists_section
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackCommutingEndomorphismGeneraStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pullback_commuting_endomorphism_generator : ∀ {X Y : Scheme.{0}} (L : LB X), L.IsLB → ∀ (β : Y ⟶ X) (g : Y ⟶ Y) (h : X ⟶ X), g ≫ β = β ≫ h →
    ∀ (k k' : ℕ) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, h] ![(k' : ℤ), -(k : ℤ)])), u.IsGen → ∀ (σ : SecK L β k),
    ∃ σ₂ : SecK L β k', ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval σ₂ r z J = (val u (r ≫ β) z J).val * sval σ (r ≫ g) z J := by
  first | exact @GlobalTheory.Mum.exists_secK_pullMul_gen | exact GlobalTheory.Mum.exists_secK_pullMul_gen | (intros; apply GlobalTheory.Mum.exists_secK_pullMul_gen <;> assumption)
end

