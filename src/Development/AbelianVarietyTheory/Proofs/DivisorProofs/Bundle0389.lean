module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PiTensorLiftCompSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerNeBotAndNotEffCartier
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

noncomputable section
namespace GlobalTheory.NotCartier

theorem ringKrullDim_stalk_le_one {X : Scheme.{0}} [IsLocallyNoetherian X] (J : X.IdealSheafData) (x : X)
    (hx : x ∈ J.support) (hmin : ∀ z ∈ J.support, z ⤳ x → z = x) (V : X.affineOpens) (hxV : x ∈ V.1)
    (hP : (J.ideal V).IsPrincipal) : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  haveI := IsLocallyNoetherian.component_noetherian V
  have hV : IsAffineOpen V.1 := V.2
  let p := hV.primeIdealOf ⟨x, hxV⟩
  let _ : Algebra Γ(X, V.1) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  have hp : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hsupp : ∀ q : Spec Γ(X, V.1), hV.fromSpec q ∈ J.support ↔ J.ideal V ≤ q.asIdeal := by
    intro q
    have hqV : hV.fromSpec q ∈ V.1 := (Set.ext_iff.1 hV.range_fromSpec _).1 ⟨q, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hqV]
    change q ∈ hV.fromSpec ⁻¹' X.zeroLocus (J.ideal V : Set Γ(X, V.1)) ↔ _
    rw [hV.fromSpec_preimage_zeroLocus]
    exact Iff.rfl
  have hmem : p.asIdeal ∈ (J.ideal V).minimalPrimes := by
    refine ⟨⟨p.isPrime, (hsupp p).1 (hp ▸ hx)⟩, fun q hq hqp => ?_⟩
    let y : PrimeSpectrum Γ(X, V.1) := ⟨q, hq.1⟩
    have hsp : hV.fromSpec y ⤳ x := by
      have := ((PrimeSpectrum.le_iff_specializes y p).1 hqp).map hV.fromSpec.continuous
      rwa [hp] at this
    have hyx : hV.fromSpec y = hV.fromSpec p := (hmin _ ((hsupp y).2 hq.2) hsp).trans hp.symm
    have := congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hyx)
    exact le_of_eq this.symm
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)]
  exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmem

end GlobalTheory.NotCartier

namespace GlobalTheory.NotCartier

theorem ker_ne_bot_and_not_effCartier : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y)
    [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) →
    i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  intro W Y _ _ i _ hdim
  set y := i (genericPoint W) with hy
  have hsub : (i.ker.support : Set Y) ⊆ closure {y} := by
    rw [Scheme.Hom.support_ker]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ closure {genericPoint W} := by
      rw [(genericPoint_spec W).def]; trivial
    exact specializes_iff_mem_closure.1 ((specializes_iff_mem_closure.2 hw).map i.continuous)
  have hyS : y ∈ i.ker.support := by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]; exact subset_closure ⟨_, rfl⟩
  have hmin : ∀ z ∈ i.ker.support, z ⤳ y → z = y := fun z hz hzy =>
    (hzy.antisymm (specializes_iff_mem_closure.2 (hsub hz))).eq
  have hlt : ¬ ringKrullDim (Y.presheaf.stalk y) ≤ 1 := fun h => by
    have := hdim.trans h
    exact absurd this (by decide)
  refine ⟨fun hbot => ?_, fun U hyU hC => ?_⟩
  · obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine hlt (ringKrullDim_stalk_le_one i.ker y hyS hmin ⟨V, hV⟩ hyV ?_)
    rw [hbot, Scheme.IdealSheafData.ideal_bot]
    exact bot_isPrincipal
  · let x : U.toScheme := ⟨y, hyU⟩
    obtain ⟨V, f, hxV, -, hf⟩ := hC x
    have hxS : x ∈ (i.ker.comap U.ι).support := by
      rw [Scheme.IdealSheafData.support_comap]; exact hyS
    have hminU : ∀ z ∈ (i.ker.comap U.ι).support, z ⤳ x → z = x := by
      intro z hz hzx
      rw [Scheme.IdealSheafData.support_comap] at hz
      exact Subtype.ext (hmin _ hz (hzx.map U.ι.continuous))
    have h1 := ringKrullDim_stalk_le_one _ x hxS hminU V hxV ⟨⟨f, hf⟩⟩
    rw [← ringKrullDim_eq_of_ringEquiv (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv] at h1
    exact hlt h1

end GlobalTheory.NotCartier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRetractionFgStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_retraction_fg_of_adjoin_finset : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  first | (exact @GlobalTheory.ker_retraction_fg) | (exact GlobalTheory.ker_retraction_fg) | (intros; apply GlobalTheory.ker_retraction_fg  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPower
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.GmStep.LevelIso

theorem T_eq_unit_zpow (B : Type) [CommRing B] (m : ℤ) :
    (LaurentPolynomial.T m : LaurentPolynomial B) =
      ((laurentVarUnit B ^ m : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) := by
  have h := laurentMap_T (RingHom.id B) m
  rw [laurentMap, LaurentPolynomial.eval₂_T] at h
  exact h.symm

theorem laurent_ringHom_ext {B R : Type} [CommRing B] [CommRing R] {φ ψ : LaurentPolynomial B →+* R}
    (hC : φ.comp LaurentPolynomial.C = ψ.comp LaurentPolynomial.C)
    (hT : φ (LaurentPolynomial.T 1) = ψ (LaurentPolynomial.T 1)) : φ = ψ := by
  have hu : Units.map φ.toMonoidHom (laurentVarUnit B) = Units.map ψ.toMonoidHom (laurentVarUnit B) :=
    Units.ext hT
  have e : ∀ (χ : LaurentPolynomial B →+* R) (m : ℤ),
      χ ((laurentVarUnit B ^ m : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) =
        ((Units.map χ.toMonoidHom (laurentVarUnit B) ^ m : Rˣ) : R) := by
    intro χ m
    rw [← map_zpow]
    rfl
  have hTm : ∀ m : ℤ, φ (LaurentPolynomial.T m) = ψ (LaurentPolynomial.T m) := fun m => by
    rw [T_eq_unit_zpow, e φ, e ψ, hu]
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add (f := _), map_add (f := _), hp, hr]
  | C_mul_T n b => rw [map_mul, map_mul, hTm n, ← RingHom.comp_apply, hC, RingHom.comp_apply]

theorem laurentMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (laurentMap g).comp (laurentMap f) = laurentMap (g.comp f) :=
  laurent_ringHom_ext (RingHom.ext fun a => by simp [laurentMap_C])
    (by rw [RingHom.comp_apply, laurentMap_T, laurentMap_T, laurentMap_T])

theorem tensorPow_univ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (R : Type) [CommRing R]
    (g : Fin (k + 1) → (B →+* R)) (hg : ∀ j, (g j).comp (algebraMap A B) = (g 0).comp (algebraMap A B)) :
    ∃! φ : PiTensorProduct A (fun _ : Fin (k + 1) => B) →+* R,
      ∀ j, φ.comp (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom = g j := by
  classical
  letI : Algebra A R := ((g 0).comp (algebraMap A B)).toAlgebra
  let g' : Fin (k + 1) → (B →ₐ[A] R) := fun j => ⟨g j, fun r => RingHom.congr_fun (hg j) r⟩
  refine ⟨(GlobalTheory.piTensorLift g').toRingHom, fun j => ?_, fun ψ hψ => ?_⟩
  · ext x
    exact GlobalTheory.piTensorLift_single g' j x
  · have hc : ∀ r : A, ψ (algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r) = algebraMap A R r := by
      intro r
      have h1 : algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r =
          PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0 (algebraMap A B r) :=
        ((PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0).commutes r).symm
      rw [h1]
      exact RingHom.congr_fun (hψ 0) (algebraMap A B r)
    let ψ' : PiTensorProduct A (fun _ : Fin (k + 1) => B) →ₐ[A] R := ⟨ψ, hc⟩
    have : ψ' = GlobalTheory.piTensorLift g' := PiTensorProduct.algHom_ext fun j => by
      ext x
      change ψ _ = _
      rw [AlgHom.comp_apply, GlobalTheory.piTensorLift_single]
      exact RingHom.congr_fun (hψ j) x
    exact congrArg AlgHom.toRingHom this

theorem laurent_univ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (R : Type) [CommRing R] (g : Fin (k + 1) → (LaurentPolynomial B →+* R))
    (hg : ∀ j, (g j).comp (laurentMap a) = (g 0).comp (laurentMap a)) :
    ∃! φ : LaurentPolynomial T →+* R, ∀ j, φ.comp (laurentMap (ι j)) = g j := by
  have hT : ∀ j, g j (LaurentPolynomial.T 1) = g 0 (LaurentPolynomial.T 1) := fun j => by
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.T 1)
    rwa [RingHom.comp_apply, RingHom.comp_apply, laurentMap_T] at this
  obtain ⟨ψ, hψ, hψu⟩ := hu R (fun j => (g j).comp LaurentPolynomial.C) (fun j => by
    refine RingHom.ext fun x => ?_
    have := RingHom.congr_fun (hg j) (LaurentPolynomial.C x)
    simpa [laurentMap_C] using this)
  let u : Rˣ := Units.map (g 0).toMonoidHom (laurentVarUnit B)
  refine ⟨LaurentPolynomial.eval₂ ψ u, fun j => ?_, fun φ hφ => ?_⟩
  · apply laurent_ringHom_ext
    · refine RingHom.ext fun b => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, laurentMap_C, LaurentPolynomial.eval₂_C]
      exact RingHom.congr_fun (hψ j) b
    · rw [RingHom.comp_apply, laurentMap_T, LaurentPolynomial.eval₂_T, zpow_one, hT j]
      rfl
  · have hC : φ.comp LaurentPolynomial.C = ψ := hψu _ (fun j => by
      refine RingHom.ext fun b => ?_
      have := RingHom.congr_fun (hφ j) (LaurentPolynomial.C b)
      simpa [laurentMap_C] using this)
    apply laurent_ringHom_ext
    · refine RingHom.ext fun t => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, LaurentPolynomial.eval₂_C, ← hC]
      rfl
    · rw [LaurentPolynomial.eval₂_T, zpow_one]
      have := RingHom.congr_fun (hφ 0) (LaurentPolynomial.T 1)
      rw [RingHom.comp_apply, laurentMap_T] at this
      rw [this]
      rfl

end GlobalTheory.EtC.GmStep.LevelIso

namespace GlobalTheory.EtC.GmStep.LevelIso

theorem level_iso : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ),
  ∃ (e0 : yoneda.obj (Spec (CommRingCat.of (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) ≅ (cech (baseHom A A')).obj (op ⦋k⦌))
    (e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≅
      (cech (laurentHom A A')).obj (op ⦋k⦌)),
    e.hom ≫ (cechC A A').app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≫ e0.hom ∧
    e.hom ≫ (cechAug (laurentHom A A')).app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) := by
  intro A A' _ _ _ k
  let ι : Fin (k + 1) → (A' →+* PiTensorProduct A (fun _ : Fin (k + 1) => A')) := fun j =>
    (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => A') j).toRingHom
  have hιA : ∀ j, (ι j).comp (algebraMap A A') = algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) :=
    fun j => RingHom.ext fun x => (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => A') j).commutes x
  have hι : ∀ j, (ι j).comp (algebraMap A A') = (ι 0).comp (algebraMap A A') := fun j => by rw [hιA, hιA]
  have hu := tensorPow_univ A A' k
  obtain ⟨e0, he0⟩ := GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback A A' _ (algebraMap A A') k ι hι hu
  have hι' : ∀ j, (laurentMap (ι j)).comp (laurentMap (algebraMap A A')) =
      (laurentMap (ι 0)).comp (laurentMap (algebraMap A A')) := by
    intro j; rw [laurentMap_comp, laurentMap_comp, hι j]
  obtain ⟨e, he⟩ := GlobalTheory.SpecWidePullback.yoneda_spec_isoWidePullback (LaurentPolynomial A) (LaurentPolynomial A')
    (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) (laurentMap (algebraMap A A')) k
    (fun j => laurentMap (ι j)) hι' (laurent_univ A A' _ (algebraMap A A') k ι (fun R _ g hg => hu R g hg))
  refine ⟨e0, e, ?_, ?_⟩
  · change e.hom ≫ WidePullback.lift _ _ _ = _
    apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, WidePullback.lift_π, Arrow.mk_hom, laurentHom, baseHom]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (he j)).trans ?_)
      refine Eq.trans ?_ (congrArg (_ ≫ ·) (he0 j)).symm
      simp only [constSq, Arrow.homMk_left, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        laurentMap_comp_C]
    · simp only [Category.assoc, WidePullback.lift_base, Arrow.mk_hom, laurentHom, baseHom]
      rw [← WidePullback.π_arrow _ 0]
      simp only [Category.assoc]
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (he 0)).trans ?_)
      refine Eq.trans ?_ ((congrArg (_ ≫ ·) (((congrArg (· ≫ yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))) (he0 0)).symm.trans (Category.assoc _ _ _)).trans (congrArg (e0.hom ≫ ·) (WidePullback.π_arrow _ 0)))).trans (Category.assoc _ _ _).symm)
      simp only [constSq, Arrow.homMk_right, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        laurentMap_comp_C]
      congr 3
      exact RingHom.ext fun x => by simp [laurentMap_C]
  · change e.hom ≫ WidePullback.base _ = _
    rw [← WidePullback.π_arrow _ 0, ← Category.assoc, he 0]
    simp only [laurentHom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, laurentMap_comp, hιA 0]

end GlobalTheory.EtC.GmStep.LevelIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFormalGroupDeterminantPowDepthOfRadii
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthCount

variable {C : Type} [Field C]

theorem prod_X_col {i : ℕ} (b : Fin i) (d : Fin i →₀ ℕ) :
    (d.prod fun s e => (X (⟨b, s⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ e)
      = monomial (Finsupp.mapDomain (Sigma.mk b) d) 1 := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add s n d hs hn ih =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single, Finsupp.prod_single_index (by simp), X_pow_eq,
      monomial_mul_monomial, one_mul]

theorem hasSubst_col {i : ℕ} (b : Fin i) :
    HasSubst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
  hasSubst_of_constantCoeff_zero (fun a => constantCoeff_X _)

theorem constantCoeff_col {i : ℕ} (b : Fin i) (g : MvPowerSeries (Fin i) C)
    (hg : constantCoeff g = 0) :
    constantCoeff (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)
      = 0 := by
  have hs := hasSubst_col (C := C) b
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst hs]
  convert finsum_zero with d
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · have hd : d = 0 := by
      have h' := h.symm
      rw [← Finsupp.mapDomain_zero (f := Sigma.mk b)] at h'
      exact Finsupp.mapDomain_injective (sigma_mk_injective (i := b)) h'
    subst hd
    simp [hg]
  · simp

theorem wt_col {i : ℕ} (v : AddValuation C (WithTop ℝ)) (ρ : Fin i → ℝ) (b : Fin i)
    (g : MvPowerSeries (Fin i) C) (hg : OrdGe v ρ g 0) (β : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    (((0 - β.sum (fun y e => ρ y.2 * (e : ℝ)) : ℝ)) : WithTop ℝ) ≤
      v (coeff β (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)) := by
  have hs := hasSubst_col (C := C) b
  rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs g β)]
  apply v.map_le_sum
  intro d _
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · rw [mul_one]
    subst h
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring),
      Finsupp.sum_fintype _ _ (by simp)]
    exact hg d
  · simp

theorem depth_count : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (ρ : Fin i → ℝ) (t : Fin d → MvPowerSeries (Fin i) C) (B : ℝ), (∀ a, constantCoeff (t a) = 0) → (∀ a, OrdGe v ρ (t a) 0) → (∀ α ∈ (detPow C i c).support, (((B + c * ∑ a, ρ a : ℝ)) : WithTop ℝ) ≤ v ((detPow C i c).coeff α * mfact α)) → ∀ f : MvPowerSeries (Σ _ : Fin i, Fin d) C, MvIsInt v f → ((B : ℝ) : WithTop ℝ) ≤ v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f)) := by
  intro C _ _ v i d c ρ t B ht0 ht hP f hf
  have hw := GlobalTheory.WeightSubst.weight_subst_nonneg C v (Σ _ : Fin i, Fin i) (Σ _ : Fin i, Fin d)
    (fun y => ρ y.2) f
    (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i =>
      (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) hf
    (fun x => constantCoeff_col x.1 _ (ht0 x.2)) (fun x => wt_col v ρ x.1 _ (ht x.2))
  unfold derivAt0
  apply v.map_le_sum
  intro α hα
  have hrow := ((_root_.GlobalTheory.DetPowShape.detPow_shape C i c).2.2.2 α hα).1
  rw [v.map_mul]
  have e : B = (B + c * ∑ a, ρ a) + (0 - α.sum (fun y e => ρ y.2 * (e : ℝ))) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hc : ∀ a : Fin i, (∑ b : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c := fun a => by
      exact_mod_cast hrow a
    simp_rw [hc]
    rw [← Finset.sum_mul]
    ring
  rw [e, WithTop.coe_add]
  exact add_le_add (hP α hα) (hw α)

end GlobalTheory.DepthCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftTranslateSmoothCommuteLeftInvariantOps
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem isSmoothFun_leftTranslate (h : IsExpLieAlgebra G 𝔤) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (g : G) : h.IsSmoothFun (fun y => f (g * y)) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff] at hf ⊢
  intro g'
  simpa only [mul_assoc] using hf (g * g')

def leftTranslateSmoothEnd (h : IsExpLieAlgebra G 𝔤) (g : G) :
    Module.End ℂ (h.smoothFuns (F := ℂ)) where
  toFun f := ⟨fun y => (f : G → ℂ) (g * y), isSmoothFun_leftTranslate h f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_leftTranslateSmoothEnd (h : IsExpLieAlgebra G 𝔤) (g : G)
    (f : h.smoothFuns (F := ℂ)) (y : G) :
    ((leftTranslateSmoothEnd h g f : h.smoothFuns (F := ℂ)) : G → ℂ) y = (f : G → ℂ) (g * y) :=
  rfl

theorem commute_rightDerivEnd_leftTranslate (h : IsExpLieAlgebra G 𝔤) (g : G) (X : 𝔤) :
    Commute (h.rightDerivEnd (F := ℂ) X) (leftTranslateSmoothEnd h g) := by
  ext f y
  simp only [Module.End.mul_apply, IsExpLieAlgebra.coe_rightDerivEnd,
    coe_leftTranslateSmoothEnd, IsExpLieAlgebra.rightDeriv]
  simp only [mul_assoc]

theorem leftTranslate_smooth_commute (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸)
    (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G) :
    ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧
      ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y,
        (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by
  refine ⟨leftTranslateSmoothEnd h g f, fun y => rfl, fun T hT y => ?_⟩
  have hc : Commute T (leftTranslateSmoothEnd h g) := by
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT ?_).symm
    rintro _ ⟨X, rfl⟩
    exact (commute_rightDerivEnd_leftTranslate h g X).symm
  have := congrArg (fun S : Module.End ℂ (h.smoothFuns (F := ℂ)) => ((S f : h.smoothFuns (F := ℂ)) : G → ℂ) y) hc.eq
  simpa only [Module.End.mul_apply, coe_leftTranslateSmoothEnd] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneModularFormValueGaloisTransport
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isobaric_monomial_div (c x y ω : ℂ) (a b w : ℕ) (h : 4 * a + 6 * b = w) :
    c * (x ^ a * y ^ b) / ω ^ w = c * ((x / ω ^ 4) ^ a * (y / ω ^ 6) ^ b) := by
  rw [div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm, ← pow_add, h, mul_div_assoc]

theorem levelOne_value_transport : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → g (F τ₀ / ω₀ ^ w) = F' τ₁ / ω₁ ^ w := by
  intro g w N F F' τ₀ τ₁ ω₀ ω₁ hN hF hq h4 h6
  obtain ⟨s, c, hs, h0, h1⟩ := _root_.GlobalTheory.QFam.levelPoly_conj g w N F F' hN hF hq
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h0, h1, Finset.sum_div, Finset.sum_div, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp), isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp),
    map_mul, map_mul, map_pow, map_pow, h4, h6]

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def LieAt (b : Base D R) {A : Over S} [GrpObj A] (act : OActN D.O A) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) : Prop :=
  ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v →
    ∃ w : Fin D.a → (epsPtR x ⟶ A),
      (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧
      v = (List.ofFn w).prod

def LieRankAt (b : Base D R) {A : Over S} [GrpObj A] (act : OActN D.O A) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (g : R' →+* k) (i : Fin D.a),
    LieMult (act.toF D) (spMap g ≫ x) ((g.comp β).comp (b.t i)) D.m

def LieHer (b : Base D R) {A : Over S} [GrpObj A] (act : OActN D.O A) {R' : Type} [CommRing R'] (β : R →+* R')
    (x : Sp R' ⟶ S) : Prop :=
  ∀ (R'' : Type) [CommRing R''] (g : R' →+* R''),
    LieAt b act (g.comp β) (spMap g ≫ x) ∧ LieRankAt b act (g.comp β) (spMap g ≫ x)

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupport
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem GlobalTheory.lift_of_reduced_of_support {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
    [IsReduced T] (g : T ⟶ Y) (hg : ∀ t, g t ∈ i.ker.support) : ∃ h : T ⟶ X, h ≫ i = g := by
  have hle : i.ker ≤ g.ker := by
    refine (Scheme.IdealSheafData.le_ofIdeals_iff (I := i.ker)).mpr ?_
    intro U a ha
    rw [RingHom.mem_ker]
    apply eq_zero_of_basicOpen_eq_bot
    rw [← Scheme.preimage_basicOpen]
    ext t
    simp only [Scheme.Hom.mem_preimage, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro ht
    have h1 := (Scheme.IdealSheafData.mem_support_iff.mp (hg t)) U
    exact (Y.mem_zeroLocus_iff _ _).mp h1 a ha ht
  exact ⟨IsClosedImmersion.lift i g hle, IsClosedImmersion.lift_fac _ _ _⟩
end

