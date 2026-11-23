module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0682
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivExtendingOfKerLe

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfKummerClassOfUnitEqZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.KumZero

theorem isUnit_top {A : Type} [CommRing A] {q : ℕ} (h : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem inv_sch {q : ℕ} {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  rintro U ⟨x⟩
  have x' : U ⟶ X := x
  simpa using hX.map x'.appTop.hom

theorem unitSec_injective {X : Scheme.{0}} : Function.Injective (unitSec (U := X)) := by
  intro a b h
  have := (GlobalTheory.EtC.GmSec.gm_sec_bijective X).1 h
  simpa using congrArg (fun z => Additive.toMul z.down) this

theorem unitSec_surjective {X : Scheme.{0}} (b : Sec Gm X) : ∃ v, unitSec v = b := by
  obtain ⟨w, hw⟩ := (GlobalTheory.EtC.GmSec.gm_sec_bijective X).2 b
  exact ⟨Additive.toMul w.down, hw⟩

theorem sec_map_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) (n : ℤ) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (n • φ) x = n • Sec.map φ x := by
  have h : (n • φ).hom = n • φ.hom := (sheafToPresheaf _ _).map_zsmul (X := F) (Y := G) (f := φ) (r := n)
  unfold Sec.map
  rw [h, NatTrans.app_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply]

theorem smul_unitSec (n : ℕ) {X : Scheme.{0}} (v : (Γ(X, ⊤))ˣ) : (n : ℤ) • unitSec v = unitSec (v ^ n) := by
  unfold unitSec ofRings.sec
  refine (map_zsmul (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op X))) (n : ℤ)
    (show (Scheme.Γ ⋙ unitsF).obj (op X) from ⟨Additive.ofMul v⟩)).symm.trans ?_
  congr 1

theorem map_q_unitSec (q : ℕ) {X : Scheme.{0}} (v : (Γ(X, ⊤))ˣ) :
    Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) = unitSec (v ^ q) := by
  rw [sec_map_zsmul, ← smul_unitSec]
  rfl

theorem _root_.GlobalTheory.EtC.eq_pow_of_kum_eq_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) →
    ∀ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = 0 → ∃ v, u = v ^ q := by
  intro q _ A _ hq u hu
  have hX := isUnit_top hq
  obtain ⟨κ, -, bd, -, hex, ⟨s, hs⟩, -⟩ := GlobalTheory.T.exists_kummer_boundary_etale_cohomology q
  have h1 : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0 := by
    rw [hs _ u hX, hu, smul_zero]
  obtain ⟨y, hy⟩ := ((hex _ (inv_sch hX) 0).1 _).1 h1
  have hsc := GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))
  obtain ⟨b, rfl⟩ := hsc.2.1.2 y
  rw [hsc.2.2.2.2] at hy
  have hb := hsc.2.1.1 hy
  obtain ⟨v, rfl⟩ := unitSec_surjective b
  rw [map_q_unitSec] at hb
  exact ⟨v, (unitSec_injective hb).symm⟩

end GlobalTheory.EtC.KumZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfNeZeroMapIsotypicSumOfCopies
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.IsotypicMap

open Representation

variable {H V V' W : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W]

theorem exists_comp_ne_zero {τ : Representation ℂ H V} {τ' : Representation ℂ H V'} {ρ : Representation ℂ H W}
    (h : IsIsotypicOf τ ρ) (T : IntertwiningMap τ τ') (hT : T ≠ 0) :
    ∃ f : IntertwiningMap ρ τ, T.comp f ≠ 0 := by
  by_contra hc
  push Not at hc
  apply hT
  apply IntertwiningMap.ext
  rw [IntertwiningMap.zero_toLinearMap, ← LinearMap.ker_eq_top, ← top_le_iff, ← (show _ = _ from h)]
  refine iSup_le fun f => ?_
  rintro _ ⟨w, rfl⟩
  exact congrArg (fun g : IntertwiningMap ρ τ' => g w) (hc f)

theorem exists_leftInverse [Finite H] {τ : Representation ℂ H V} {ρ : Representation ℂ H W}
    (f : IntertwiningMap ρ τ) (hf : Function.Injective f) :
    ∃ s : IntertwiningMap τ ρ, ∀ w, s (f w) = w := by
  have : NeZero (Nat.card H : ℂ) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  obtain ⟨g, hg⟩ := MonoidAlgebra.exists_leftInverse_of_injective
    (IntertwiningMap.equivLinearMapAsModule ρ τ f) (LinearMap.ker_eq_bot.2 hf)
  exact ⟨(IntertwiningMap.equivLinearMapAsModule τ ρ).symm g, fun w => LinearMap.congr_fun hg w⟩

theorem equiv_of_isotypic_map : ∀ (H : Type) [Group H] [Finite H] (V V' W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (τ : Representation ℂ H V) (τ' : Representation ℂ H V') (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W'), ρ.IsIrreducible → ρ'.IsIrreducible → IsIsotypicOf τ ρ → IsIsotypicOf τ' ρ' → ∀ T : Representation.IntertwiningMap τ τ', T ≠ 0 → Nonempty (Representation.Equiv ρ ρ') := by
  intro H _ _ V V' W W' _ _ _ _ _ _ _ _ τ τ' ρ ρ' hρ hρ' h h' T hT
  obtain ⟨f, hf⟩ := exists_comp_ne_zero h T hT
  have hi := (Representation.IsIrreducible.injective_or_eq_zero (T.comp f)).resolve_right hf
  obtain ⟨s, hs⟩ := exists_leftInverse (T.comp f) hi
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hf
    apply IntertwiningMap.ext
    ext w
    have hw : w = 0 := (hs w).symm
    subst hw
    simp
  obtain ⟨f', hf'⟩ := exists_comp_ne_zero h' s hs0
  have hb := (Representation.IsIrreducible.bijective_or_eq_zero (s.comp f')).resolve_right hf'
  exact ⟨(IntertwiningMap.ofBijective _ hb).symm⟩

end GlobalTheory.IsotypicMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationSepClosureIsEquivalence
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.SepCech

theorem aug_comm {Y Y' X : Scheme.{0}} (f : Y ⟶ X) (g : Y' ⟶ X) (u : yoneda.obj Y ⟶ yoneda.obj Y')
    (w : u ≫ yoneda.map g = yoneda.map f ≫ 𝟙 _) :
    SimplicialObject.cechNerve.map (Arrow.homMk u (𝟙 _) w : Arrow.mk (yoneda.map f) ⟶ Arrow.mk (yoneda.map g)) ≫ GlobalTheory.EtC.cechAug g =
      GlobalTheory.EtC.cechAug f := by
  apply NatTrans.ext; funext n
  simp [GlobalTheory.EtC.cechAug, SimplicialObject.cechNerve, Arrow.mapCechNerve, Arrow.augmentedCechNerve]
  erw [NatTrans.comp_app, WidePullback.lift_base]

theorem cont (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] : ContCone R F (cechCone K Ω) := by
  obtain ⟨hc⟩ := GlobalTheory.T.isColimit_finiteSubextensionRingCocone K Ω
  obtain ⟨hl⟩ := GlobalTheory.T.isLimit_finiteSubextensionSpecArrowCone K Ω hc
  refine GlobalTheory.T.isCohomologyContinuousOnCone_of_levelwise R F _ _ _ (fun k => ?_)
  obtain ⟨hk⟩ := GlobalTheory.T.cechNerve_level_preserves_cofiltered_limit _ _ _ hl (fun _ _ _ => show IsIso (𝟙 _) from inferInstance)
    (fun _ => show IsIso (𝟙 _) from inferInstance) k
  refine GlobalTheory.T.continuity_cofiltered_limit_represented_affine R F hF _ _ _ hk (fun L => ?_) ?_
  · obtain ⟨Z, π, e, hπ, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsAffineHom _ _ (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) inferInstance k
    haveI := hπ
    exact ⟨Z, isAffine_of_isAffineHom π, ⟨e⟩⟩
  · obtain ⟨Z, π, e, -, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsAffineHom _ _ (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) inferInstance k
    exact ⟨Z, ⟨e⟩⟩

theorem cechAug_sepClosure_eqv : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω], Eqv R (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) F := by
  intro R _ F hF K Ω _ _ _ _
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have hc := cont R F hF K Ω
  have hA : ∀ L : (FinSub K Ω)ᵒᵖ, Eqv R (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1)))) F := by
    intro L
    haveI := L.unop.2
    haveI : Algebra.IsSeparable K L.unop.1 := Algebra.isSeparable_tower_bot_of_isSeparable K L.unop.1 Ω
    obtain ⟨h1, h2⟩ := _root_.GlobalTheory.spec_map_smooth_surjective_of_isSeparable K L.unop.1
    exact _root_.GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology R _ F
  have hw : ∀ L : (FinSub K Ω)ᵒᵖ, (cechCone K Ω).π.app L ≫ GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) =
      GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := fun L => aug_comm _ _ _ _
  have hw2 : ∀ ⦃L L' : (FinSub K Ω)ᵒᵖ⦄ (f : L ⟶ L'), (arr K Ω ⋙ SimplicialObject.cechNerve).map f ≫
      GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L'.unop.1))) =
      GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) := fun L L' f => aug_comm _ _ _ _
  intro n
  constructor
  · refine (injective_iff_map_eq_zero (pull R _ F n)).mpr (fun z hz => ?_)
    let L0 : (FinSub K Ω)ᵒᵖ := op ⟨⊥, inferInstance⟩
    have h0 : pull R ((cechCone K Ω).π.app L0) F n
        (pull R (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L0.unop.1)))) F n z) = 0 :=
      (pull_comp R _ _ F n z).symm.trans ((congrArg (fun g => pull R g F n z) (hw L0)).trans hz)
    obtain ⟨L1, f, hf⟩ := (hc n).2 L0 _ h0
    have hf' : pull R (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L1.unop.1)))) F n z = 0 :=
      (congrArg (fun g => pull R g F n z) (hw2 f)).symm.trans
        ((pull_comp R ((arr K Ω ⋙ SimplicialObject.cechNerve).map f)
          (GlobalTheory.EtC.cechAug (Spec.map (CommRingCat.ofHom (algebraMap K L0.unop.1)))) F n z).trans hf)
    exact ((injective_iff_map_eq_zero (pull R _ F n)).mp (hA L1 n).1) z hf'
  · intro x
    obtain ⟨L, y, hy⟩ := (hc n).1 x
    obtain ⟨z, rfl⟩ := (hA L n).2 y
    refine ⟨z, ?_⟩
    rw [← hy]
    exact (congrArg (fun g => pull R g F n z) (hw L)).symm.trans (pull_comp R _ _ F n z)

end GlobalTheory.SepCech
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyShiftMem
section
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer.CloseTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

def splitL (I : Type) [Fintype I] (g : ℕ) : (I ⊕ Fin g → ℂ) →L[ℂ] Tot I g :=
  (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (Sum.inl i)).prod
    (ContinuousLinearMap.pi fun b ↦ ContinuousLinearMap.proj (Sum.inr b))


omit [DecidableEq I] in
theorem shift_eq (w : Fin g → ℂ) (x : I ⊕ Fin g → ℂ) :
    (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : Tot I g) = (0, w) + splitL I g x := by
  ext <;> simp [splitL]

theorem splitL_single (b : Fin g) :
    splitL I g (Pi.single (Sum.inr b) 1) = ((0, Pi.single b 1) : Tot I g) := by
  ext i <;> simp [splitL, Pi.single_apply]


omit [DecidableEq I] in
theorem eventually_shift_mem {W : Opens (Tot I g)} {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0, (0, w) + splitL I g x ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) :=
    continuous_const.add (splitL I g).continuous
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  simpa using hw


omit [DecidableEq I] in
theorem analyticAt_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x)
    (h.analytic _ hw) (analyticAt_const.add ((splitL I g).analyticAt 0)) (by simp)

theorem fderiv_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W)
    (b : Fin g) :
    (fun z ↦ fderiv ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) z (Pi.single (Sum.inr b) 1))
      =ᶠ[𝓝 0] fun x : I ⊕ Fin g → ℂ ↦ (dw b h).fn ((0, w) + splitL I g x) := by
  filter_upwards [eventually_shift_mem hw] with z hz
  have e : HasFDerivAt (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x))
      ((fderiv ℂ h.fn ((0, w) + splitL I g z)).comp (splitL I g)) z :=
    HasFDerivAt.comp (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) z
      (h.analytic _ hz).differentiableAt.hasFDerivAt ((splitL I g).hasFDerivAt.const_add _)
  rw [e.fderiv, ContinuousLinearMap.comp_apply, splitL_single]
  exact (Hol.fn_der _ h hz).symm

end GlobalTheory.AnPer.CloseTaylor


open GlobalTheory.AnPer.CloseTaylor in
theorem GlobalTheory.AnPer.close_of_sliceTaylor : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D), (∀ i, t i ∈ J) → ∀ (r : ℕ) (n : Fin r → Fin g → D), (∀ j a, n j a ∈ J) → (∀ j a b, n j a * n j b = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens (Tot I g)) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∀ ρ₁ ρ₂ : Hol W →+* D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₁ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun b ↦ ∑ j, n j b) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₂ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun _ ↦ 0) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol W₀)) ρ₁ ρ₂ := by
  intro I _ _ g D _ _ J N hJ t ht r n hn hnn E _ _ _ W W₀ a ha hW ρ₁ ρ₂ h₁ h₂
  induction r generalizing ρ₁ with
  | zero =>
    have : ρ₁ = ρ₂ := RingHom.ext fun h ↦ GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ by
      rw [h₁, h₂]; simp
    rw [this]
    exact Relation.ReflTransGen.refl
  | succ r ih =>
    obtain ⟨ρ', hρ'⟩ := _root_.GlobalTheory.AnPer.exists_sliceTaylor_algHom N (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b)
      (fun s ↦ hJ _ fun c ↦ by
        rcases s c with i | b
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _) W W₀ a ha hW
    refine Relation.ReflTransGen.head (b := (ρ' : Hol W →+* D ⊗[ℂ] Hol W₀)) ?_
      (ih (fun j ↦ n j.succ) (fun j ↦ hn _) (fun j ↦ hnn _) _ hρ')
    refine ⟨fun b ↦ (-n 0 b) ⊗ₜ[ℂ] 1, fun b ↦ Ideal.mem_map_of_mem _ (J.neg_mem (hn 0 b)), fun b c ↦ ?_, fun h ↦ ?_⟩
    · rw [Algebra.TensorProduct.tmul_mul_tmul, neg_mul_neg, hnn, zero_tmul]
    refine GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    have e : (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b) = fun i : I ⊕ Fin g ↦
        (Sum.elim t fun b ↦ ∑ j, n j b) i + (Sum.elim (fun _ ↦ 0) fun b ↦ -n 0 b) i := by
      ext (i | b)
      · simp
      · simp [Fin.sum_univ_succ]
    have hs := _root_.GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero N (Sum.elim t fun b ↦ ∑ j, n j b) (Sum.elim (fun _ : I ↦ 0) fun b ↦ -n 0 b)
      (fun s hs ↦ hJ s fun c ↦ (Ideal.span_le.2 (by
        rintro _ (⟨i | b, rfl⟩ | ⟨i | b, rfl⟩)
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _
        · exact J.zero_mem
        · exact J.neg_mem (hn 0 b))) (hs c))
      (by rintro (i | b) (j | c) <;> simp [hnn]) _ (analyticAt_shifted h (hW p hp))
    obtain ⟨-, -, -, hcongr, -, -⟩ :=
      GlobalTheory.PeriodFamily.taylor_formal_properties N (Sum.elim t fun b ↦ ∑ j, n j b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.coe_coe, hρ', map_add (f := _), map_sum, h₁, e]
    simp only [map_mul, h₁, shift_eq]
    rw [hs, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add]
    refine congrArg _ (Finset.sum_congr rfl fun b _ ↦ ?_)
    rw [hcongr _ _ (fderiv_shifted h (hW p hp) b)]
    simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIde
section
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem uniformBell_comp_coeff (m : ℕ) {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    n.uniformBell N ^ m * m.uniformBell (n * N) = m.uniformBell n * (m * n).uniformBell N := by
  have h1 := Nat.uniformBell_mul_eq n hN
  have h2 := Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)
  have h3 := Nat.uniformBell_mul_eq m hn
  have h4 := Nat.uniformBell_mul_eq (m * n) hN
  have hpos : 0 < m.factorial * n.factorial ^ m * N.factorial ^ (m * n) := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc n.uniformBell N ^ m * m.uniformBell (n * N) * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n))
      = m.uniformBell (n * N) * (n.uniformBell N * N.factorial ^ n * n.factorial) ^ m * m.factorial := by ring
    _ = (m * (n * N)).factorial := by rw [h1, h2]
    _ = ((m * n) * N).factorial := by rw [Nat.mul_assoc]
    _ = (m * n).uniformBell N * N.factorial ^ (m * n) * (m.uniformBell n * n.factorial ^ m * m.factorial) := by
      rw [h3, h4]
    _ = m.uniformBell n * (m * n).uniformBell N * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n)) := by ring

theorem exists_dividedPowers_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  intro B _ Q
  obtain ⟨γ, hγ, he⟩ := _root_.GlobalTheory.PDA.exists_isPreDividedPowers_augmentation B Q
  have hcomp : ∀ x ∈ Set.range (fun k : ℕ ↦ Q.e (k + 1)), ∀ m n : ℕ, n ≠ 0 →
      γ m (γ n x) = (m.uniformBell n : Q.P) * γ (m * n) x := by
    rintro _ ⟨k, rfl⟩ m n hn
    obtain ⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1 := ⟨n * (k + 1) - 1, by
      have : 0 < n * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos
      omega⟩
    have hmem : Q.e (n * (k + 1)) ∈ Q.aug := hj ▸ Q.e_succ_mem_aug j
    have key := congrArg (Nat.cast (R := Q.P)) (uniformBell_comp_coeff m hn k.succ_ne_zero)
    push_cast at key
    rw [he n k, hγ.mul m _ _ hmem, hj, he m j, ← hj, he (m * n) k, ← Nat.mul_assoc]
    linear_combination key * Q.e (m * n * (k + 1))
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.PDA.exists_dividedPowers_of_comp_on_gens Q.P Q.aug γ (Set.range fun k : ℕ ↦ Q.e (k + 1)) hγ rfl hcomp
  refine ⟨δ, fun n ↦ ?_⟩
  rw [hδ]
  have := he n 0
  simpa [Nat.uniformBell_one_right] using this

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative
section
noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg MvPolynomial GlobalTheory.FockDeg

namespace GlobalTheory.FockAlg.HarmLift

variable {p q r s : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem plusPart_eq_sub {Z : Mat p q} (hZ : IsPC Z) (Q : Pol p q r s) :
    plusPart (fockAct1 p q r s Z) Q = fockAct1 p q r s Z Q - minusPart (fockAct1 p q r s Z) Q := by
  rw [fockAct1_eq, omAct_eq_parts (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ) Q, add_sub_cancel_right]

theorem minusPart_mem {Z : Mat p q} (hZ : IsPC Z) {d : ℕ} {Q : Pol p q r s}
    (hQ : Q ∈ homog (Ix p q × Ix r s) d) :
    minusPart (fockAct1 p q r s Z) Q ∈ homog (Ix p q × Ix r s) (d - 2) := by
  rw [fockAct1_eq, minusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ)]
  exact downOp_mem _ d Q hQ

theorem minusPart_low {Z : Mat p q} (hZ : IsPC Z) {d : ℕ} (hd : d < 2) {Q : Pol p q r s}
    (hQ : Q ∈ homog (Ix p q × Ix r s) d) : minusPart (fockAct1 p q r s Z) Q = 0 := by
  rw [fockAct1_eq, minusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ)]
  exact downOp_low _ d Q hd hQ

theorem span_harm2 : Submodule.span ℂ (harm2 p q r s) = HarmStable.sub2 p q r s := by
  rw [← HarmStable.coe_fockHarmonicsSecondMemberSubmodule, Submodule.span_eq]

theorem homog_le (pr : Pol p q r s →ₗ[ℂ] W)
    (hpr : ∀ Z : Mat p q, IsPC Z → ∀ f, pr (fockAct1 p q r s Z f) = 0) (d : ℕ) :
    homog (Ix p q × Ix r s) d ≤ HarmStable.sub2 p q r s ⊔ LinearMap.ker pr := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases Nat.lt_or_ge d 2 with hd | hd
    · intro f hf
      refine Submodule.mem_sup_left ?_
      rw [← SetLike.mem_coe, HarmStable.coe_fockHarmonicsSecondMemberSubmodule]
      exact fun Z hZ => minusPart_low hZ hd hf
    · obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
      rw [(GlobalTheory.FischerParts.fischer_parts p q r s n).1, span_harm2]
      refine sup_le (inf_le_right.trans le_sup_left) (Submodule.span_le.2 ?_)
      rintro _ ⟨Q, hQ, Z, hZ, rfl⟩
      rw [SetLike.mem_coe, plusPart_eq_sub hZ]
      refine Submodule.sub_mem _ (Submodule.mem_sup_right (hpr Z hZ Q)) ?_
      exact ih (n - 2) (by omega) (minusPart_mem hZ hQ)

theorem exists_harm2_rep : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (pr : Pol P Q R S →ₗ[ℂ] W), (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) →
    ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := by
  intro P Q R S W _ _ pr hpr f
  have hf : f ∈ HarmStable.sub2 P Q R S ⊔ LinearMap.ker pr := by
    rw [← sum_homogeneousComponent f]
    exact Submodule.sum_mem _ fun i _ => homog_le pr hpr i (homogeneousComponent_mem i f)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
  refine ⟨y, ?_, ?_⟩
  · rw [← HarmStable.coe_fockHarmonicsSecondMemberSubmodule]; exact hy
  · rw [map_add (f := _), LinearMap.mem_ker.1 hz, add_zero]

end GlobalTheory.FockAlg.HarmLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisLiftResidueCongruencePadic
section
namespace GlobalTheory.ResidueLift

open IsLocalRing

theorem res_eq_zero_iff {l : ℕ} [Fact l.Prime] (x : GlobalTheory.ZJ.OO l) :
    residue (GlobalTheory.ZJ.OO l) x = 0 ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.ZH.not_isUnit_OO_iff]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] L] (J : Type) (a b : J → PadicAlgCl l), (∀ j, ‖a j‖ ≤ 1) → (∀ j, ‖b j‖ ≤ 1) → (∀ p : MvPolynomial J (PadicAlgCl l), (∀ n, p.coeff n ∈ L ∧ ‖p.coeff n‖ ≤ 1) → (‖MvPolynomial.eval a p‖ < 1 ↔ ‖MvPolynomial.eval b p‖ < 1)) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ j, ‖g (a j) - b j‖ < 1 := by
  intro l _ L _ J a b ha hb hab
  let K := PadicAlgCl l
  let O := GlobalTheory.ZJ.OO l
  let a' : J → O := fun j => ⟨a j, (GlobalTheory.ZH.mem_OO_iff _).2 (ha j)⟩
  let b' : J → O := fun j => ⟨b j, (GlobalTheory.ZH.mem_OO_iff _).2 (hb j)⟩
  let As : Subring O := L.toSubalgebra.toSubring.comap O.subtype
  let f : As →+* GlobalTheory.ZJ.kb l := (residue O).comp As.subtype
  let R := f.range
  have key : ∀ (c : J → O) (q : MvPolynomial J As),
      MvPolynomial.aeval (fun j => residue O (c j)) (MvPolynomial.map f.rangeRestrict q) = 0 ↔
      ‖MvPolynomial.eval (fun j => (c j : K)) (MvPolynomial.map (O.subtype.comp As.subtype) q)‖ < 1 := by
    intro c q
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval_map]
    have h1 : MvPolynomial.eval₂ ((algebraMap R (GlobalTheory.ZJ.kb l)).comp f.rangeRestrict) (fun j => residue O (c j)) q
        = residue O (MvPolynomial.eval₂ As.subtype c q) := by
      rw [MvPolynomial.eval₂_comp_left]; rfl
    have h2 : MvPolynomial.eval₂ (O.subtype.comp As.subtype) (fun j => (c j : K)) q
        = ((MvPolynomial.eval₂ As.subtype c q : O) : K) :=
      (MvPolynomial.eval₂_comp_left O.subtype As.subtype c q).symm
    rw [h1, h2, res_eq_zero_iff]
  have hII : ∀ p : MvPolynomial J R, MvPolynomial.aeval (fun j => residue O (a' j)) p = 0 →
      MvPolynomial.aeval (fun j => residue O (b' j)) p = 0 := by
    intro p hp
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective f.rangeRestrict f.rangeRestrict_surjective p
    rw [key] at hp ⊢
    refine (hab _ fun n => ?_).1 hp
    rw [MvPolynomial.coeff_map]
    exact ⟨(AddMonoidAlgebra.coeff q n).2, (GlobalTheory.ZH.mem_OO_iff _).1 (((AddMonoidAlgebra.coeff q n : As) : O).2)⟩
  haveI := GlobalTheory.ZJ.isAlgClosed_kb (p := l)
  obtain ⟨φ, hφR, hφ⟩ := _root_.GlobalTheory.exists_ringEquiv_extending_of_ker_le _ GlobalTheory.ZJ.exists_pow_eq_one_kb R J _ _ hII
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl l L φ fun x hx => hφR _ ⟨⟨x, hx⟩, rfl⟩
  exact ⟨g, fun j => hg (a' j) (b' j) (hφ j).symm⟩

end GlobalTheory.ResidueLift
end

