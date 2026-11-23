module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveLatticeGluedFromIntersection
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.Unglue

theorem ideal_eq_top {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥)
    (h : ∀ a : E, (∀ i ∈ I, a * (i : E) ∈ (algebraMap (𝓞 E) E).range) → a ∈ (algebraMap (𝓞 E) E).range) :
    I = ⊤ := by
  have h0 : (I : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI
  have h1 : (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ≤ 1 := by
    intro a ha
    have ha' := (FractionalIdeal.mem_inv_iff h0).1 ha
    refine (FractionalIdeal.mem_one_iff _).2 (h a fun i hi => ?_)
    exact (FractionalIdeal.mem_one_iff _).1 (ha' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hi))
  have h2 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 E)⁰ E) = I * (I : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact top_le_iff.1 h2

theorem star_mem {E : Type} [Field E] [NumberField E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨RingOfIntegers.mapRingEquiv starRingAut b, rfl⟩

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (L : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (L : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target
  | (apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementSixOneSixtyEight.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementSixOneSixtyEight.target ..)

theorem isLattice_capX_and_exists_glue (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V)
    (hl : IsLine Y X ι z u) (L : Submodule (𝓞 D.host.E) Y.V) (hL : IsSDIn Y (flatSp Y X ι z) L) (hp : IsPrim Y z L) :
    Submodule.IsFullLattice D.host.E (capX Y X ι L) ∧ ∃ x₀ : X.V, L = glueLat Y X ι z u (capX Y X ι L) x₀ := by
  obtain ⟨hi, ho, hz⟩ := hl
  obtain ⟨hfg, hsp, hsd⟩ := hL
  have hT := Tu_ne_zero u
  have hinj : Function.Injective ι := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    refine X.nondeg.1 x fun y => ?_
    rw [← hi, hx, map_zero, LinearMap.zero_apply]
  have hzU : ∀ a : D.host.E, a • z ∈ flatSp Y X ι z := fun a =>
    Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z))
  have hzL : z ∈ L := by simpa using (hp 1).2 (one_mem _)
  have hLU : ∀ y ∈ L, y ∈ flatSp Y X ι z := fun y hy => hsp ▸ Submodule.subset_span hy
  have hint : ∀ y ∈ L, Y.hD y z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := fun y hy =>
    (hsd z (hLU z hzL)).1 hzL y hy
  have hdec : ∀ y ∈ L, ∃ x : X.V, y = ι x + (-(Y.hD y z) * (Tu D u)⁻¹) • z := by
    intro y hy
    obtain ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 (hLU y hy)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hb
    refine ⟨x, ?_⟩
    have : Y.hD (ι x + s • z) z = -(s * Tu D u) := by
      have h1 := ho x
      simp only [HSpace.hD] at h1 hz ⊢
      rw [map_add (f := _), map_smul, h1, hz, smul_eq_mul]; ring
    rw [this]
    congr 2
    field_simp
  have hlat : Submodule.IsLattice D.host.E (capX Y X ι L) := by
    refine GlobalTheory.StdFrames.isLattice_crdLat X ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective (ι.restrictScalars (𝓞 D.host.E)) hinj (hfg.of_le ?_)
      exact Submodule.map_comap_le _ _
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  refine ⟨{ toIsLattice := hlat, span_eq_top := ?_ }, ?_⟩
  · apply Submodule.eq_top_iff'.2
    intro y
    let x := (Formalism.L2.Herm.crd X).symm y
    have hx : ι x ∈ Submodule.span D.host.E (L : Set Y.V) := by
      rw [hsp]
      exact Submodule.mem_sup_left (LinearMap.mem_range_self ι x)
    obtain ⟨c, hc, hcx⟩ := exists_smul_mem L hx
    have hcy : c • y ∈ capX Y X ι L := by
      change c • y ∈ Formalism.L2.Herm.crdLat X (L.comap (ι.restrictScalars (𝓞 D.host.E)))
      refine ⟨c • x, ?_, ?_⟩
      · change ι (c • x) ∈ L
        simpa using hcx
      · simp [x]
    have hcy' : c • y ∈ Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E)) :=
      Submodule.subset_span hcy
    rw [← algebraMap_smul D.host.E c] at hcy'
    have := (Submodule.span D.host.E (capX Y X ι L : Set (Fin X.rank → D.host.E))).smul_mem
      (c : D.host.E)⁻¹ hcy'
    simpa only [smul_smul, inv_mul_cancel₀ (RingOfIntegers.coe_ne_zero_iff.2 hc), one_smul] using this
  · let I : Ideal (𝓞 D.host.E) :=
      (L.map ((Y.hT z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hI : ∀ i : 𝓞 D.host.E, i ∈ I ↔ ∃ y ∈ L, Y.hD y z = (i : D.host.E) := fun i => Iff.rfl
    have hI0 : I ≠ ⊥ := by
      obtain ⟨i, hi'⟩ := hint z hzL
      intro h
      have : i ∈ I := (hI i).2 ⟨z, hzL, hi'.symm⟩
      rw [h, Ideal.mem_bot] at this
      rw [this, map_zero, hz] at hi'
      exact hT (neg_eq_zero.1 hi'.symm)
    have hItop : I = ⊤ := by
      refine ideal_eq_top I hI0 fun a ha => ?_
      have : star a • z ∈ L := by
        refine (hsd _ (hzU _)).2 fun x hx => ?_
        obtain ⟨i, hi'⟩ := hint x hx
        have := ha i ((hI i).2 ⟨x, hx, hi'.symm⟩)
        have e : Y.hD x (star a • z) = a * Y.hD x z := by
          simp only [HSpace.hD]
          rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
          congr 1
          exact star_star a
        rw [e, ← hi']
        exact this
      simpa using star_mem ((hp _).1 this)
    obtain ⟨l, hlL, hl1⟩ := (hI (-1)).1 (hItop ▸ Submodule.mem_top)
    obtain ⟨x₀, hx₀⟩ := hdec l hlL
    have hl2 : l = (Tu D u)⁻¹ • z + ι x₀ := by
      rw [hx₀, hl1, add_comm]
      simp
    have hc : (capX Y X ι L).comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
        L.comap (ι.restrictScalars (𝓞 D.host.E)) :=
      Submodule.comap_map_eq_of_injective (f := (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E))
        (Formalism.L2.Herm.crd X).injective _
    refine ⟨x₀, ?_⟩
    rw [glueLat, hc, ← hl2]
    refine le_antisymm (fun y hy => ?_)
      (sup_le (Submodule.map_comap_le _ _) ((Submodule.span_singleton_le_iff_mem _ _).2 hlL))
    obtain ⟨x, hx⟩ := hdec y hy
    obtain ⟨b, hb⟩ := hint y hy
    have e : y + b • l = ι (x + b • x₀) := by
      rw [← algebraMap_smul D.host.E b, ← algebraMap_smul D.host.E b x₀, hb, map_add (f := _), map_smul, hl2]
      generalize Y.hD y z = t at hx ⊢
      rw [hx]
      module
    have hm : y + b • l ∈ L := L.add_mem hy (L.smul_mem _ hlL)
    have e2 : y = ι (x + b • x₀) - b • l := by rw [← e, add_sub_cancel_right]
    rw [e2]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x + b • x₀, ?_, rfl⟩)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l)))
    change ι (x + b • x₀) ∈ L
    rw [← e]
    exact hm

end GlobalTheory.AdIsom.Unglue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleRationalClassKernelIntegrals
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.RegClass

open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

variable {D : D7} {V : HSp D}

theorem rat_mem (g : GF V) : rat V g ∈ GQ V := by
  rw [show GQ V = (rat V).range from (range_ratEmb ..).symm]; exact ⟨g, rfl⟩

def classEquiv (γ : GF V) : {δ : GF V | IsConj γ δ} ≃ ratClass (GQ V) (rat V γ) :=
  Equiv.ofBijective (fun δ => ⟨rat V δ, by
      obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
      refine ⟨rat V c⁻¹, rat_mem _, ?_⟩
      rw [← hc]; simp only [map_mul, map_inv, inv_inv]⟩)
    ⟨fun a b h => Subtype.ext (ratEmb_injective _ _ (congrArg Subtype.val h)), fun δ => by
      obtain ⟨δ, g, hg, rfl⟩ := δ
      rw [show GQ V = (rat V).range from (range_ratEmb ..).symm] at hg
      obtain ⟨c, rfl⟩ := hg
      refine ⟨⟨c⁻¹ * γ * c, isConj_iff.2 ⟨c⁻¹, by group⟩⟩, Subtype.ext ?_⟩
      simp only [map_mul, map_inv]⟩

theorem classKernel_eq (γ : GF V) (f : GA D V → ℂ) (x : GA D V) :
    classKernel (GQ V) (rat V γ) f x = ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x) :=
  ((classEquiv γ).tsum_eq fun δ : ratClass (GQ V) (rat V γ) => f (x⁻¹ * δ * x)).symm

theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

theorem fd_iff {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) :
    (IntegrableOn φ 𝓕 μ ↔ Integrable (descend (GQ V) φ) (autMeasure V μ)) ∧
      ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (F := descend (GQ V) φ) (p := 1))
    rw [hφ.lift_descend, memLp_one_iff_integrable, memLp_one_iff_integrable] at this
    exact this.symm
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

theorem regClass : ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ | IsConj γ δ} ∧
    ∀ (f : GA D V → ℂ), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x =
      ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x)) ∧
    (Continuous f → HasCompactSupport f → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (c : ℂ),
      ((∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt (GQ V) μ 𝓕 (rat V γ) f c) ↔
        Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ) ∧
          ∫ q, descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) q ∂autMeasure V μ = c)) := by
  intro D V γ hγ
  refine ⟨GlobalTheory.regSS_conjClass_isSSClass γ hγ, fun f => ⟨classKernel_eq γ f, fun _ hcs μ _ c => ?_⟩⟩
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (classKernel (GQ V) (rat V γ) f) :=
    fun δ hδ x => classKernel_mul _ _ hδ x
  constructor
  · intro H
    have h𝓕 := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (GQ V) μ
    obtain ⟨-, hi, hv⟩ := H _ h𝓕
    obtain ⟨e1, e2⟩ := fd_iff h𝓕 hinv
    exact ⟨e1.1 hi, e2 ▸ hv⟩
  · rintro ⟨hi, hv⟩ 𝓕 h𝓕
    obtain ⟨e1, e2⟩ := fd_iff h𝓕 hinv
    exact ⟨summable_class hcs (rat_mem γ), e1.2 hi, e2.trans hv⟩

theorem main : ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ | IsConj γ δ} ∧ ∀ (f : GA D V → ℂ), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x = ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x)) ∧ (Continuous f → HasCompactSupport f → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (c : ℂ), ((∀ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt (GQ V) μ 𝓕 (rat V γ) f c) ↔ Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ) ∧ ∫ q, descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) q ∂autMeasure V μ = c)) := regClass

end GlobalTheory.RegClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRa
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem factorIdem_mul (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (p : plusAlg σ J γ) :
    factorIdem e i * ((p : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      ((e.symm (Pi.single i (e p i)) : plusAlg σ J γ) : genAlg γ) := by
  have h : e.symm (Pi.single i 1) * p = e.symm (Pi.single i (e p i)) := by
    apply e.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [← h]; rfl

theorem factorIdem_mul_self (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    factorIdem e i * factorIdem e i = factorIdem e i := by
  have := factorIdem_mul e i (e.symm (Pi.single i 1))
  rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same] at this
  exact this

theorem factorIdem_ne_zero (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) : factorIdem e i ≠ 0 := by
  intro h
  have h1 : e.symm (Pi.single i 1) = 0 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) i
  simp at h2

theorem factorIdem_selfAdj (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (factorIdem e i) * J = J * factorIdem e i :=
  (e.symm (Pi.single i 1)).2

theorem factorIdem_orth (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (1 - factorIdem e i) * J * factorIdem e i = 0 := by
  have hq : cT (σ : E →+* E) (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) * J =
      J * (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) :=
    (1 - e.symm (Pi.single i 1)).2
  have hc : (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      1 - factorIdem e i := rfl
  rw [hc] at hq
  rw [hq, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, factorIdem_mul_self, sub_self, Matrix.mul_zero]

theorem factorIdem_comm (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    ∀ l ∈ genAlg γ, l * factorIdem e i = factorIdem e i * l := by
  intro l hl
  exact congrArg Subtype.val (mul_comm (⟨l, hl⟩ : genAlg γ) (e.symm (Pi.single i 1) : plusAlg σ J γ))

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem rank_factorIdem {γ : GL (Fin n) E} (hA : ClauseAlg σ J γ) (hP : ClausePlus σ J γ)
    (e : plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    (factorIdem e i).rank = Module.finrank E (E ⊗[F] K i) := by
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  obtain ⟨-, -, hbij⟩ := hP
  let L := genAlg (γ : Matrix (Fin n) (Fin n) E)
  let P := plusAlg σ J (γ : Matrix (Fin n) (Fin n) E)
  let φ : L →ₗ[E] (Fin n → E) :=
    { toFun := fun l => (l : Matrix (Fin n) (Fin n) E) *ᵥ v
      map_add' := fun a b => Matrix.add_mulVec _ _ _
      map_smul' := fun c a => Matrix.smul_mulVec _ _ _ }
  let incl : P →ₗ[F] L := P.val.toLinearMap
  let ψ : E ⊗[F] P →ₗ[E] L := LinearMap.liftBaseChange E incl
  let ι : K i →ₗ[F] P := e.symm.toLinearMap ∘ₗ LinearMap.single F K i
  let Φ : E ⊗[F] K i →ₗ[E] (Fin n → E) := φ ∘ₗ ψ ∘ₗ ι.baseChange E
  have hψ : ∀ t, ψ t = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) (TensorProduct.comm F E P t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      change ψ 0 = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) ((TensorProduct.comm F E P).toLinearMap 0)
      rw [map_zero, map_zero, map_zero]
    | tmul a p =>
      simp [ψ, incl, plusTensor, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def, mul_comm]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hψb : Function.Bijective ψ := by
    have : (ψ : E ⊗[F] P → L) = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) ∘ TensorProduct.comm F E P :=
      funext hψ
    rw [this]; exact hbij.comp (TensorProduct.comm F E P).bijective
  have hι : Function.Injective (ι.baseChange E) := by
    have h0 : Function.Injective ι := e.symm.injective.comp (Pi.single_injective i)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap ι h0
  have hΦ : Function.Injective Φ := hv.1.comp (hψb.1.comp hι)
  have hΦt : ∀ (a : E) (x : K i), Φ (a ⊗ₜ x) =
      a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v) := by
    intro a x
    simp [Φ, φ, ψ, ι, incl, LinearMap.liftBaseChange_tmul, Matrix.smul_mulVec]
  have hrange : LinearMap.range Φ = LinearMap.range (factorIdem e i).mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        refine ⟨a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v), ?_⟩
        rw [hΦt, Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
        simp
      | add x y hx hy => rw [map_add Φ]; exact add_mem hx hy
    · rintro _ ⟨w, rfl⟩
      obtain ⟨l, rfl⟩ := hv.2 w
      obtain ⟨s, rfl⟩ := hψb.2 l
      change (factorIdem e i).mulVecLin (φ (ψ s)) ∈ LinearMap.range Φ
      induction s using TensorProduct.induction_on with
      | zero => simp [φ]
      | tmul a p =>
        refine ⟨a ⊗ₜ (e p i), ?_⟩
        rw [hΦt]
        simp only [ψ, incl, LinearMap.liftBaseChange_tmul, Matrix.mulVecLin_apply]
        have hc : (((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) = a • ((p : L) : Matrix (Fin n) (Fin n) E) := rfl
        change _ = factorIdem e i *ᵥ ((((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v)
        rw [hc, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
      | add x y hx hy =>
        rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact add_mem hx hy
  rw [Matrix.rank, ← hrange, LinearMap.finrank_range_of_inj hΦ]

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem eq_zero_of_mulVec {M : Matrix (Fin n) (Fin n) E} (h : ∀ w, M *ᵥ w = 0) : M = 0 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.mulVec_single_one] using this

theorem rank_pos_of_ne_zero {M : Matrix (Fin n) (Fin n) E} (hM : M ≠ 0) : 0 < M.rank := by
  refine Nat.pos_of_ne_zero fun h => hM (eq_zero_of_mulVec fun w => ?_)
  rw [Matrix.rank, Submodule.finrank_eq_zero] at h
  have : M.mulVecLin w ∈ LinearMap.range M.mulVecLin := ⟨w, rfl⟩
  rw [h] at this
  exact (Submodule.mem_bot E).1 this

theorem eq_one_of_idem_rank {M : Matrix (Fin n) (Fin n) E} (hM : M * M = M) (hr : M.rank = n) : M = 1 := by
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hr, Module.finrank_fin_fun]
  have hu : ∀ u, M *ᵥ u = u := by
    intro u
    obtain ⟨w, hw⟩ : u ∈ LinearMap.range M.mulVecLin := htop ▸ Submodule.mem_top
    rw [← hw, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hM]
  have h0 := eq_zero_of_mulVec (M := M - 1) fun w => by rw [Matrix.sub_mulVec, hu, Matrix.one_mulVec, sub_self]
  exact sub_eq_zero.1 h0

theorem two_le_of_decomp {P : Type} [CommRing P] [Algebra F P] {k' : ℕ} {K' : Fin k' → Type}
    [∀ i, Field (K' i)] [∀ i, Algebra F (K' i)] (e' : P ≃ₐ[F] ∀ i, K' i) (hk' : 2 ≤ k')
    (e : P ≃ₐ[F] ∀ i, K i) (i : Fin k) : ∃ j, j ≠ i := by
  by_contra hne
  simp only [not_exists, ne_eq, not_not] at hne
  let a : Fin k' := ⟨0, by omega⟩
  let b : Fin k' := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  let q : P := e'.symm (Pi.single a 1)
  have hqq : q * q = q := by
    apply e'.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, ← Pi.single_mul, one_mul]
  have hq : IsIdempotentElem (e q i) := by
    show e q i * e q i = e q i
    rw [← Pi.mul_apply, ← map_mul, hqq]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hq with h | h
  · have : e q = 0 := funext fun j => by rw [hne j]; exact h
    have h2 := congrFun (e'.symm_apply_eq.1 (e.map_eq_zero_iff.1 this)) a
    simp at h2
  · have : e q = 1 := funext fun j => by rw [hne j]; exact h
    have h1 : q = 1 := by rw [← map_one e] at this; exact e.injective this
    have h2 := congrFun (e'.symm_apply_eq.1 h1) b
    simp [Pi.single_apply, hab.symm] at h2

theorem factorIdem_ne_one (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (hj : ∃ j, j ≠ i) :
    factorIdem e i ≠ 1 := by
  intro h
  obtain ⟨j, hj⟩ := hj
  have h1 : e.symm (Pi.single i 1) = 1 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) j
  simp [Pi.single_apply, hj] at h2

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

theorem factorIdem_orthSplit_rank : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)] (e : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) (i : Fin k), GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i).rank = Module.finrank D.host.E (TensorProduct D.host.F D.host.E (Kf i)) := by
  intro hRS D V γ hss k Kf _ _ e i hnf
  have hreg := GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS γ hss
  obtain ⟨hA, hP, -⟩ := hRS.1 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg
  obtain ⟨-, k', K', _, _, ⟨e'⟩, hk', -⟩ := hnf
  have hj := two_le_of_decomp e' hk' e i
  refine ⟨⟨factorIdem_mul_self e i, factorIdem_selfAdj e i, factorIdem_orth e i, factorIdem_comm e i,
    rank_pos_of_ne_zero (factorIdem_ne_zero e i), lt_of_le_of_ne (Matrix.rank_le_width _) fun h =>
      factorIdem_ne_one e i hj (eq_one_of_idem_rank (factorIdem_mul_self e i) h)⟩,
    rank_factorIdem hA hP e i⟩

end GlobalTheory.FactorSplit
end

