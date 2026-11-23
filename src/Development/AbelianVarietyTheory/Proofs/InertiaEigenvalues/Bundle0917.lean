module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0913
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0886
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0893
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntFormDescentBelow
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.XiIntSteps

theorem exists_local_basis {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) {V : Type} [AddCommGroup V]
    [Module F V] (C : Submodule F V) [FiniteDimensional F C] (Int : V → Prop) (h0 : Int 0)
    (hadd : ∀ f g, Int f → Int g → Int (f + g)) (hsmul : ∀ (a : F) f, p.valuation F a ≤ 1 → Int f → Int (a • f))
    (hbd : ∀ f ∈ C, ∃ κ : F, κ ≠ 0 ∧ Int (κ • f)) {M : ℕ} (g : Fin M → V) (hg : ∀ i, g i ∈ C)
    (hgen : ∀ f ∈ C, Int f → ∃ o : Fin M → F, (∀ i, p.valuation F (o i) ≤ 1) ∧ f = ∑ i, o i • g i) :
    ∃ (m : ℕ) (β : Fin m → V), (∀ k, β k ∈ C ∧ Int (β k)) ∧ (∀ f ∈ C, ∃ c : Fin m → F, f = ∑ k, c k • β k) ∧
      ∀ c : Fin m → F, Int (∑ k, c k • β k) → ∀ k, p.valuation F (c k) ≤ 1 := by
  classical
  let B₀ := Module.finBasis F C
  choose κ hκ0 hκ using fun i => hbd (B₀ i : V) (B₀ i).2
  let B := B₀.unitsSMul fun i => Units.mk0 (κ i) (hκ0 i)
  have hB : ∀ i, ((B i : C) : V) = κ i • (B₀ i : V) := fun i => by
    simp [B, Module.Basis.unitsSMul_apply, Units.smul_def]
  let e : (Fin (Module.finrank F C) → F) →ₗ[F] V := C.subtype ∘ₗ (B.equivFun.symm : _ →ₗ[F] C)
  have heC : ∀ x, e x ∈ C := fun x => (B.equivFun.symm x).2
  have he1 : ∀ f : C, e (B.equivFun f) = f := fun f => by simp [e]
  have heinj : Function.Injective e := Subtype.val_injective.comp B.equivFun.symm.injective
  have hsingle : ∀ i, e (Pi.single i 1) = κ i • (B₀ i : V) := fun i => by
    rw [← hB, ← he1 (B i)]
    congr 1
    funext k
    simp [Module.Basis.equivFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  let S : Set (Fin (Module.finrank F C) → F) := {x | Int (e x)}
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F))
    (fun ki : Fin M × Fin (Module.finrank F C) => B.equivFun ⟨g ki.1, hg ki.1⟩ ki.2)
  have hvle : ∀ s : 𝓞 F, p.valuation F (algebraMap (𝓞 F) F s) ≤ 1 := fun s => by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact p.intValuation_le_one s
  obtain ⟨m, b, hbM, hbsp, hbli⟩ := GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi p _ S (by show Int (e 0); rw [map_zero]; exact h0)
    (fun x hx y hy => by show Int (e (x + y)); rw [map_add (f := _)]; exact hadd _ _ hx hy)
    (fun a ha x hx => by show Int (e (a • x)); rw [map_smul]; exact hsmul _ _ ha hx)
    (fun i => by show Int (e _); rw [hsingle]; exact hκ i)
    ⟨algebraMap (𝓞 F) F d, (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.coe_ne_zero d),
      fun x hx i => by
        obtain ⟨o, ho, hxo⟩ := hgen (e x) (heC x) hx
        have hx' : x = ∑ k, o k • B.equivFun ⟨g k, hg k⟩ := heinj (by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [hxo, map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, he1])
        rw [hx', Finset.sum_apply, Finset.mul_sum]
        refine Valuation.map_sum_le _ fun k _ => ?_
        obtain ⟨r, hr⟩ := hd (k, i)
        rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, map_mul, ← Algebra.smul_def]
        refine mul_le_one' (ho k) ?_
        rw [← hr]
        exact hvle r⟩
  refine ⟨m, fun k => e (b k), fun k => ⟨heC _, hbM k⟩, fun f hf => ?_, fun c hc k => ?_⟩
  · have hxsp : B.equivFun ⟨f, hf⟩ ∈ Submodule.span F (Set.range b) := by
      rw [← Finset.univ_sum_single (B.equivFun ⟨f, hf⟩)]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Pi.single i (B.equivFun ⟨f, hf⟩ i) = B.equivFun ⟨f, hf⟩ i • (Pi.single i (1 : F) : Fin _ → F) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨a, -, ha⟩ := hbsp (Pi.single i 1) (by show Int (e _); rw [hsingle]; exact hκ i)
      rw [ha]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hxsp
    refine ⟨c, ?_⟩
    have := he1 ⟨f, hf⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum] at this
    exact this.symm.trans (Finset.sum_congr rfl fun k _ => map_smul _ _ _)
  · have hy : (∑ k, c k • b k) ∈ S := by
      show Int (e _)
      convert hc using 1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
    obtain ⟨a, ha, hya⟩ := hbsp _ hy
    have hz : ∑ k, (c k - a k) • b k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]; rw [← hya, sub_self]
    rw [sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hbli _ hz k)]
    exact ha k

theorem intForm_descent_below (l e : ℕ) (hl : l.Prime) : ∃ c₀ : ℕ, ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j →
    ∀ w : WeightFamilies.Wt D j, w.LastPos → Dom (wtA w) w.n →
    holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) ''
      {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)}) →
    (∀ k ∈ T.Kf j T.σ₀, ∀ h, T.mu j T.σ₀ (h * k) = T.mu j T.σ₀ h) →
    ∀ C : Cover T j T.σ₀, C.IsUnif → C.IsPinned (wtA w) w.n →
    ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)),
      la.asIdeal.comap (RingOfIntegers.mapRingHom C.inc) = p.asIdeal →
      ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → ((l : ℕ) : 𝓞 C.d.c₂.F) ∉ la.asIdeal ^ (e + 1) →
      ∀ φ ∈ C.intForms (wtA w) w.n {la}, (∀ k ∈ T.Kf j T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j T.σ₀) → ℂ)), (∀ i, la.valuation C.d.c₂.F (x i) ≤ 1) ∧
          (∀ i, ψ i ∈ baseInt T j T.σ₀ (wtA w) w.n {p}) ∧ ((l : ℂ) ^ c₀) • φ = ∑ i, C.σ₂ (x i) • ψ i := by
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.TowerDifferent.relDifferent_order_bounded l e hl
  refine ⟨c, ?_⟩
  intro D T hL j hj w hlast hD hspan hK C hU hP la p hp0 hl1 hl2 φ hφ hφK
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  have hp : la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal := by
    rw [← hp0]; ext x; rfl
  have hσ := T.toCore.good_σ₀
  have hlp : ((l : ℕ) : 𝓞 T.Q.c.F) ∈ p.asIdeal := by
    rw [← hp0, Ideal.mem_comap, map_natCast]; exact hl1
  have hgood : T.Q.l.GoodAt l :=
    Formalism.L2.Pj.goodAt_of_two_primes hL.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl
  have hfd := hL.cuspFD _ hj _ _ hD
  obtain ⟨M, g, hg, hgen⟩ := GlobalTheory.SupFinite.supSet_finitelyGenerated _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp
    hgood (wtA w) w.n hD hfd
  have hval := GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg _ _ _ _ (T.Q.Xo j) T.Q.c p
  obtain ⟨m, β, hβ, hspanβ, hprim⟩ := exists_local_basis p (cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n)
    (GlobalTheory.GoodPts.BddAll (T.Q.Xo j) T.Q.c p 1)
    ((hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top))
    (fun f g => GlobalTheory.GoodPtsModel.bddAll_add)
    (fun a f ha hf => by
      by_cases h0 : a = 0
      · subst h0
        set_option synthInstance.maxHeartbeats 100000 in
          rw [zero_smul]
        exact (hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top)
      have hv : (0 : ℤ) ≤ vLa p a := by
        have hne : p.valuation T.Q.c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 h0
        have := (WithZero.log_le_log hne one_ne_zero).2 ha
        simp only [WithZero.log_one] at this
        simp only [vLa]; omega
      exact (GlobalTheory.GoodPtsModel.smul_mem_supSet (W := ⊤) hv ⟨trivial, hf⟩).2)
    (fun f hf => by
      obtain ⟨κ, h1, h2⟩ := _root_.GlobalTheory.CuspBound.exists_bddAll_cusp _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp hgood (wtA w) w.n f hD hf
      exact ⟨κ, h1, (GlobalTheory.GoodPtsModel.bddAll_iff_smul _ _).1 h2⟩)
    g (fun i => (hg i).1) (fun f hf hb => hgen f ⟨hf, hb⟩)
  have hβs : ∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧
      rdU (T.U j T.σ₀) (β k) ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) := fun k =>
    ⟨cusp_le_sec _ _ _ _ _ (hβ k).1, ReciprocityTheory.ChartRestriction.G.PullbackSections.rdC_mem_holSub0 T.good_σ₀ (wtA w) w.n ⟨β k, (hβ k).1⟩⟩
  obtain ⟨m', x, ψ, hψ, hφe⟩ := _root_.GlobalTheory.CoverFormDesc.cover_form_desc D T hL j hj T.σ₀ hσ C hU _ _ hD hP hspan hK φ
    (C.intForms_subset _ _ _ hφ) hφK
  have hcc' : ∀ i, ∃ cc : Fin m → T.Q.c.F, ψ i = ∑ k, T.σ₀ (cc k) • T.phiJ j T.σ₀ (wtA w) (β k) := fun i => by
    obtain ⟨f, hf, hfe⟩ := hψ i
    obtain ⟨cc, hcc⟩ := hspanβ f (_root_.GlobalTheory.CuspAllEmb.mem_cuspA_of_rdU_mem_holSub0 D T hL j hj w hlast f hf.1 hf.2)
    refine ⟨cc, ?_⟩
    rw [← hfe, hcc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CoreJ.phiJ, map_sum, map_smulₛₗ, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  choose cc hcc using hcc'
  have hσ₂ : ∀ z, C.σ₂ (C.inc z) = T.σ₀ z := fun z => congrArg (fun f => f z) hU.2.2.1
  let y : Fin m → C.d.c₂.F := fun k => ∑ i, x i * C.inc (cc i k)
  have hsum : φ = ∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k) := by
    rw [hφe]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, hcc, Finset.smul_sum, smul_smul, map_sum, Finset.sum_smul, map_mul, hσ₂]
    exact Finset.sum_comm
  have hφ' : (∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k)) ∈ C.intForms (wtA w) w.n {la} := hsum ▸ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.T.traceCombination_coverForm_integral_over_prime D T hL j hj T.σ₀ hσ _ _ hD hspan hK C hU hP la p hp m β hβs
    (fun k => (hval _).1 (hβ k).2) y hφ'
  have hdiff : ∀ k, ∀ d ∈ differentIdeal (𝓞 T.Q.c.F) (𝓞 C.d.c₂.F),
      la.valuation C.d.c₂.F (y k * (d : C.d.c₂.F)) ≤ 1 := fun k =>
    _root_.GlobalTheory.InvDiffLocal.valuation_mul_different_le_one T.Q.c.F C.d.c₂.F la p hp (y k)
      ⟨N, fun b hb => hprim (fun k => Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) ((hval _).2 (hN b hb)) k⟩
  have hcd := hc T.Q.c.F C.d.c₂.F p la hp hl1 hl2
  refine ⟨m, fun k => (l : C.d.c₂.F) ^ c * y k, fun k => T.phiJ j T.σ₀ (wtA w) (β k), ?_, ?_, ?_⟩
  · exact fun k => _root_.GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal l c T.Q.c.F C.d.c₂.F la hl1 hcd (y k) (hdiff k)
  · refine fun k => ⟨β k, ⟨(hβs k).1, (hβs k).2, fun q hq => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff.1 hq]
    exact (hval _).1 (hβ k).2
  · rw [hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, map_mul, map_pow, map_natCast]

end GlobalTheory.XiIntSteps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealFockThetaLiftVanishingOfGeneratingVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GenRealFock

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem pureTensor_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (P Q : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ptP i t (P + Q) = R.ptP i t P + R.ptP i t Q := by
  unfold RealDat.ptP; exact map_add _ _ _

theorem pureTensor_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (c : ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ptP i t (c • P) = c • R.ptP i t P := by
  unfold RealDat.ptP; exact map_smul _ _ _

theorem downInt_add_f (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f f' : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f' * l (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y (f + f') l g = downInt R i t y f l g + downInt R i t y f' l g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp [thetaKO, add_mul]

theorem downInt_smul_f (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y (c • f) l g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp [thetaKO, mul_assoc]

theorem downInt_add_l (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l l' : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l' (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y f (l + l') g = downInt R i t y f l g + downInt R i t y f l' g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp [mul_add]

theorem downInt_smul_l (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y f (c • l) g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

theorem exists_bilin (R : RealDat D A Ks) (F : Face D A) (hG : GlobalTheory.LiftRows.Given R F) (hP : R.FullP)
    (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ∃ B : GA D (Wc D i) → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ,
      ∀ g P l, B g P l = downInt R i t y (R.ptP i t P) l g := by
  have hth := hG.core.thP.pt_theta i t
  have hint := fun f l g hf => _root_.GlobalTheory.DownLift.GenFinite.integrableOn_downIntegrand D G Pl0 T A Ks R F hG hP i t y f l g hf
  refine ⟨fun g => LinearMap.mk₂ ℂ (fun P l => downInt R i t y (R.ptP i t P) l g) ?_ ?_ ?_ ?_, fun g P l => rfl⟩
  · intro P Q l
    rw [pureTensor_add, downInt_add_f _ _ _ _ _ _ _ _ (hint _ l g (hth P)) (hint _ l g (hth Q))]
  · intro c P l
    rw [pureTensor_smul, downInt_smul_f, smul_eq_mul]
  · intro P l l'
    exact downInt_add_l _ _ _ _ _ _ _ _ (hint _ l g (hth P)) (hint _ l' g (hth P))
  · intro c P l
    rw [downInt_smul_l, smul_eq_mul]

theorem gen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t (R.ioP i x w)) l g = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t P) l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hio P l g
  obtain ⟨B, hB⟩ := exists_bilin R F hG hP i t y
  have hth := hG.core.thP.pt_theta i t
  have key := (_root_.GlobalTheory.GenByIo.forms_vanish_of_io) D G Pl0 T A Ks R F hG hP i t (GA D (Wc D i)) B ?_ ?_ ?_ P g
  · rw [← hB, key, LinearMap.zero_apply]
  · intro j u hu P P' e l
    rw [hB, hB, e]
    exact (_root_.GlobalTheory.DownLift.downInt_realEquiv) D G Pl0 T A Ks R F hG hP i t y u hu _ (hth P) l j
  · intro τ Y hY P P' hd h0 j
    refine LinearMap.ext fun l => ?_
    rw [LinearMap.zero_apply, hB]
    refine (_root_.GlobalTheory.DownLift.GenReal.downInt_lie) D G Pl0 T A Ks R F hG hP i t y τ Y hY P P' hd l (fun g' => ?_) j
    rw [← hB, h0 g', LinearMap.zero_apply]
  · intro x w j
    refine LinearMap.ext fun l => ?_
    rw [LinearMap.zero_apply, hB]
    exact hio x w l j

end GlobalTheory.GenRealFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerMulTorusShiftAddEqSphericalProductStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_mul_torusShift_add_eq_sphericalProduct : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((GlobalTheory.RamShift.shift m T ϖ).1 + l.1)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  first | exact @GlobalTheory.RamShift.whit_mul_tl_shift_add | exact GlobalTheory.RamShift.whit_mul_tl_shift_add | (intros; apply GlobalTheory.RamShift.whit_mul_tl_shift_add <;> assumption)
end

