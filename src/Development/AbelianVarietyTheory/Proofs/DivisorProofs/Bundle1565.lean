module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
section
open NumberField IsDedekindDomain

namespace GlobalTheory.AdelicCoordSB

theorem finprod_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ φ hSB hae
  classical
  refine ⟨?_, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hae⟩
  let L : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), Set (κ → v.adicCompletion F) :=
    fun v => {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
  let S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := {v | ¬ φ v = Set.indicator (L v) 1}
  have hS : S.Finite := Filter.eventually_cofinite.1 hae
  let ev : (κ → FiniteAdeleRing (𝓞 F) F) → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → v.adicCompletion F) :=
    fun y v i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)
  have hev : ∀ y v i, ev y v i = (y i).1 v := fun _ _ _ => rfl
  have hcont : ∀ v, Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => ev y v := fun v =>
    continuous_pi fun i => (RestrictedProduct.continuous_eval (R := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      w.adicCompletion F) (A := fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v).comp
      (continuous_apply i)
  have hfin : ∀ y, (Function.mulSupport fun v => φ v (ev y v)).Finite := by
    intro y
    have hint : ∀ᶠ v in Filter.cofinite, ev y v ∈ L v :=
      Filter.eventually_all.2 fun i => (y i).2
    refine (Filter.eventually_cofinite.1 (hae.and hint)).subset ?_
    intro w hw h'
    apply hw
    simp only
    rw [h'.1, Set.indicator_of_mem h'.2]
    rfl
  change IsLocallyConstant fun y => ∏ᶠ v, φ v (ev y v)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  by_cases hy : ∀ v ∉ S, ev y v ∈ L v
  ·
    let G : Set (κ → FiniteAdeleRing (𝓞 F) F) := {z | ∀ v ∉ S, ev z v ∈ L v}
    have hGe : G = ⋂ i, (fun z : κ → FiniteAdeleRing (𝓞 F) F => z i) ⁻¹'
        {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ S → x.1 v ∈ v.adicCompletionIntegers F} := by
      ext z
      simp only [G, L, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, hev]
      exact ⟨fun h i v hv => h v hv i, fun h v hv i => h i v hv⟩
    have hGo : IsOpen G := by
      rw [hGe]
      exact isOpen_iInter_of_finite fun i =>
        (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)).preimage
          (continuous_apply i)
    have heq : ∀ z ∈ G, ∏ᶠ v, φ v (ev z v) = ∏ v ∈ hS.toFinset, φ v (ev z v) := by
      intro z hz
      refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      by_contra hvS
      apply hv
      have hφ : φ v = Set.indicator (L v) 1 := not_not.1 hvS
      simp only
      rw [hφ, Set.indicator_of_mem (hz v hvS)]
      rfl
    have hlc : IsLocallyConstant fun z : κ → FiniteAdeleRing (𝓞 F) F => ∏ v ∈ hS.toFinset, φ v (ev z v) := by
      have : ∀ v, IsLocallyConstant fun z : κ → FiniteAdeleRing (𝓞 F) F => φ v (ev z v) := fun v =>
        (hSB v).1.comp_continuous (hcont v)
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun z => ?_
      have h2 : ∀ᶠ w in nhds z, ∀ v ∈ hS.toFinset, φ v (ev w v) = φ v (ev z v) :=
        (Filter.eventually_all_finset _).2 fun v _ => (IsLocallyConstant.iff_eventually_eq _).1 (this v) z
      filter_upwards [h2] with w hw
      exact Finset.prod_congr rfl hw
    filter_upwards [hGo.mem_nhds hy, (IsLocallyConstant.iff_eventually_eq _).1 hlc y] with z hz hz'
    rw [heq z hz, heq y hy]
    exact hz'
  ·
    push_neg at hy
    obtain ⟨v, hvS, hvL⟩ := hy
    have hφ : φ v = Set.indicator (L v) 1 := not_not.1 hvS
    let U : Set (κ → FiniteAdeleRing (𝓞 F) F) := {z | ev z v ∉ L v}
    have hLc : IsClosed (L v) := by
      have e : L v = Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        ext x; simp [L]
      rw [e]
      exact isClosed_set_pi fun _ _ => (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).isClosed
    have hUo : IsOpen U := hLc.isOpen_compl.preimage (hcont v)
    have h0 : ∀ z ∈ U, ∏ᶠ w, φ w (ev z w) = 0 := fun z hz =>
      finprod_eq_zero _ v (by show φ v (ev z v) = 0; rw [hφ, Set.indicator_of_notMem hz]) (hfin z)
    filter_upwards [hUo.mem_nhds hvL] with z hz
    rw [h0 z hz, h0 y hvL]

end GlobalTheory.AdelicCoordSB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeConjDirectSumTraceSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (skewGram)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped nonZeroDivisors
open GlobalTheory.TripleSpaceW (conjSub mem_conjSub conjO coe_conjO)
open GlobalTheory.SkewLat (scLat pairLat)
open GlobalTheory.SkewLat.DualPair

noncomputable section

namespace GlobalTheory.SkewLat.DualPairConj

variable {D : D7}

theorem mem_conj_scLat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {y : Fin n → D.host.E} :
    y ∈ conjSub (scLat D.host.AA (conjSub Λ)) ↔ ∀ c ∈ D.host.AA⁻¹, star c • y ∈ Λ := by
  rw [mem_conjSub, GlobalTheory.SkewLat.mem_scLat]
  refine forall_congr' fun c => forall_congr' fun _ => ?_
  have e : star (c • star y) = star c • y := by
    ext i; simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', star_star]
  rw [mem_conjSub, e]

theorem star_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin n → D.host.E} (hs : s ∈ Λ) : star a • s ∈ conjSub (scLat D.host.AA (conjSub Λ)) := by
  refine mem_conj_scLat.2 fun c hc => ?_
  obtain ⟨b, hb⟩ := int_of_inv_mul hc ha
  rw [smul_smul, ← star_mul', ← hb, ← coe_conjO]
  exact Λ.smul_mem (conjO b) hs

theorem fwd' (hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar) (S : HSp D)
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (hΛ : IsSelfDualC S Λ) {x y : Fin S.rank → D.host.E} (hx : x ∈ conjSub (scLat D.host.AA (conjSub Λ)))
    (hy : y ∈ conjSub (scLat D.host.AA (conjSub Λ))) :
    IntTr (D.host.xi0 * hS S x y) := by
  rw [mem_conj_scLat] at hx hy
  have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, ∀ v ∈ D.host.AA * D.host.AA⁻¹,
      IntTr (D.host.xi0 * u * star v * hS S x y) := by
    intro u hu
    refine FractionalIdeal.mul_induction_on hu
      (C := fun u => ∀ v ∈ D.host.AA * D.host.AA⁻¹, IntTr (D.host.xi0 * u * star v * hS S x y)) ?_ ?_
    · intro a ha c hc v hv
      refine FractionalIdeal.mul_induction_on hv
        (C := fun v => IntTr (D.host.xi0 * (a * c) * star v * hS S x y)) ?_ ?_
      · intro a' ha' c' hc'
        obtain ⟨b, hb⟩ := (hΛ.2 (star c' • y)).1 (hy c' hc') (star c • x) (hx c hc)
        have e1 : D.host.xi0 * (a * c) * star (a' * c') * hS S x y = D.host.xi0 * a * star a' * (b : D.host.E) := by
          rw [hb, show (∑ i, ∑ j, star ((star c • x) i) * S.gram i j * (star c' • y) j) =
            hS S (star c • x) (star c' • y) from rfl, hS_smul, star_mul', star_star]
          ring
        rw [e1]
        exact ((intTr_iff_mem_dual _).2 (xi_mem hs ha ha')).mul_int b
      · intro v1 v2 h1 h2
        rw [star_add, show D.host.xi0 * (a * c) * (star v1 + star v2) * hS S x y =
          D.host.xi0 * (a * c) * star v1 * hS S x y + D.host.xi0 * (a * c) * star v2 * hS S x y by ring]
        exact h1.add h2
    · intro u1 u2 h1 h2 v hv
      rw [show D.host.xi0 * (u1 + u2) * star v * hS S x y =
        D.host.xi0 * u1 * star v * hS S x y + D.host.xi0 * u2 * star v * hS S x y by ring]
      exact (h1 v hv).add (h2 v hv)
  have := key 1 one_mem_AA_mul 1 one_mem_AA_mul
  simpa using this

theorem bwd' (hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) (S : HSp D)
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ) {y : Fin S.rank → D.host.E}
    (h : ∀ a ∈ D.host.AA, ∀ s ∈ Λ, IntTr (D.host.xi0 * hS S (star a • s) y)) :
    y ∈ conjSub (scLat D.host.AA (conjSub Λ)) := by
  refine mem_conj_scLat.2 fun c hcA => ?_
  refine (hΛ.2 (star c • y)).2 fun s hs => ?_
  have hmem : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) ≤ D.host.AAbar *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) := by
    rw [show D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) =
      FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar by ring, hX,
      ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    have h1 := (intTr_iff_mem_dual _).1 (h j hj s hs)
    rw [hS_smul_left, star_star] at h1
    rw [smul_mul_assoc, show hS S s y * D.host.xi0 * j = D.host.xi0 * (j * hS S s y) by ring]
    exact Submodule.smul_mem _ z h1
  have hXne : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA ≠ 0 :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 xi_ne) AA_ne
  have hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) ≤ D.host.AAbar := by
    calc FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y)
        = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
      _ ≤ D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)⁻¹ := by gcongr
      _ = D.host.AAbar := by rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
  obtain ⟨b, hb⟩ := int_of_inv_mul hcA (hc _ (hle (FractionalIdeal.mem_spanSingleton_self _ _)))
  refine ⟨conjO b, ?_⟩
  have e : ((conjO b : 𝓞 D.host.E) : D.host.E) = hS S s (star c • y) := by
    rw [coe_conjO, hb, star_mul', star_star, hS_smul_right]
  first | exact e | exact e.symm

end GlobalTheory.SkewLat.DualPairConj


open GlobalTheory.SkewLat.DualPairConj in
theorem GlobalTheory.SkewLat.pairLat_conj_trace_selfDual : ∀ {D : D7} (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)},
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E),
    y ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e ↔
      ∀ x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (skewGram A B e) y x)) := by
  intro D A B ΛA ΛB hA hB d e y
  have hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar := fun c h => by
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h
  have hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA := by
    first | exact GlobalTheory.star_mem_AA_of_mem_AAbar | exact GlobalTheory.star_mem_AA_of_mem_AAbar D | (intros; apply GlobalTheory.star_mem_AA_of_mem_AAbar; assumption)
  constructor
  · intro hy x hx o
    have hy' := GlobalTheory.SkewLat.mem_pairLat.1 hy
    have hx' := GlobalTheory.SkewLat.mem_pairLat.1 hx
    rw [form_skewGram, mul_add]
    exact ((fwd hs A hA hx'.1 hy'.1).add (fwd' hs B hB hx'.2 hy'.2)) o
  · intro h
    refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨bwd hc A hA fun a ha s hs' => ?_, bwd' hc B hB fun a ha s hs' => ?_⟩
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun k => a * s k) (fun _ => 0) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = a • s := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = 0 := by ext k; simp [x]
      have hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact smul_mem_scLat ha hs'
        · rw [hxB]; exact zero_mem _
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, add_zero] at this
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun _ => 0) (fun k => star a * s k) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = 0 := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = star a • s := by ext k; simp [x]
      have hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact zero_mem _
        · rw [hxB]; exact star_smul_mem ha hs'
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, zero_add] at this

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLatticeVacuumEigen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

namespace GlobalTheory.HeisLatVac

theorem vacFn_apply_base_add {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hY : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (u : (κ → K) × (κ → K)) (hu : u ∈ Λ) :
    vacFn ψ₀ Λ χ x₀ (x₀ + u.1) = χ u * ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
  have h : ∃ u' ∈ Λ, x₀ + u.1 = x₀ + u'.1 := ⟨u, hu, rfl⟩
  rw [vacFn, dite_eq_left h]
  obtain ⟨hu', he⟩ := h.choose_spec
  set u' := h.choose
  have h1 : u.1 = u'.1 := add_left_cancel he
  have hd : ((0 : κ → K), u.2 - u'.2) = u - u' := by
    ext <;> simp [h1]
  have hdm : ((0 : κ → K), u.2 - u'.2) ∈ Λ := hd ▸ sub_mem hu hu'
  have hsum : u = u' + ((0 : κ → K), u.2 - u'.2) := by rw [hd]; abel
  have hχ : χ u = χ u' * ψ₀ (x₀ ⬝ᵥ (u.2 - u'.2)) * ψ₀ (⅟(2 : K) * (u'.1 ⬝ᵥ (u.2 - u'.2) - (0 : κ → K) ⬝ᵥ u'.2)) := by
    conv_lhs => rw [hsum]
    rw [hco u' hu' _ hdm, hY _ hdm]
  rw [hχ, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  rw [h1]
  simp only [dotProduct_sub, zero_dotProduct]
  ring

theorem schr_vacFn : ∀ {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, ∀ w ∈ Λ, ψ₀ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) = 1) →
    ∀ w ∈ Λ, GlobalTheory.WeilM.schr ψ₀ w (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) = χ w • GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀ := by
  intro K κ _ _ _ ψ₀ Λ χ x₀ hco hY hiso w hw
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  by_cases hx : ∃ u ∈ Λ, x = x₀ + u.1
  · obtain ⟨u, hu, rfl⟩ := hx
    have e : x₀ + u.1 + w.1 = x₀ + (u + w).1 := by simp [add_assoc]
    rw [e, vacFn_apply_base_add ψ₀ Λ χ x₀ hco hY (u + w) (add_mem hu hw),
      vacFn_apply_base_add ψ₀ Λ χ x₀ hco hY u hu, hco u hu w hw]
    have h1 : ψ₀ ((x₀ + u.1) ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2)) *
        ψ₀ (-(x₀ ⬝ᵥ (u + w).2) - ⅟(2 : K) * ((u + w).1 ⬝ᵥ (u + w).2)) =
        ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      have : (x₀ + u.1) ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) + ⅟(2 : K) * (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) +
          (-(x₀ ⬝ᵥ (u + w).2) - ⅟(2 : K) * ((u + w).1 ⬝ᵥ (u + w).2)) =
          (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) + (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
        simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
        linear_combination (-(w.1 ⬝ᵥ u.2)) * (invOf_mul_self (2 : K))
      rw [this, AddChar.map_add_eq_mul, hiso u hu w hw, one_mul]
    rw [← h1]
    ring
  · have hx' : ¬∃ u ∈ Λ, x + w.1 = x₀ + u.1 := by
      rintro ⟨u', hu', he⟩
      refine hx ⟨u' - w, sub_mem hu' hw, ?_⟩
      rw [Prod.fst_sub, ← add_sub_assoc, ← he, add_sub_cancel_right]
    simp only [vacFn, dif_neg hx, dif_neg hx', mul_zero]

end GlobalTheory.HeisLatVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanScaledMappedRowDetsEqPowMulSpan
section
open NumberField

open Pointwise
namespace GlobalTheory

theorem twistDet_rows {E K : Type} [Field E] [Field K] (τE : E →+* K) {p : ℕ}
    (β : Fin p → K) (c : Fin p → Fin p → E) :
    (Matrix.of fun i => β i • fun a => τE (c i a)).det = (∏ i, β i) * τE (Matrix.of c).det := by
  have h : (Matrix.of fun i => β i • fun a => τE (c i a)) =
      Matrix.diagonal β * (Matrix.of c).map τE := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [h, Matrix.det_mul, Matrix.det_diagonal, RingHom.map_det]
  rfl

theorem pow_eq_span_prod_set {K : Type} [Field K] [NumberField K] (p : ℕ) (𝔟 : Submodule (𝓞 K) K) :
    𝔟 ^ p = Submodule.span (𝓞 K) (∏ _i ∈ (Finset.univ : Finset (Fin p)), (𝔟 : Set K)) := by
  rw [← Submodule.prod_span]
  simp [Finset.prod_const]

theorem span_twistDets_eq {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)) :
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := by
  set S : Set K := {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det}
    with hS
  have hpow := pow_eq_span_prod_set p 𝔟
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    choose β hβ c hc hyc using hy
    have hy' : y = fun i => β i • fun a => τE (c i a) := funext hyc
    subst hy'
    rw [twistDet_rows]
    refine Submodule.mul_mem_mul ?_ ?_
    · rw [hpow]
      refine Submodule.subset_span ?_
      rw [Set.mem_finsetProd]
      exact ⟨β, fun {i} _ => hβ i, rfl⟩
    · exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, rfl⟩, rfl⟩
  · rw [Submodule.mul_le]

    have key : ∀ c : Fin p → Fin p → E, (∀ i, c i ∈ Λ) →
        ∀ m ∈ 𝔟 ^ p, m * τE (Matrix.of c).det ∈ Submodule.span (𝓞 K) S := by
      intro c hc m hm
      rw [hpow] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        rw [Set.mem_finsetProd] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        refine Submodule.subset_span ⟨fun i => β i • fun a => τE (c i a), fun i => ?_, ?_⟩
        · exact ⟨β i, hβ (Finset.mem_univ i), c i, hc i, rfl⟩
        · rw [twistDet_rows]
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
      | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx
    have key2 : ∀ e ∈ GlobalTheory.IdxTensor.dets E p Λ, ∀ m ∈ 𝔟 ^ p,
        m * τE e ∈ Submodule.span (𝓞 K) S := by
      intro e he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, hc, rfl⟩ := hx
        exact key c hc
      | zero => intro m _; simp
      | add x y _ _ hx hy =>
        intro m hm; rw [map_add (f := _), mul_add]; exact add_mem (hx m hm) (hy m hm)
      | smul a x _ hx =>
        intro m hm
        rw [Algebra.smul_def, map_mul]
        have : τE (algebraMap (𝓞 E) E a) = ((τ a : 𝓞 K) : K) := hτ a
        rw [this, mul_left_comm, ← Algebra.smul_def (τ a)]
        · exact Submodule.smul_mem _ (τ a) (hx m hm)
    intro m hm n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      exact key2 e he m hm
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExists
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SplitEmbed

theorem exists_algHom_of_splitsFully : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl (F := F), SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ σ h v hs
  classical
  haveI hprime : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hne : v.asIdeal.under ℤ ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) hb)
  obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.principal (v.asIdeal.under ℤ))
  have hq' : v.asIdeal.under ℤ = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hne (by rw [hq']; simp)
  have hqp : Prime q := by
    rw [← Ideal.span_singleton_prime hq0, ← hq']
    exact hprime
  set p := q.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [hq', hpdef, Int.span_natAbs]
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
    have : (p : ℤ) ∈ v.asIdeal.under ℤ := by rw [hspan]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have hcount : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
    have := hs
    unfold SplitsFully at this
    rw [hspan] at this
    exact this
  rw [GlobalTheory.AdelicU.nonempty_split_iff h]
  exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two h.2.2.1 hp hcount v hpv

end GlobalTheory.SplitEmbed
end

