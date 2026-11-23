module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0003
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.AutomorphicForms.MeasuresGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.BumpEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AmpSlot
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PairPosition
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.WeilBound.NonsplitUniqueness.Places

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AbsLast
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {v : Pl K}

private theorem fixed_fd (U : Subgroup (Gw n v)) (hU : CO U) (σ : SmIrr (Gw n v)) :
    FiniteDimensional ℂ (fixedVectors σ.ρ U) := by
  have h := PositivityTheory.Exh.irreducibleAdmissibleGL (v.adicCompletion K) n σ.V σ.ρ σ.smooth σ.irred
  have h2 := h.2 U hU.2 hU.1
  have e : GlobalTheory.PRep.fixed σ.ρ U = fixedVectors σ.ρ U := by
    ext x
    constructor
    · intro hx g hg
      simpa using hx ⟨g, hg⟩
    · intro hx g
      simpa using hx g g.2
  rw [← e]
  exact h2

private theorem td : TotallyDisconnectedSpace (Gw n v) := by
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) (v.adicCompletion K)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → v.adicCompletion K))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

end UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed

open UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed in
theorem UpperTheory.ConvolutionTheory.T.absLast :
    UpperTheory.ConvolutionTheory.T.AbsLast := by
  intro K _ _ n v _ _ m _ U hU ι _ τ a Z τ₀ c Z₀ hc hZ₀ h0 hZ hfix hid
  by_contra hno
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero hZ₀
  have hk : ((Multiset.filter (· = ζ) Z₀).card : ℂ) ≠ 0 := by
    have : 0 < (Multiset.filter (· = ζ) Z₀).card :=
      Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩
    exact_mod_cast this.ne'
  let σ : Option ι → SmIrr (Gw n v) := fun o => o.elim τ₀ τ
  let C : Option ι → ℂ := fun o => o.elim (c * ((Multiset.filter (· = ζ) Z₀).card : ℂ))
    (fun i => -(a i * ((Multiset.filter (· = ζ) (Z i)).card : ℂ)))
  haveI : m.IsMulRightInvariant := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL (v.adicCompletion K) n m
  haveI : LocallyCompactSpace (Gw n v) :=
    hU.1.locallyCompactSpace_of_mem_nhds_of_group (hU.2.mem_nhds U.one_mem)
  haveI : T2Space (Gw n v) := Units.isEmbedding_embedProduct.t2Space
  haveI : TotallyDisconnectedSpace (Gw n v) := td
  have key := UpperTheory.ConvolutionTheory.C.charIndep (Gw n v) m U hU (Option ι) σ C (fun o => fixed_fd U hU (σ o)) ?_ none hfix
  · have hset : {o : Option ι | Nonempty ((σ o).ρ.Equiv (σ none).ρ)} = {none} := by
      ext o
      cases o with
      | none => exact ⟨fun _ => rfl, fun _ => ⟨Representation.Equiv.refl (σ none).ρ⟩⟩
      | some i =>
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, reduceCtorEq, iff_false]
        exact fun h => hno ⟨i, h⟩
    rw [hset, finsum_mem_singleton] at key
    exact (mul_ne_zero hc hk) key
  · intro φ s hφ hinv hs
    have e := hid φ (s none) (fun i => s (some i)) hφ hinv (hs none) (fun i => hs (some i))
    have p := UpperTheory.ConvolutionTheory.C.powIndep (Option ι)
      (fun o => o.elim (c * s none) (fun i => -(a i * s (some i))))
      (fun o => o.elim Z₀ Z)
      (fun o => by cases o with
        | none => exact h0
        | some i => exact hZ i)
      (by
        filter_upwards [e] with j hj
        rw [Fintype.sum_option]
        simp only [Option.elim]
        have : ∑ i, -(a i * s (some i)) * ((Z i).map (· ^ j)).sum
            = -∑ i, a i * ((Z i).map (· ^ j)).sum * s (some i) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [this, ← hj]
        ring) ζ
    rw [Fintype.sum_option] at p ⊢
    simp only [Option.elim] at p
    have : ∑ i, C (some i) * s (some i)
        = ∑ i, -(a i * s (some i)) * ((Multiset.filter (· = ζ) (Z i)).card : ℂ) :=
      Finset.sum_congr rfl (fun i _ => by simp only [C, Option.elim]; ring)
    rw [this]
    have h1 : C none = c * ((Multiset.filter (· = ζ) Z₀).card : ℂ) := rfl
    rw [h1]
    linear_combination p
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDescOf
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

theorem haar_norm (K : Type) [Field K] [NumberField K] (n : ℕ) (x : Pl K) [MeasurableSpace (Gw n x)] [BorelSpace (Gw n x)] :
    ∃ mm : Measure (Gw n x), mm.IsHaarMeasure ∧ mm (GLnLocal.integralGL (x.adicCompletion K) n) = 1 := by
  have hc := GLnLocal.isCompact_integralGL (x.adicCompletion K) n
  have ho := GLnLocal.isOpen_integralGL (x.adicCompletion K) n
  let P : TopologicalSpace.PositiveCompacts (Gw n x) := ⟨⟨_, hc⟩, by
    change (interior (GLnLocal.integralGL (x.adicCompletion K) n : Set (Gw n x))).Nonempty
    rw [ho.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩

theorem coreDesc_of (hAbs : AbsLast) (hPull : PullBack) (hUnit : UnitTrace) (hOne : OneTerm) (hSum : SideSum) (hPS : PickS)
    (hPI : PickInf) (hTy : TyEx) (hTE : TermE) (hGood : GoodEx) (hPl : Places) (hOcc : OccursBasics)
    (hEig : EigBasic) (hCI : CI) (hGM : GM.GM) : CoreDesc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ θ hθ V Λ t hV hVθ hAt hOffA v w hv τ' hτ'
  obtain ⟨S, q, w₀, hvS, hqS, hq, hunr, hsph, hS'⟩ := hPS F E σ hσ hp n hn μE V Λ t hV hAt v
  have hne := (hPl F E hp).2.2.1
  obtain ⟨T, hTS, hmk, htyped, hrank, c, f₀, UF, hUF, hL⟩ := hTy F E σ hσ hp n hn μE V hV q w₀ hq S hqS hunr hsph
    (Function.update (fun u => (hne u).some) v w)
  have hw : T.mk' v = w := by rw [hmk, Function.update_self]
  clear hmk
  subst hw
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 htyped
  obtain ⟨m, hm, D, s, hs, νE, iE, νF, iF, b, a, aE, aF, hposition, harch, hAE, hAF, hpair, hua⟩ :=
    hPI F E σ hσ hp n hn μE μF u hu0
  letI : ∀ x : Pl E, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl E, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  letI : ∀ x : Pl F, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl F, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  have hmE : ∀ x : Pl E, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure := fun x => (haar_norm E n x).imp fun _ h => h.1
  have hmF : ∀ x : Pl F, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure ∧ mm (GLnLocal.integralGL (x.adicCompletion F) n) = 1 :=
    fun x => haar_norm F n x
  choose mE hmE using hmE
  choose mF hmF using hmF
  have hτ : ∀ x : Pl E, ∃ τ : SmIrr (Gw n x), Occurs μE V x τ := fun x => by
    haveI := hmE x
    exact (hOcc E n μE V x (mE x) hV).1
  choose τ₁ hτ₁ using hτ
  obtain ⟨τ, hτ, hτw⟩ : ∃ τ : ∀ x : Pl E, SmIrr (Gw n x), (∀ x, Occurs μE V x (τ x)) ∧ τ (T.mk' v).1 = τ' := by
    refine ⟨Function.update τ₁ (T.mk' v).1 τ', fun x => ?_, Function.update_self ..⟩
    by_cases h : x = (T.mk' v).1
    · subst h; rw [Function.update_self]; exact hτ'
    · rw [Function.update_of_ne h]; exact hτ₁ x
  subst hτw
  obtain ⟨ν, hν⟩ := hGood n hn
  obtain ⟨x, cE, Z₀, hx, hcE, hZ₀, hZ0, hE⟩ := hTE F E σ hσ hp n hn m hm μE θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV
    hVθ hrank ⟨u, hu, hua⟩ mE hmE τ hτ ν hν.1.antitone
  obtain ⟨κ, hκ, hG⟩ := hGM F E σ hσ hp n hn μE μF θ hθ q w₀ hq νE νF aE aF 1 one_pos hAE hAF hpair
  set SF : Set (Pl F) := {y | y ∈ S ∨ y = q} with hSF
  set SE : Set (Pl E) := {y | y.under (𝓞 F) ∈ SF} with hSE
  obtain ⟨ι, _, V₀, τ₀, bF, Z, hι, hF⟩ := hSum F E σ n (Module.finrank F E) hn μF νF mF hmF aF q w₀ S UF ν hν.1.antitone
    (fun V₀ => ∃ Λ' t', At μF SF V₀ Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ y ∉ SE, t y = bcSat t' y) x hx
  have hvsp : v ∈ T.sp := Finset.mem_filter.2 ⟨hTS ▸ hvS, hv⟩
  obtain ⟨τv, r, hr, hiso, htr, hlev⟩ := hPull F E n v (T.mk' v) (hv _) (mF v) (mE _) (hmF v).1 (hmE _) (τ _)
  obtain ⟨hCO, hfix, hφ⟩ := hlev (T.J _) (UF v) (T.co _) (hUF v hvsp)
  have hunit : ∀ y ∈ T.sp, _ := fun y hy => hUnit E n μE V hV (T.mk' y).1 (mE _) (hmE _) (τ _) (T.J _) (hτ _) (T.co _) (by
    refine (Submodule.ne_bot_iff _).2 ⟨u, ⟨hu.1, ?_⟩, hu0⟩
    have h1 : u ∈ eigL μE (T.mk' y).1 (T.J _) (T.χ _) := (Submodule.mem_iInf _).1 hu.2 _
    rw [T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)] at h1
    have h2 := T.chr (T.mk' y).1
    rw [T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)] at h2
    rwa [(hEig E n μE _ _ _ (T.co _) h2).2.1] at h1)
  have hsu : ∀ y : Pl F, ∃ z : ℂ, y ∈ T.sp → z ≠ 0 ∧ HasTrace (mE _) (τ (T.mk' y).1).ρ
      ((T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1) z := fun y => by
    by_cases hy : y ∈ T.sp
    · obtain ⟨z, hz⟩ := (hunit y hy).2.2.2
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose su hsu using hsu
  let ψ₁ : ∀ y : Pl F, Gw n (T.mk' y).1 → ℂ := fun y => (T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1
  obtain ⟨L₁, hfit₁, -, hL₁s, hL₁n⟩ := hL ψ₁ fun y hy => ⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩
  have hL₁S : L₁.S = S := hfit₁.S_eq.trans hTS
  have hs₁ : ∀ i (y : Pl F), ∃ z : ℂ, y ∈ S → HasTrace (mF y) (τ₀ i y).ρ (L₁.f y) z := fun i y => by
    by_cases hy : y ∈ S
    · haveI := (hmF y).1
      have ht := L₁.test y (hL₁S ▸ hy)
      obtain ⟨z, hz⟩ := (hOcc F n μF (V₀ i) y (mF y) (hι i).1).2.2 _ ((hι i).2.2.2 y) (L₁.f y) ⟨ht.2.2.1, ht.2.2.2⟩
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose s₁ hs₁ using hs₁
  haveI := (hmF v).1
  obtain ⟨i, hi⟩ := hAbs F n v (mF v) (UF v) hCO ι (fun i => τ₀ i v)
    (fun i => (κ * ∏ y ∈ S, c y) * bF i * ∏ y ∈ S.erase v, s₁ i y) Z τv (cE * r * ∏ y ∈ T.sp.erase v, su y) Z₀
    (mul_ne_zero (mul_ne_zero hcE hr) (Finset.prod_ne_zero_iff.2 fun y hy => (hsu y (Finset.mem_of_mem_erase hy)).1))
    hZ₀ hZ0 (fun i => (hι i).2.2.1) (hfix (hunit v hvsp).1) (by
      intro φ s₀ sF hφt hφi hs₀ hsF
      obtain ⟨ψv, hψt, hψi, rfl⟩ := hφ φ hφt hφi
      obtain ⟨L, hfit, hLc, hLs, hLn⟩ := hL (Function.update ψ₁ v ψv) fun y hy => by
        by_cases h : y = v
        · subst h; rw [Function.update_self]; exact ⟨hψt, hψi⟩
        · rw [Function.update_of_ne h]; exact ⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩
      have hLS : L.S = S := hfit.S_eq.trans hTS
      obtain ⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩ := hG L ν hν
      have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hLS]; rfl
      have hfS : 𝔣.S = SF := Set.ext fun y => by rw [h𝔣.2.2.1, hLS]; rfl
      obtain ⟨hAt', hc1, hc2⟩ := hS' 𝔢.S fun y => by rw [h𝔢.2.2.1, hLS]
      have hoff : OffFam F n 𝔢.S 𝔣.S Λ t := by
        rw [heS, hfS]
        exact hOffA SF ((S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy)
      filter_upwards [hCI F E n _ hn hp.pos μE μF θ 𝔢 𝔣 _ hgeo Λ t hc1 hc2 hoff x hx] with j hj
      rw [hOne E n _ hn μE θ 𝔢 V Λ t hV hVθ hAt' x j,
        hE L _ hfit _ 𝔢 h𝔢 (Function.update su v (r * s₀)) (fun y hy => by
          by_cases h : y = v
          · subst h; rw [Function.update_self, Function.update_self]; exact htr _ _ hs₀
          · rw [Function.update_of_ne h, Function.update_of_ne h]; exact (hsu y hy).2) j, heS, hfS,
        hF L 𝔣 hLS (fun y hy => (hLc y hy).2) h𝔣 (fun i => Function.update (s₁ i) v (sF i)) (fun i y hy => by
          by_cases h : y = v
          · subst h
            rw [Function.update_self, hLs y hvsp, Function.update_self]; exact hsF i
          · rw [Function.update_of_ne h]
            have e : L.f y = L₁.f y := by
              by_cases hy' : GM.Split E y
              · have hys : y ∈ T.sp := Finset.mem_filter.2 ⟨hTS ▸ hy, hy'⟩
                rw [hLs y hys, hL₁s y hys, Function.update_of_ne h]
              · rw [hLn y hy hy', hL₁n y hy hy']
            rw [e]; exact hs₁ i y hy) j, hLS, Finset.prod_congr rfl fun y hy => (hLc y hy).1,
        Finset.prod_update_of_mem hvsp, Finset.mul_sum] at hj
      simp only [Finset.prod_update_of_mem hvS, Finset.sdiff_singleton_eq_erase] at hj
      calc _ = cE * (Z₀.map (· ^ j)).sum * (r * s₀ * ∏ y ∈ T.sp.erase v, su y) := by ring
        _ = _ := hj
        _ = _ := Finset.sum_congr rfl fun i _ => by ring)
  obtain ⟨Λ', t', hA, hΛ, ht⟩ := (hι i).2.1
  have hSFf : SF.Finite := (S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy
  refine ⟨V₀ i, Λ', t', (hι i).1, ⟨SF, hSFf, hA⟩, hΛ, ?_, τ₀ i v, (hι i).2.2.2 v, hiso _ hi⟩
  obtain ⟨𝔢, -, h𝔢, -⟩ := hG L₁ ν hν
  have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hL₁S]; rfl
  exact Filter.mem_of_superset (heS ▸ 𝔢.finS : SE.Finite).compl_mem_cofinite fun y hy => ht y hy

end UpperTheory.ConvolutionTheory.T
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OffStable
section
open NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.T

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem val_gal (v : HeightOneSpectrum (𝓞 F)) (σ : E ≃ₐ[F] E) (w u : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver v.asIdeal] (h : u = σ • w) (y : w.adicCompletion E) :
    Valued.v (galEquiv v σ w u h y) = Valued.v y := by
  have hK : ∀ x : E, Valued.v (galEquiv v σ w u h (algebraMap E (w.adicCompletion E) x)) =
      Valued.v (algebraMap E (w.adicCompletion E) x) := by
    intro x
    have hx := valuation_smul σ w x
    rw [← h] at hx
    rw [galEquiv_algebraMap, HeightOneSpectrum.algebraMap_adicCompletion,
      HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa using hx
  have hclosed : IsClosed {y : w.adicCompletion E | Valued.v (galEquiv v σ w u h y) = Valued.v y} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y0 hy0
    have h0 : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    have h1 : Valued.v y0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (galEquiv v σ w u h y0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_galEquiv v σ w u h).continuousAt.preimage_mem_nhds (Valued.locally_const h2)]
      with y hy hy'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hy hy' hy0 ⊢
    rwa [hy, hy']
  exact (HeightOneSpectrum.denseRange_algebraMap E w).induction_on y hclosed hK

private theorem galFin_apply (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (y : CompletionsOver E v)
    (u : PlacesOver E v) :
    galFin σ v y u = galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u) (y (σ⁻¹ • u)) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  have h1 : galFin σ v (tensorEquiv' E v t) =
      tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
    simp [galFin, galOf]
  rw [h1]
  clear h1
  induction t with
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
  | tmul x a =>
    rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
    congr 1
    · exact (galEquiv_algebraMap v σ _ _ _ x).symm
    · exact ((galEquiv v σ _ _ (eq_smul_inv_smul v σ u)).commutes a).symm

variable {w u : HeightOneSpectrum (𝓞 E)} (φ : w.adicCompletion E →+* u.adicCompletion E)

private theorem le_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y ≤ 1) : valuation (u.adicCompletion E) (φ y) ≤ 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).le_one_iff_le_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).le_one_iff_le_one.1 hy

private theorem lt_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y < 1) : valuation (u.adicCompletion E) (φ y) < 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).lt_one_iff_lt_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_one_iff_lt_one.1 hy

private theorem eq_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y = 1) : valuation (u.adicCompletion E) (φ y) = 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).eq_one_iff_eq_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hy

private theorem integral_map (n : ℕ) (hφ : ∀ y, Valued.v (φ y) = Valued.v y)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.integralGL (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.integralGL (u.adicCompletion E) n := by
  rw [GLnLocal.mem_integralGL_iff] at hg ⊢
  rw [← map_inv]
  simp only [Valuation.mem_integer_iff] at hg ⊢
  exact ⟨fun i j => le_of_val φ hφ (hg.1 i j), fun i j => le_of_val φ hφ (hg.2 i j)⟩

private theorem iwahori_map (n : ℕ) (hφ : ∀ y, Valued.v (φ y) = Valued.v y)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.iwahori (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.iwahori (u.adicCompletion E) n := by
  rw [GLnLocal.mem_iwahori_iff] at hg ⊢
  exact ⟨fun i j => le_of_val φ hφ (hg.1 i j), fun i j h => lt_of_val φ hφ (hg.2.1 i j h),
    fun i => eq_of_val φ hφ (hg.2.2 i)⟩

end

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.offStable :
    UpperTheory.ConvolutionTheory.T.OffStable := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v
  have hv : ∀ (u : PlacesOver E v) y,
      Valued.v ((galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom y) = Valued.v y :=
    fun u y => UpperTheory.ConvolutionTheory.T.val_gal v σ _ _ _ y
  have hc : ∀ (x : GL (Fin n) (CompletionsOver E v)) (u : PlacesOver E v),
      GM.cmp u (mapGL n (galFin σ v) x) =
        mapGL n (galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom (GM.cmp (σ⁻¹ • u) x) :=
    fun x u => Units.ext (Matrix.ext fun a b => UpperTheory.ConvolutionTheory.T.galFin_apply σ v _ u)
  refine ⟨fun x hx u => ?_, fun x hx u => ?_,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.integralGL (u.1.adicCompletion E) n).comap (GM.cmp u), ?_⟩,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.iwahori (u.1.adicCompletion E) n).comap (GM.cmp u),
      fun g => by simp [Subgroup.mem_iInf]⟩,
    fun w => ⟨And.intro (GLnLocal.isCompact_integralGL _ n) (GLnLocal.isOpen_integralGL _ n),
      And.intro (GLnLocal.isCompact_iwahori _ n) (GLnLocal.isOpen_iwahori _ n),
      GLnLocal.iwahori_le_integralGL _ n⟩⟩
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.integral_map _ n (hv u) (hx _)
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.iwahori_map _ n (hv u) (hx _)
  · ext g
    simp [Subgroup.mem_iInf, unitSet, GM.cmp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OneTerm
section
theorem UpperTheory.ConvolutionTheory.T.oneTerm :
    UpperTheory.ConvolutionTheory.T.OneTerm := by
  intro K _ _ _ n l _ μ _ θ 𝔰 V Λ t hV hθ hAt x j
  have hset : {V' : Submodule ℂ (UpperTheory.ConvolutionTheory.C.LL μ) | UpperTheory.ConvolutionTheory.C.IsSummand μ V' ∧
      V'.map (θ.U : UpperTheory.ConvolutionTheory.C.LL μ →ₗ[ℂ] UpperTheory.ConvolutionTheory.C.LL μ) = V' ∧
      UpperTheory.ConvolutionTheory.At μ 𝔰.S V' Λ t} = {V} := by
    ext V'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact UpperTheory.ConvolutionTheory.Dp.atInj K n μ V' V h1 hV 𝔰.S 𝔰.finS t h3.2 hAt.2
    · rintro rfl
      exact ⟨hV, hθ, hAt⟩
  unfold UpperTheory.ConvolutionTheory.Side.tr
  rw [hset, finsum_mem_singleton]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PickInf
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate

theorem UpperTheory.ConvolutionTheory.T.Port.adj_ne {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (u : H) (hu : star T u ≠ 0) : (T * star T) u ≠ 0 := by
  intro h0
  apply hu
  rw [ContinuousLinearMap.star_eq_adjoint] at h0 ⊢
  have h1 : T (ContinuousLinearMap.adjoint T u) = 0 := h0
  rw [← inner_self_eq_zero (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_left, h1, inner_zero_right]

theorem UpperTheory.ConvolutionTheory.T.Port.pickInf_of (hInf : UpperTheory.ConvolutionTheory.L1.InfSplit) (hAB : UpperTheory.ConvolutionTheory.L1.ArchBasic)
    (hBump : UpperTheory.ConvolutionTheory.L1.BumpEx) (hPosition : UpperTheory.ConvolutionTheory.L1.ArchSlotEx) (hSq : UpperTheory.ConvolutionTheory.L1.SqOp)
    (hAmp : UpperTheory.ConvolutionTheory.L1.AmpSlot) (hPair : UpperTheory.ConvolutionTheory.L1.PairPosition) : UpperTheory.ConvolutionTheory.T.PickInf := by
  set_option synthInstance.maxHeartbeats 100000 in
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ u hu
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, by have := hp.two_le; omega⟩
  obtain ⟨p⟩ := (hInf F E σ hσ m hm).1 inferInstance
  obtain ⟨D, -⟩ := (hInf F E σ hσ m hm).2 p
  obtain ⟨-, -, -, -, -, ⟨s, hsl, hs⟩, -, -⟩ := hAB F E σ m D n
  obtain ⟨νF, hνF⟩ : ∃ νF : Measure (archGroup F n), νF.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨b, hbs, hbf, hbn, hbu⟩ := hBump F n νF (LL μE)
    (((rightRegularRep (rationalGLOne (K := E) (n := n)) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0)) u hu
  obtain ⟨νE, hνE, a, aE, aF, hA⟩ := hPosition F E σ m D n νF b hbs hbf hbn
  obtain ⟨hsq, -, -, -⟩ := hSq F n νF b a aF m hA.sq hA.pow hA.norm (LL μE)
    (((rightRegularRep (rationalGLOne (K := E) (n := n)) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0))
  obtain ⟨hAE, hAF⟩ := hAmp F E σ m D n νE νF b a aE aF hA
  refine ⟨m, hm, D, s, hs, νE, hνE, νF, hνF, b, a, aE, aF, hsl, hA, hAE μE, hAF μF,
    hPair F E σ m hm D n νE νF b a aE aF hA, ?_⟩
  have key := UpperTheory.ConvolutionTheory.T.Port.adj_ne _ u hbu
  rw [← hsq] at key
  exact key

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.T.pickInf :
    UpperTheory.ConvolutionTheory.T.PickInf := UpperTheory.ConvolutionTheory.T.Port.pickInf_of infSplit archBasic bumpEx archPositionEx sqOp ampPosition pairPosition
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
section
theorem UpperTheory.ConvolutionTheory.T.places :
    UpperTheory.ConvolutionTheory.T.Places := PositivityTheory.tft.places_holds
end

