module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0733
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProduct
section
noncomputable section

open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  GlobalTheory.CuspRep GlobalTheory.DefiniteBC

namespace GlobalTheory.SpehRec

theorem isL_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} {π' : Representation ℂ (GL (Fin N) k) W}
    (h : IsL 𝔪 π) (e : π.Equiv π') : IsL 𝔪 π' := by
  obtain ⟨m, x, hd, hx, hc⟩ := h
  exact ⟨m, x, hd, hx, hc.of_equiv e (.refl _)⟩

section Sum

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem sumList_append (l l' : List (WD h)) : sumList (l ++ l') = (sumList l).lpSum (sumList l') := by
  induction l with
  | nil => simp [sumList, WD.lpSum_comm (WD.lpZero (h := h)), WD.lpSum_zero]
  | cons x l ih =>
    simp only [List.cons_append, sumList, List.foldr_cons] at ih ⊢
    rw [ih, WD.lpSum_assoc]

theorem sumList_flatMap {α : Type*} (L : List α) (f : α → List (WD h)) :
    sumList (L.flatMap f) = sumList (L.map fun i => sumList (f i)) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.flatMap_cons, sumList_append, ih]
    rfl

end Sum

theorem rec_spehQuot : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h),
    IsRec h rc → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (a d n : ℕ) (hd : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n),
      IsUnitarisable σ.ρ → IsGeneric σ.ρ → IsSpehQuot hd σ σ' →
      rc (cls (ParLaws.toRep σ')) =
        sumList ((List.range d).map fun k : ℕ => (rc (cls (ParLaws.toRep σ))).lpTw (((d : ℝ) - 1) / 2 - k)) := by
  intro E Ω _ _ _ _ _ A w
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h rc hrc hTZ hLM a d n hd σ σ' hu hg hq
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, hφ⟩ := hTZ.exists_prod σ.smooth σ.irred hu hg
  have hA := GlobalTheory.T.isLanglandsQuotient_of_irreducible_unitary_segment_product _ (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) a _ σ.ρ σ.irred m δ Δ s hΔ hδu hs hd0 hφ
  have hB := GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL _ hLM (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) (GlobalTheory.T.parabolicInduction_in_stages_product_of_products _) a _ σ.ρ m δ Δ s hΔ hδu hs hd0 hφ d n hd _ σ'.ρ σ'.irred hq
  have h4 := GlobalTheory.lpSum_segments_nu E Ω A w h rc hrc
  obtain ⟨a', ha', ε, -, L⟩ := hrc
  rw [L.langlands _ _ (isL_of_equiv hB (equivRep (ParLaws.toRep σ'))),
    L.langlands _ _ (isL_of_equiv hA (equivRep (ParLaws.toRep σ))), List.map_flatMap, sumList_flatMap]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact h4 _ _

end GlobalTheory.SpehRec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSubgroupOfTrivOutsideOfLocalPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TrivOutsideGen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem coe_mul_mat (x y : GAf L n) :
    ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl

theorem map_inv_mul_map (x : GAf L n) (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1 := by
  rw [← Matrix.map_mul, ← coe_mul_mat, inv_mul_cancel]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem map_inv_eq_one (x : GAf L n) (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1) :
    ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1 := by
  have := map_inv_mul_map x w
  rwa [h, mul_one] at this

theorem adele_eq_zero (z : AL L) (hz : ∀ w, compAt L w z = 0) : z = 0 := by
  have hcard : Module.finrank (maximalRealSubfield L) L = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _ hcard
  obtain ⟨A, B, hAB⟩ := GlobalTheory.tensor_exists_decomp b z
  have hw : ∀ w, A w = 0 ∧ B w = 0 := by
    intro w
    have h := hz w
    rw [hAB] at h
    apply GlobalTheory.tensor_decomp_eq_zero b
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h
    exact h
  have hA : A = 0 := DFunLike.ext _ _ fun w => (hw w).1
  have hB : B = 0 := DFunLike.ext _ _ fun w => (hw w).2
  rw [hAB, hA, hB]
  simp

theorem eq_one_of_trivOutside_empty (y : GAf L n) (hy : TrivOutside (∅ : Set _) y) : y = 1 := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  rw [← sub_eq_zero]
  apply adele_eq_zero
  intro w
  have h1 := congrFun (congrFun (hy w (Set.notMem_empty w)) i) j
  simp only [Matrix.map_apply] at h1
  rw [map_sub, h1]
  simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_of_trivOutside_of_local : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (K : Subgroup (GAf L n)) (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) (y : GAf L n), TrivOutside (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) y → (∀ v ∈ T, ∃ p ∈ K, TrivOutside {v} p ∧ (p.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v)) → y ∈ K := by
  intro L _ _ _ n K T
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro y hy _
    rw [eq_one_of_trivOutside_empty y (by simpa using hy)]
    exact K.one_mem
  | insert v T hv ih =>
    intro y hy hloc
    obtain ⟨p, hpK, hpT, hpv⟩ := hloc v (Finset.mem_insert_self v T)
    have hpinv : ∀ w, w ≠ v → ((p⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1 :=
      fun w hw => map_inv_eq_one p w (hpT w (by simpa using hw))
    have key : y = p * (p⁻¹ * y) := by group
    rw [key]
    refine K.mul_mem hpK (ih _ ?_ ?_)
    · intro w hw
      rw [coe_mul_mat, Matrix.map_mul]
      by_cases hwv : w = v
      · subst hwv
        rw [← hpv, map_inv_mul_map]
      · have hwT : w ∉ ((insert v T : Finset _) : Set _) := by
          simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
          exact ⟨hwv, hw⟩
        rw [hpinv w hwv, hy w hwT, mul_one]
    · intro w hw
      obtain ⟨q, hqK, hqT, hqw⟩ := hloc w (Finset.mem_insert_of_mem hw)
      refine ⟨q, hqK, hqT, ?_⟩
      have hwv : w ≠ v := fun h => hv (h ▸ hw)
      rw [hqw, coe_mul_mat, Matrix.map_mul, hpinv w hwv, one_mul]

end GlobalTheory.TrivOutsideGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCloseToComponentLocalDegreeOne
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.NormCompat.LocalDegOne

theorem valued_algebraMap_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem mul_sub_one_le {R : Type} [CommRing R] (v : Valuation R (WithZero (Multiplicative ℤ))) (a b : R) (M : ℕ)
    (ha : v (a - 1) ≤ WithZero.exp (-(M : ℤ))) (hb : v (b - 1) ≤ WithZero.exp (-(M : ℤ))) :
    v (a * b - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  have e : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by ring
  have h1 : WithZero.exp (-(M : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  rw [e]
  refine (v.map_add _ _).trans (max_le ?_ ((v.map_add _ _).trans (max_le ha hb)))
  rw [v.map_mul]
  calc v (a - 1) * v (b - 1) ≤ WithZero.exp (-(M : ℤ)) * 1 := mul_le_mul' ha (hb.trans h1)
    _ = _ := mul_one _

theorem norm_div_close_to_one : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) → ∀ M : ℕ, ∃ M' : ℕ, ∀ (c : E) (z : E'), c ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → w'.valuation E' (z / algebraMap E E' c - 1) ≤ WithZero.exp (-(M' : ℤ)) → w.valuation E (Algebra.norm E z / c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  intro E E' _ _ _ _ _ w w' i hi hcomp M
  set σ : E' →+* w.adicCompletion E := (i.symm : w'.adicCompletion E' →+* w.adicCompletion E).comp (algebraMap E' (w'.adicCompletion E')) with hσ
  have hσE : ∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x := fun x => by
    simp only [hσ, RingHom.comp_apply, RingEquiv.coe_toRingHom, ← hcomp x, RingEquiv.symm_apply_apply]
  have hσv : ∀ x : E', Valued.v (σ x) = w'.valuation E' x := fun x => by
    rw [← _root_.GlobalTheory.CompletionIsom.valued_v_map E E' w w' i hi hcomp (σ x)]
    simp only [hσ, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact valued_algebraMap_eq w' x
  obtain ⟨M₁, hM₁⟩ := _root_.GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one E E' w w' σ hσE hσv M
  refine ⟨max (max M M₁) 1, fun c z hc hz hzw => ?_⟩
  have hle : ∀ k, k ≤ max (max M M₁) 1 → WithZero.exp (-((max (max M M₁) 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(k : ℤ)) := fun k hk => by
    rw [WithZero.exp_le_exp]; omega
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, Valuation.map_one] at hzw
    have := hzw.trans (hle 1 (le_max_right _ _))
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at this
    omega
  have hF := hM₁ z hz0 fun w'' h1 h2 => (hz w'' h1 h2).trans (hle M₁ (by omega))
  have hσz : σ z ≠ 0 := (map_ne_zero σ).2 hz0
  have hcE : algebraMap E (w.adicCompletion E) c ≠ 0 := (map_ne_zero _).2 hc
  have h2 : Valued.v (σ z / algebraMap E (w.adicCompletion E) c - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    have e : σ z / algebraMap E (w.adicCompletion E) c - 1 = σ (z / algebraMap E E' c - 1) := by
      rw [map_sub, map_div₀, hσE, map_one]
    rw [e, hσv]
    exact hzw.trans (hle M (by omega))
  rw [← valued_algebraMap_eq, map_sub, map_div₀, map_one]
  have e2 : algebraMap E (w.adicCompletion E) (Algebra.norm E z) / algebraMap E (w.adicCompletion E) c =
      (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z) * (σ z / algebraMap E (w.adicCompletion E) c) := by
    field_simp
  rw [e2]
  exact mul_sub_one_le Valued.v _ _ M hF h2

end GlobalTheory.NormCompat.LocalDegOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceInUnique
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.TowerPlace

theorem placeIn_unique : ∀ (Λ : Subring ℂ) [IsDiscreteValuationRing Λ] (l : ℕ), l.Prime → ¬ IsUnit ((l : ℕ) : Λ) → ∃ e : ℕ, ∀ (L : Type) [Field L] [NumberField L] (ι : L →+* ℂ), (∀ x, ι x ∈ Λ ∨ (ι x)⁻¹ ∈ Λ) → ∃ la : HeightOneSpectrum (𝓞 L), placesIn ι Λ = {la} ∧ (∀ x, ι x ∈ Λ ↔ la.valuation L x ≤ 1) ∧ ((l : ℕ) : 𝓞 L) ∈ la.asIdeal ∧ ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) := by
  intro Λ _ l hl hlu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Λ
  have hl0 : ((l : ℕ) : Λ) ≠ 0 := by
    intro h
    have h' : ((((l : ℕ) : Λ)) : ℂ) = 0 := by rw [h]; rfl
    push_cast at h'
    exact hl.ne_zero (by exact_mod_cast h')
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨e, fun L _ _ ι hval => ?_⟩
  let B : ValuationSubring L :=
    { toSubring := Λ.comap ι
      mem_or_inv_mem' := fun x => by
        rcases hval x with h | h
        · exact Or.inl h
        · right
          show ι x⁻¹ ∈ Λ
          rw [map_inv₀]; exact h }
  have hint : ∀ x : 𝓞 L, (ι.comp (algebraMap (𝓞 L) L)) x ∈ Λ := fun x => by
    have : IsIntegral B (algebraMap (𝓞 L) L x) := (x.isIntegral_coe).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    show ι (algebraMap (𝓞 L) L x) ∈ Λ
    rw [← hy]; exact y.2
  let g : 𝓞 L →+* Λ := (ι.comp (algebraMap (𝓞 L) L)).codRestrict Λ hint
  have hg : ∀ x : 𝓞 L, ((g x : Λ) : ℂ) = ι (algebraMap (𝓞 L) L x) := fun x => rfl
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal Λ).comap g
  have hlP : ((l : ℕ) : 𝓞 L) ∈ P := by
    show g l ∈ IsLocalRing.maximalIdeal Λ
    rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hlu
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlP
    exact hl.ne_zero (by exact_mod_cast hlP)
  let la : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, hPne⟩
  have hunit : ∀ s : 𝓞 L, s ∉ la.asIdeal → IsUnit (g s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hsup : ∀ x : L, la.valuation L x ≤ 1 → ι x ∈ Λ := by
    intro x hx
    obtain ⟨a, s, h⟩ := la.exists_primeCompl_mul_eq_of_integer (K := L) x hx
    obtain ⟨w, hw⟩ := hunit s s.2
    have h3 : (((w⁻¹ : Λˣ) : Λ) : ℂ) * ι (algebraMap (𝓞 L) L s) = 1 := by
      rw [← hg, ← hw]
      have := congrArg Subtype.val w.inv_mul
      exact this
    have hs0 : ι (algebraMap (𝓞 L) L s) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h3; exact zero_ne_one h3
    have hw' : (ι (algebraMap (𝓞 L) L s))⁻¹ ∈ Λ := by
      rw [← eq_inv_of_mul_eq_one_left h3]; exact ((w⁻¹ : Λˣ) : Λ).2
    have hx' : ι x = ι (algebraMap (𝓞 L) L a) * (ι (algebraMap (𝓞 L) L s))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, h]
    rw [hx']
    exact Λ.mul_mem (hint a) hw'
  have hsub : ∀ x : L, ι x ∈ Λ → la.valuation L x ≤ 1 := by
    intro x hx
    by_contra hv
    push_neg at hv
    have hx0 : x ≠ 0 := by rintro rfl; simp at hv
    have hy : la.valuation L x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hv
    obtain ⟨a, s, h⟩ := la.exists_primeCompl_mul_eq_of_integer (K := L) x⁻¹ hy.le
    have hs1 : la.valuation L (algebraMap (𝓞 L) L s) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) (v := la)).2 s.2
    have ha : a ∈ la.asIdeal := by
      refine (la.valuation_lt_one_iff_mem (K := L) a).1 ?_
      show la.valuation L (algebraMap (𝓞 L) L a) < 1
      rw [← h, map_mul, hs1, mul_one]; exact hy
    have h4 : (⟨ι x, hx⟩ : Λ) * g a = g s := Subtype.ext (show ι x * ι (algebraMap (𝓞 L) L a) = ι (algebraMap (𝓞 L) L s) by
      rw [← map_mul, ← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul])
    have hga : g a ∈ IsLocalRing.maximalIdeal Λ := ha
    have := hunit s s.2
    rw [← h4] at this
    exact ((IsLocalRing.mem_maximalIdeal _).1 (Ideal.mul_mem_left _ _ hga)) this
  refine ⟨la, ?_, fun x => ⟨hsub x, hsup x⟩, hlP, ?_⟩
  · ext la'
    constructor
    · intro h'
      rw [Set.mem_singleton_iff]
      have hle : la.asIdeal ≤ la'.asIdeal := by
        intro r hr
        by_contra hr'
        have h1 : la'.valuation L (algebraMap (𝓞 L) L r) = 1 :=
          (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) (v := la')).2 hr'
        have h2 : la'.valuation L (algebraMap (𝓞 L) L r)⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
        have h3 := hsub _ (h' _ h2)
        have h5 : la.valuation L (algebraMap (𝓞 L) L r) < 1 := (la.valuation_lt_one_iff_mem (K := L) r).2 hr
        have hr0' : r ≠ 0 := by rintro rfl; exact hr' la'.asIdeal.zero_mem
        have hr0 : la.valuation L (algebraMap (𝓞 L) L r) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 hr0')
        rw [map_inv₀] at h3
        have := one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 hr0, h5⟩
        exact absurd h3 (not_le.2 this)
      have hEq : la.asIdeal = la'.asIdeal := la.isMaximal.eq_of_le la'.isPrime.ne_top hle
      exact HeightOneSpectrum.ext hEq.symm
    · intro h
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hsup
  · intro hmem
    have hmap : Ideal.map g (la.asIdeal ^ (e + 1)) ≤ (IsLocalRing.maximalIdeal Λ) ^ (e + 1) := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono Ideal.map_comap_le (e + 1)
    have h5 := hmap (Ideal.mem_map_of_mem g hmem)
    rw [map_natCast, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, hu] at h5
    obtain ⟨c, hc⟩ := h5
    have hpe : ϖ ^ e ≠ 0 := pow_ne_zero _ hϖ.ne_zero
    have hu' : (u : Λ) = ϖ * c := by
      apply mul_right_cancel₀ hpe
      rw [hc]; ring
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (hu' ▸ u.isUnit))

end GlobalTheory.TowerPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeDifferentOrderBoundedAbsoluteRamificatio
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.TowerDifferent

theorem not_pow_dvd_differentIdeal_int : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsPrime], la ≠ ⊥ → ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ¬ la ^ (e * e + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  intro L _ _ l e hl la _ hla h1 h2 hD
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : la.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hla
  obtain ⟨e', J, he0, hee, hcop, hfac⟩ := _root_.GlobalTheory.maxIdeal_exact_pow_dvd_span_prime L l e hl la h1 h2
  obtain ⟨hchar, hfin, ϖ, hϖ, hlϖ, hcard⟩ := _root_.GlobalTheory.quot_pow_maximal_charP_local_card L la J l e' e' hl he0 he0 hcop hfac
  letI : Algebra (ZMod (l ^ e')) (𝓞 L ⧸ la ^ (e' * e')) := ZMod.algebra _ _
  have hnd : ¬ l ^ e' ∣ e' := fun h => (Nat.lt_pow_self hl.one_lt).not_ge (Nat.le_of_dvd he0 h)
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.LocalTraceNonzero.exists_trace_ne_zero l e' e' (𝓞 L ⧸ la ^ (e' * e')) ϖ he0 hϖ hlϖ hcard hnd
  obtain ⟨c0, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hIQ : la ^ (e' * e') ⊔ J ^ e' = ⊤ := by
    have h' : IsCoprime la J := Ideal.isCoprime_iff_sup_eq.mpr hcop
    exact Ideal.isCoprime_iff_sup_eq.mp (h'.pow)
  have hmul : la ^ (e' * e') * J ^ e' = Ideal.span {((l ^ e' : ℕ) : 𝓞 L)} := by
    rw [pow_mul, ← mul_pow, ← hfac, Ideal.span_singleton_pow, Nat.cast_pow]
  obtain ⟨i, hi, q, hq, hiq⟩ : ∃ i ∈ la ^ (e' * e'), ∃ q ∈ J ^ e', i + q = 1 := by
    have : (1 : 𝓞 L) ∈ la ^ (e' * e') ⊔ J ^ e' := hIQ ▸ Submodule.mem_top
    exact Submodule.mem_sup.mp this
  have hx : q * c0 ∈ J ^ e' := Ideal.mul_mem_right _ _ hq
  have hxc : Ideal.Quotient.mk (la ^ (e' * e')) (q * c0) = Ideal.Quotient.mk (la ^ (e' * e')) c0 := by
    rw [Ideal.Quotient.eq]
    have : q * c0 - c0 = -(i * c0) := by linear_combination c0 * hiq
    rw [this]; exact neg_mem (Ideal.mul_mem_right _ _ hi)
  have htr := GlobalTheory.T.intCast_trace_eq_trace_quotient_of_mem' L l e' (la ^ (e' * e')) (J ^ e') hIQ hmul (q * c0) hx
  rw [hxc] at htr
  have hnot : Algebra.intTrace ℤ (𝓞 L) (q * c0) ∉ Ideal.span {((l ^ e' : ℕ) : ℤ)} := by
    intro hm
    rw [Algebra.intTrace_eq_trace, Ideal.mem_span_singleton] at hm
    apply hc
    rw [← htr, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hm)]
  have hmap : la ^ (e' * e') * J ^ e' = Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((l ^ e' : ℕ) : ℤ)}) := by
    rw [hmul, Ideal.map_span, Set.image_singleton, map_natCast]
  have := not_dvd_differentIdeal_of_intTrace_not_mem (A := ℤ) (la ^ (e' * e')) (J ^ e') hmap (q * c0) hx hnot
  apply this
  refine dvd_trans (pow_dvd_pow _ ?_) hD
  have := Nat.mul_le_mul hee hee
  omega

theorem differentIdeal_dvd_int (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    differentIdeal (𝓞 K) (𝓞 L) ∣ differentIdeal ℤ (𝓞 L) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 L)]
  exact dvd_mul_right _ _

theorem relDifferent_order_bounded : ∀ (l e : ℕ), l.Prime → ∃ c : ℕ, ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  intro l e hl
  refine ⟨e * e, ?_⟩
  intro K L _ _ _ _ _ p la _ h1 h2 h3
  exact not_pow_dvd_differentIdeal_int L l e hl la.asIdeal la.ne_bot h1 h2 (dvd_trans h3 (differentIdeal_dvd_int K L))

end GlobalTheory.TowerDifferent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramifiedStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalSegmentRep_length_one_unramified : LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → IsSpherical y.rep → Δ.len = 1 ∧ Δ.first.IsUnramChar := by
  first | exact @GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | exact GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | (intros; apply GlobalTheory.SphSeg.len_eq_one_and_isUnramChar <;> assumption)
end

