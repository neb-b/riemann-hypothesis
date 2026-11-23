module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TotPosSign

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embReal_algebraMap {w : InfinitePlace F} (hw : w.IsReal) (t : F) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (algebraMap F w.Completion t) =
      InfinitePlace.embedding_of_isReal hw t := by
  have := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv w.1).symm t)
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]
  rw [← WithAbs.equiv_symm_apply]
  simpa only [RingEquiv.apply_symm_apply] using this

theorem eta_inf_eq_one [Algebra.IsQuadraticExtension F E] {w : InfinitePlace F} (hw : w.IsReal) (t : Fˣ)
    (ht : 0 < InfinitePlace.embedding_of_isReal hw (t : F)) :
    GlobalTheory.QuadSymbol.eta F E w.Completion (GlobalTheory.QuadSymbol.infDiag F t w) = 1 := by
  rw [GlobalTheory.QuadSymbol.eta_eq_one_iff, GlobalTheory.QuadSymbol.mem_normGroup_iff]
  set g := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set a : w.Completion := algebraMap F w.Completion (t : F)
  have hga : g a = InfinitePlace.embedding_of_isReal hw (t : F) := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, embReal_algebraMap]
  refine ⟨algebraMap w.Completion (w.Completion ⊗[F] E) (g.symm (Real.sqrt (g a))), ?_⟩
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, Algebra.IsQuadraticExtension.finrank_eq_two F E,
    ← map_pow, Real.sq_sqrt (hga ▸ ht.le), RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {x : L} {y : L'} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  change (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v x) =
    (fun z : WithZero (Multiplicative ℤ) =>
      if h : z = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v y)
  rw [h]

theorem valued_eq_exp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (hx : x ≠ 0) :
    Valued.v x = WithZero.exp (-ordL x) := by
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h0, neg_neg]
  conv_lhs => rw [← WithZero.coe_unzero h0]
  rfl

theorem eta_inert [Algebra.IsQuadraticExtension F E] {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v) (x : (v.adicCompletion F)ˣ) :
    GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F) x = (-1) ^ ordL (x : v.adicCompletion F) := by
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  let χ : (v.adicCompletion F)ˣ →* ℤˣ :=
    MonoidHom.mk' (GlobalTheory.QuadSymbol.eta F E (v.adicCompletion F)) ((GlobalTheory.QuadSymbol.localCharacters F E).1 v)
  set π := atFin v (unif v)
  set k := ordL (x : v.adicCompletion F)
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := unif_spec v
  set u := x * π ^ (-k)
  have hu1 : IsUnitAt v u := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ, valued_eq_exp x.ne_zero,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [k]
  have hx : x = u * π ^ k := by simp [u]
  have e1 : χ u = 1 := GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hu1)
  have e2 : χ π = -1 := GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2
    (GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hv hu (unif_spec v))
  change χ x = _
  rw [hx, map_mul, map_zpow, e1, e2, one_mul]

end Loc

end GlobalTheory.TotPosSign

namespace GlobalTheory.TotPosSign

section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSplit_under {w : Pl E} (h : IsSplitAt w) : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  obtain ⟨u, hne, hu⟩ := h
  exact GlobalTheory.LFun.isSplit_iff.2 ⟨u, w, hne, hu, rfl⟩

theorem not_isSplit_under {w : Pl E} (h : ¬ IsSplitAt w) : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 ↥(maximalRealSubfield E))) := by
  rintro hs
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
  by_cases haw : a = w
  · subst haw
    exact h ⟨b, hab.symm, hb⟩
  · exact h ⟨a, haw, ha⟩

theorem isUnram_of_unr (hU : Unr E) (v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E))) : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
  GlobalTheory.LFun.isUnram_iff.2 fun P _ => by
    haveI := hU P
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

theorem neg_one_zpow_cast (k : ℤ) : ((((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) : ℂ) = (-1 : ℂ) ^ k := by
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp
  · rw [hk.neg_one_zpow, hk.neg_one_zpow]; simp

theorem term_eq (hU : Unr E) (w : Pl E) (t : Units ↥(maximalRealSubfield E)) :
    (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) (algebraMap ↥(maximalRealSubfield E) E t))) =
      ((GlobalTheory.QuadSymbol.eta ↥(maximalRealSubfield E) E ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))
        (GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E)))) : ℤ) : ℂ) := by
  have h2 : Module.finrank ↥(maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ↥(maximalRealSubfield E) E
  split_ifs with hs
  · rw [GlobalTheory.QuadSymbol.eta_eq_one_iff.2 (GlobalTheory.LFun.mem_normGroup_of_isSplit h2 (isSplit_under hs) _)]
    simp
  · rw [eta_inert (not_isSplit_under hs) (isUnram_of_unr hU _), neg_one_zpow_cast]
    congr 1
    refine ordL_congr ?_
    have hx : ((GlobalTheory.QuadSymbol.finDiag ↥(maximalRealSubfield E) t (w.under (𝓞 ↥(maximalRealSubfield E))) : (w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E))) =
        algebraMap ↥(maximalRealSubfield E) _ (t : ↥(maximalRealSubfield E)) := rfl
    have e := GlobalTheory.LFun.valued_complMap (F := ↥(maximalRealSubfield E)) (E := E) (w := w) rfl
      (a := algebraMap ↥(maximalRealSubfield E) ((w.under (𝓞 ↥(maximalRealSubfield E))).adicCompletion ↥(maximalRealSubfield E)) (t : ↥(maximalRealSubfield E))) (by simp)
    rw [GlobalTheory.LFun.isUnram_iff.1 (isUnram_of_unr hU _) w rfl, pow_one, GlobalTheory.LFun.complMap_algebraMap] at e
    rw [hx, e]

theorem bijOn_under {S : Set (Pl E)} (hS : IsSection S) :
    Set.BijOn (fun w : Pl E => w.under (𝓞 ↥(maximalRealSubfield E))) S Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, fun a ha b hb hab => ?_, fun v _ => ?_⟩
  · obtain ⟨u, -, hu⟩ := hS a
    exact (hu a ⟨ha, rfl⟩).trans (hu b ⟨hb, hab.symm⟩).symm
  · obtain ⟨w, hw⟩ := (GlobalTheory.QNorm.places_over ↥(maximalRealSubfield E) E).2.1 v
    obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
    exact ⟨u, hu, hu'.trans hw⟩

end CM

end GlobalTheory.TotPosSign

namespace GlobalTheory.UnitaryClasses


open GlobalTheory.TotPosSign in
theorem signProd_totPos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S →
    ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) →
    ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := by
  intro E _ _ _ hU S hS d hd hpos
  have hmem : d ∈ maximalRealSubfield E := (mem_maximalRealSubfield_iff d).2 fun φ => by
    obtain ⟨r, -, hr⟩ := hpos φ
    rw [hr, Complex.star_def, Complex.conj_ofReal]
  set t0 : ↥(maximalRealSubfield E) := ⟨d, hmem⟩
  have ht0 : algebraMap (↥(maximalRealSubfield E)) E t0 = d := rfl
  have ht0' : t0 ≠ 0 := fun h => hd (by rw [← ht0, h, map_zero])
  set t := Units.mk0 t0 ht0'
  have PF := GlobalTheory.QuadSymbol.productFormula (↥(maximalRealSubfield E)) E t
  have hinf : ∀ w : InfinitePlace ↥(maximalRealSubfield E),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E w.Completion (GlobalTheory.QuadSymbol.infDiag _ t w) = 1 := by
    intro w
    have hw : w.IsReal := IsTotallyReal.isReal w
    refine eta_inf_eq_one hw t ?_
    letI : Algebra (↥(maximalRealSubfield E)) ℂ := w.embedding.toAlgebra
    let τ : E →ₐ[↥(maximalRealSubfield E)] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    obtain ⟨r, hr, e⟩ := hpos τ.toRingHom
    have e2 : (InfinitePlace.embedding_of_isReal hw (t : ↥(maximalRealSubfield E)) : ℂ) = r := by
      rw [InfinitePlace.embedding_of_isReal_apply, ← e]
      exact (τ.commutes t0).symm
    rw [Complex.ofReal_inj] at e2
    rw [e2]; exact hr
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)),
      GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v) = 1 := by
    have h := PF.2
    unfold GlobalTheory.QuadSymbol.etaProd at h
    rwa [Finset.prod_eq_one fun w _ => hinf w, mul_one] at h
  let cz : ℤˣ →* ℂ := (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)
  have hd' : d = algebraMap (↥(maximalRealSubfield E)) E ((t : Units ↥(maximalRealSubfield E)) : ↥(maximalRealSubfield E)) := rfl
  rw [hd', finprod_mem_eq_of_bijOn _ (bijOn_under hS) (g := fun v : HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E)) => cz
      (GlobalTheory.QuadSymbol.eta (↥(maximalRealSubfield E)) E (v.adicCompletion (↥(maximalRealSubfield E)))
        (GlobalTheory.QuadSymbol.finDiag (↥(maximalRealSubfield E)) t v))) fun w _ => term_eq hU w t,
    finprod_mem_univ, ← MonoidHom.map_finprod _ (GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport PF.1), hfin, map_one]

end GlobalTheory.UnitaryClasses

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKsSubMapClsEqHomO
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

noncomputable section

namespace GlobalTheory.HTRho

theorem finrank_ksSub_map_cls_eq_homO {k O H : Type*} [Field k] [AddCommGroup H] [Module k H]
    [FiniteDimensional k H] [Ring O] (σ : O →+* Module.End k H) (G Z : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z) (hZG : Z ≤ G) :
    finrank k ((ksSub σ 0 G Z).map (cls G)) =
      finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx))
        (qAct σ G hG)) := by
  set Zc := Z.comap G.subtype
  set hom := homO (qAct (rAct σ G hG) Zc (fun a x hx => hZ a x hx)) (qAct σ G hG)
  let Ψ : hom →ₗ[k] (G →ₗ[k] H ⧸ G) := (LinearMap.lcomp k (H ⧸ G) Zc.mkQ) ∘ₗ hom.subtype
  have hΨ : ∀ S : hom, Ψ S = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) ∘ₗ Zc.mkQ := fun S => rfl
  have inj : Function.Injective Ψ := by
    intro S S' h
    rw [hΨ, hΨ] at h
    exact Subtype.ext (LinearMap.ext fun q => by
      obtain ⟨x, rfl⟩ := Zc.mkQ_surjective q
      exact LinearMap.congr_fun h x)
  have hr : LinearMap.range Ψ = (ksSub σ 0 G Z).map (cls G) := by
    apply le_antisymm
    · rintro _ ⟨S, rfl⟩
      obtain ⟨G', hG'⟩ := Submodule.exists_isCompl G
      obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective G.mkQ (Submodule.range_mkQ G)
      have hs' : ∀ q, G.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
      let T : G →ₗ[k] H ⧸ G := Ψ S
      let f : H →ₗ[k] H := s ∘ₗ T ∘ₗ Submodule.linearProjOfIsCompl G G' hG'
      have hf : ∀ x (hx : x ∈ G), G.mkQ (f x) = (S : (G ⧸ Zc) →ₗ[k] H ⧸ G) (Zc.mkQ ⟨x, hx⟩) := by
        intro x hx
        have hp : Submodule.linearProjOfIsCompl G G' hG' x = ⟨x, hx⟩ :=
          Submodule.linearProjOfIsCompl_apply_left hG' ⟨x, hx⟩
        simp only [f, LinearMap.comp_apply, hp, hs']
        rfl
      refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro a x hx
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
        change G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))
        rw [hf _ (hG a x hx), ← qAct_mk σ G hG, hf x hx]
        rw [← (mem_homO _ _ _).1 S.2 a]
        rfl
      · intro x hx
        rw [← Submodule.Quotient.mk_eq_zero]
        change G.mkQ (f x) = 0
        rw [hf x (hZG hx)]
        have : Zc.mkQ ⟨x, hZG hx⟩ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hx
        rw [this, map_zero]
      · intro x _ y _
        simp
      · apply LinearMap.ext
        rintro ⟨x, hx⟩
        exact hf x hx
    · rintro _ ⟨f, hf, rfl⟩
      have hker : Zc ≤ LinearMap.ker (cls G f) := by
        intro x hx
        rw [LinearMap.mem_ker]
        exact (Submodule.Quotient.mk_eq_zero _).2 (hf.2.1 x hx)
      let S0 := Zc.liftQ (cls G f) hker
      have hS0 : S0 ∈ hom := by
        rw [mem_homO]
        intro a q
        obtain ⟨x, rfl⟩ := Zc.mkQ_surjective q
        change S0 (Zc.mkQ (rAct σ G hG a x)) = qAct σ G hG a (S0 (Zc.mkQ x))
        simp only [S0, Submodule.liftQ_mkQ]
        change G.mkQ (f (σ a x)) = G.mkQ (σ a (f x))
        rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hf.1 a x x.2
      refine ⟨⟨S0, hS0⟩, ?_⟩
      rw [hΨ]
      exact Submodule.liftQ_mkQ _ _ _
  rw [← hr, LinearMap.finrank_range_of_inj inj]

end GlobalTheory.HTRho
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMapEqOfKerEq
section
noncomputable section

namespace GlobalTheory.UPel.Sm.KSCount

open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

section Gen

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

theorem ksDim_finrank [FiniteDimensional k H] (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H)
    (Fil Z : Submodule k H) : KSDim ρ φ Fil Z (finrank k ((ksSub ρ φ Fil Z).map (cls Fil))) := by
  set M := (ksSub ρ φ Fil Z).map (cls Fil) with hM
  let b := Module.finBasis k M
  have hb : ∀ i, ∃ f ∈ ksSub ρ φ Fil Z, cls Fil f = (b i : Fil →ₗ[k] H ⧸ Fil) := fun i => (b i).2
  choose f hf hfb using hb
  have key : ∀ (g : H →ₗ[k] H) (c : Fin (finrank k M) → k),
      (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
        cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil) := fun g c => by
    simp_rw [← hfb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  refine ⟨f, hf, fun g hg => ?_⟩
  let m : M := ⟨cls Fil g, g, hg, rfl⟩
  have hsum : ∀ c : Fin (finrank k M) → k, (cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil)) ↔
      m = ∑ i, c i • b i := fun c => by
    rw [Subtype.ext_iff]; simp [m]
  refine ⟨b.equivFun m, (key g _).2 ((hsum _).2 ?_), fun c hc => ?_⟩
  · rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · have := (hsum c).1 ((key g c).1 hc)
    rw [this, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem finrank_map_add_ker {M N : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] (p : Submodule k M) (f : M →ₗ[k] N) :
    finrank k (p.map f) + finrank k (LinearMap.ker (f ∘ₗ p.subtype)) = finrank k p := by
  rw [← LinearMap.finrank_range_add_finrank_ker (f ∘ₗ p.subtype), LinearMap.range_comp,
    Submodule.range_subtype]

end Gen

end GlobalTheory.UPel.Sm.KSCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionValuationAtFinitePlaceEqSubDet
section
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem vV_algebraMap_of_isUnit (T : CDVR) {u : T.V} (hu : IsUnit u) : vV T.V (algebraMap T.V T.Fr u) = 0 := by
  have : valV T.V (algebraMap T.V T.Fr u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal u).1 h hu
  simp [vV, this]

theorem rho_vw_eq_vAdd_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ w, s.rho_vw w = (vAdd w b : ℝ) - (vAdd w (P.B w τ.1).det : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s b hb hev w
  obtain ⟨v, hv⟩ := s.hasPts.2 w
  have hval := s.val_eq hv
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  have hval' : nval T.V e (evR Xo c s.sig y.1) = ((flDefect_vw Dw c τ w + s.rho_vw w : ℝ) : EReal) := hval
  have hδ : flDefect_vw Dw c τ w = 0 := by simp [flDefect_vw, hD.q]
  rw [hδ, zero_add] at hval'
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F T.Fr
    (Algebra.ofId c.F T.Fr) P.y₀
  obtain ⟨ha, hB, hloc⟩ := P.loc w
  have hx : y.1.x = z.x := (P.only T.Fr y.1 hy.2).trans hz.1.symm
  obtain ⟨Y, u, hY, hch⟩ := hloc T io e ho y.1 z y.2.2 hz hx
  have hdet : ∀ τ', ((P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)).det =
      io (P.B w τ').det * algebraMap T.V T.Fr (Y τ').det := fun τ' => by
    rw [Matrix.det_mul, RingHom.map_det, RingHom.map_det]; rfl
  have hYne : ∀ τ', algebraMap T.V T.Fr (Y τ').det ≠ 0 := fun τ' => ((hY τ').map _).ne_zero
  have hBne : ∀ τ', io (P.B w τ').det ≠ 0 := fun τ' => (map_ne_zero io).2 (hB τ')
  have key := hev T.Fr z y.1 (fun τ' => (P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)) _
    (fun τ' => by rw [hdet]; exact (mul_ne_zero (hBne τ') (hYne τ')).isUnit)
    (mul_ne_zero ((map_ne_zero io).2 ha) (u.isUnit.map _).ne_zero).isUnit hz hch
  rw [hdet] at key
  have key' : evR Xo c s.sig y.1 * (io (P.B w τ.1).det * algebraMap T.V T.Fr (Y τ.1).det) = io b := key
  have hbne : io b ≠ 0 := (map_ne_zero io).2 hb
  have h0 : evR Xo c s.sig y.1 ≠ 0 := left_ne_zero_of_mul (key' ▸ hbne)
  have h1 := congrArg (vV T.V) key'
  rw [vV_mul h0 (mul_ne_zero (hBne _) (hYne _)), vV_mul (hBne _) (hYne _), vV_algebraMap_of_isUnit T (hY _),
    ho.2, ho.2] at h1
  rw [nval_of_ne h0, EReal.coe_eq_coe_iff] at hval'
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  rw [← hval', div_eq_iff he]
  show _ = ((vLa w b : ℝ) - (vLa w (P.B w τ.1).det : ℝ)) * e
  linarith

end GlobalTheory.DefPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMapOfCanonicalCommutationPlacewiseSignature
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.CCRFock
open MvPolynomial

theorem atPl_linear_dep {W : Type} [Fintype W] [DecidableEq W] {Λ : W → Type} (w : W) :
    ∃ L : Module.End ℂ (MvPolynomial (Λ w) ℂ) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] v : W, MvPolynomial (Λ v) ℂ),
      ∀ A, L A = GlobalTheory.RealLift.atPl (V := fun v : W => MvPolynomial (Λ v) ℂ) w A :=
  ⟨{ toFun := fun A => GlobalTheory.RealLift.atPl (V := fun v : W => MvPolynomial (Λ v) ℂ) w A
     map_add' := fun A B => by
       unfold GlobalTheory.RealLift.atPl
       exact PiTensorProduct.map_update_add
         (fun v : W => (LinearMap.id : MvPolynomial (Λ v) ℂ →ₗ[ℂ] MvPolynomial (Λ v) ℂ)) w A B
     map_smul' := fun c A => by
       unfold GlobalTheory.RealLift.atPl
       exact PiTensorProduct.map_update_smul
         (fun v : W => (LinearMap.id : MvPolynomial (Λ v) ℂ →ₗ[ℂ] MvPolynomial (Λ v) ℂ)) w c A }, fun _ => rfl⟩

theorem fock_map_of_ccr_dep : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ}
    (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] w : W, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hcomm f₀ hf₀ hvac
  obtain ⟨m, D, hm, hdm, hD0, hH⟩ := GlobalTheory.HoweD.ccr_fock_ops_sig H hadd hsmul hcomm
  obtain ⟨θ, hθ, hθ'⟩ := GlobalTheory.CCRFock.exists_polMapD W (fun w => Ix (P w) (Q w) × Ix (R w) (S w))
  have hd0 : ∀ j, D j f₀ = 0 := fun j => hD0 j f₀ (hvac j.1 j.2.1 j.2.2)
  have hD := GlobalTheory.CCRFock.polEval_pderiv m D hm f₀ (fun i j => by convert hdm i j) hd0
  refine ⟨polEval m hm f₀ ∘ₗ θ, ?_, ?_⟩
  · exact (GlobalTheory.FockAlg.injective_of_pderiv (polEval m hm f₀) D hD (by rw [polEval_one]; exact hf₀)).comp hθ
  · intro c T
    rw [hH c, Fintype.sum_sigma]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, sumPl, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    obtain ⟨L, hL⟩ := atPl_linear_dep (W := W) (Λ := fun w => Ix (P w) (Q w) × Ix (R w) (S w)) w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [heisOp_eq_sum_mul_pderiv, ← hL, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, map_sum, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    simp only [hL]
    refine Finset.sum_congr rfl fun l _ => ?_
    obtain ⟨hX, hY⟩ := hθ' w l T
    rw [hX, hY, polEval_X, hD]

end GlobalTheory.CCRFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
section
noncomputable section

namespace GlobalTheory.LevModel

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def Moved (X₂ X : Data E r) (δ : GL (Fin r) E) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) : Prop :=
  ∀ (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ),
    mat x' ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩


open Classical in
def genScal {S : Type} [CommRing S] (t : Sˣ) : Ix Dw → Sˣ := fun i => if i = none then t else 1

def Over (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) (U : Unf Xo c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) r)
    (U₂ : Unf d.Xo₂ d.c₂ σ₂ r) (k₂ : U₂.Comp) (k : U.Comp) (δ : GL (Fin r) E) : Prop :=
  ∀ (x : Frame (U₂.X k₂).Ψ r) (hx : x ∈ (U₂.X k₂).dom) (x' : Frame (U.X k).Ψ r), Moved (U₂.X k₂) (U.X k) δ x x' →
    ∃ hx' : x' ∈ (U.X k).dom, ∃ t : ℂˣ, ((∀ τ i, ‖dmin (U₂.X k₂).Gm x τ i‖ = 1) → ‖(t : ℂ)‖ = 1) ∧
      letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
      ∃ y : FrPt Xo c (CAt σ₂),
        FrBor (S := CAt σ₂) (genScal (Dw := Dw) (S := CAt σ₂) t) (U.un k ⟨x', hx'⟩) y ∧
        FrOver d (U₂.un k₂ ⟨x, hx⟩) y

end GlobalTheory.LevModel
end
end

