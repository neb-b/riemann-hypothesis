module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0572
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2ExteriorSquareIso
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

section Wedge

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem update_pair_vector_zero (a b x : M) : Function.update ![a, b] 0 x = ![x, b] := by
  funext i; fin_cases i <;> simp

theorem update_pair_vector_one (a b x : M) : Function.update ![a, b] 1 x = ![a, x] := by
  funext i; fin_cases i <;> simp

def ιTwo : M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun a a' b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 0 a a'
      simpa only [update_pair_vector_zero] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 0 r a
      simpa only [update_pair_vector_zero] using h)
    (fun a b b' ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_add ![a, b] 1 b b'
      simpa only [update_pair_vector_one] using h)
    (fun r a b ↦ by
      have h := (exteriorPower.ιMulti R 2 (M := M)).map_update_smul ![a, b] 1 r b
      simpa only [update_pair_vector_one] using h)

theorem ιTwo_apply (a b : M) : ιTwo a b = exteriorPower.ιMulti R 2 ![a, b] := by
  rw [ιTwo, LinearMap.mk₂_apply]

theorem ιTwo_self (a : M) : ιTwo (R := R) a a = 0 := by
  rw [ιTwo_apply]
  exact (exteriorPower.ιMulti R 2 (M := M)).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) rfl (by decide)

theorem ιTwo_swap (a b : M) : ιTwo (R := R) b a = -ιTwo a b := by
  have h := ιTwo_self (R := R) (a + b)
  simp only [map_add (f := _), LinearMap.add_apply, ιTwo_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem sum_sum_ιTwo_of_symm {n : ℕ} (x : Fin n → M) (c : Fin n → Fin n → R)
    (hc : ∀ a b, c a b = c b a) : ∑ a, ∑ b, c a b • ιTwo (R := R) (x a) (x b) = 0 := by
  rw [← Finset.sum_product' (s := Finset.univ) (t := Finset.univ)
    (f := fun a b ↦ c a b • ιTwo (R := R) (x a) (x b))]
  refine Finset.sum_involution (fun p _ ↦ p.swap) (fun p _ ↦ ?_) (fun p _ hp ↦ ?_)
    (fun p _ ↦ by simp) (fun p _ ↦ Prod.swap_swap p)
  · simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hc p.2 p.1, ιTwo_swap (x p.1), smul_neg, add_neg_cancel]
  · intro he
    apply hp
    have : p.1 = p.2 := (Prod.ext_iff.1 he).2
    simp only [this, ιTwo_self, smul_zero]

end Wedge

section Forget

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def fnZZ2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def hypercohomologyTwoToAlgebraCohomology : Hyp2 F →ₗ[R] CatCoh.H2 F :=
  Submodule.mapQ _ _ (fnZZ2 F) (by rintro _ ⟨e, rfl⟩; exact ⟨e.1, rfl⟩)

theorem hypercohomologyTwo_cup_forget_forms (a b : Hyp1 F) : hypercohomologyTwoToAlgebraCohomology F (cupHyp F a b) = cup F (toO F a) (toO F b) := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rfl

def cupProductWedge (halt : ∀ a, cupHyp F a a = 0) : Hyp1 F [⋀^Fin 2]→ₗ[R] Hyp2 F where
  toFun v := cupHyp F (v 0) (v 1)
  map_update_add' v i a b := by fin_cases i <;> simp
  map_update_smul' v i r a := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all

def cupWedge (halt : ∀ a, cupHyp F a a = 0) : ⋀[R]^2 (Hyp1 F) →ₗ[R] Hyp2 F :=
  exteriorPower.alternatingMapLinearEquiv (cupProductWedge F halt)

theorem cupWedge_ιTwo (halt : ∀ a, cupHyp F a a = 0) (a b : Hyp1 F) :
    cupWedge F halt (ιTwo a b) = cupHyp F a b := by
  rw [ιTwo_apply, cupWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem exact_clAll_toO (hc : Closed1 F = ⊤) : Function.Exact (clAll F hc) (toO F) := by
  intro y
  constructor
  · intro hy
    have h : y ∈ Fil1 F := hy
    rw [Fil1_eq_range] at h
    obtain ⟨ω, rfl⟩ := h
    exact ⟨ω.1, rfl⟩
  · rintro ⟨w, rfl⟩
    have h : clAll F hc w ∈ Fil1 F := by
      rw [Fil1_eq_range]; exact ⟨_, rfl⟩
    exact h

end Forget

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem exists_wedge_hyp_equiv : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F →
    (∀ a, cupHyp F a a = 0) → ∃ e : ⋀[R]^2 (Hyp1 F) ≃ₗ[R] Hyp2 F,
      ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b := by
  intro R _ C _ F hF h0 hc hs hw halt
  let e₀ := cupWedge F halt
  have e₀_ι : ∀ a b, e₀ (ιTwo a b) = cupHyp F a b := cupWedge_ιTwo F halt
  have hsurj : Function.Surjective e₀ := by
    intro z
    obtain ⟨n, a, b, rfl⟩ := _root_.GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp R C F hF h0 hc hs hw z
    exact ⟨∑ k, ιTwo (a k) (b k), by simp only [map_sum, e₀_ι]⟩
  have hex := exact_clAll_toO F hc
  have hinj : Function.Injective e₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    obtain ⟨ew, hew⟩ := hw

    have hcomm : ew.toLinearMap ∘ₗ exteriorPower.map 2 (toO F) = hypercohomologyTwoToAlgebraCohomology F ∘ₗ e₀ := by
      refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
      have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
      have hv' : (toO F) ∘ v = ![toO F (v 0), toO F (v 1)] := by funext i; fin_cases i <;> rfl
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, exteriorPower.map_apply_ιMulti, hv', hew]
      rw [hv, ← ιTwo_apply, e₀_ι, hypercohomologyTwo_cup_forget_forms]
      rfl
    have h1 : exteriorPower.map 2 (toO F) t = 0 := by
      apply ew.injective
      have := LinearMap.congr_fun hcomm t
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
      rw [this, ht, map_zero, map_zero]
    obtain ⟨m, a, w, rfl⟩ := GlobalTheory.T.exists_sum_ιMulti_of_exteriorSquare_map_eq_zero R (Glob1 F) (Hyp1 F) (CatCoh.H1 F) (clAll F hc) (toO F) hs hex t h1
    simp only [← ιTwo_apply] at ht ⊢
    have hsum : ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, e₀_ι] using ht
    obtain ⟨N, ⟨Φ⟩⟩ := hF
    obtain ⟨l, -, hl⟩ := _root_.GlobalTheory.AbCoh.frame_coord R C F h0 N Φ
    let x : Fin N → Hyp1 F := fun i ↦ clAll F hc (Φ.w i)
    have hcl : ∀ v : Glob1 F, clAll F hc v = ∑ i, l i v • x i := by
      intro v
      conv_lhs => rw [hl v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, x]

    let Mi : Fin N → Hyp1 F := fun i ↦ ∑ k, l i (w k) • a k
    have ht1 : ∑ k, ιTwo (R := R) (a k) (clAll F hc (w k)) = ∑ i, ιTwo (Mi i) (x i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hcl, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Mi]
      exact Finset.sum_comm
    have hM0 : ∀ i, toO F (Mi i) = 0 := by
      intro i
      have := _root_.GlobalTheory.AbCoh.sum_toO_eq_zero_of_sum_cup R C F ⟨N, ⟨Φ⟩⟩ h0 hc hs m a w hsum (l i)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [Mi, map_sum, map_smul] using this
    have hMu : ∀ i, ∃ u, clAll F hc u = Mi i := fun i ↦ (hex (Mi i)).1 (hM0 i)
    choose u hu using hMu
    rw [ht1]
    simp only [← hu]
    have hcup : ∑ i, cupHyp F (clAll F hc (u i)) (clAll F hc (Φ.w i)) = 0 := by
      rw [← ht, ht1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← hu, map_sum, e₀_ι, x]
    have hw2 := (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R C F hc hs N u Φ.w).1 hcup
    have hsym := (_root_.GlobalTheory.AbCoh.wsum_eq_zero_iff R C F ⟨N, ⟨Φ⟩⟩ h0 N u Φ.w).1 hw2
    let c : Fin N → Fin N → R := fun p q ↦ ∑ i, l p (u i) * l q (Φ.w i)
    have hc' : ∀ p q, c p q = c q p := by
      intro p q
      have := hsym (l p) (l q)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c]
      rw [this]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
    have step : ∀ i, ιTwo (R := R) (clAll F hc (u i)) (x i) =
        ∑ p, ∑ q, (l p (u i) * l q (Φ.w i)) • ιTwo (R := R) (x p) (x q) := by
      intro i
      rw [hcl (u i)]
      conv_lhs => rw [show x i = ∑ q, l q (Φ.w i) • x q from hcl (Φ.w i)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by rw [mul_comm]
    have hexp : ∑ i, ιTwo (R := R) (clAll F hc (u i)) (x i) = ∑ p, ∑ q, c p q • ιTwo (R := R) (x p) (x q) := by
      simp only [step]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      simp only [c, Finset.sum_smul]
    rw [hexp]
    exact sum_sum_ιTwo_of_symm x c hc'
  refine ⟨LinearEquiv.ofBijective e₀ ⟨hinj, hsurj⟩, fun a b ↦ ?_⟩
  have := e₀_ι a b
  rw [ιTwo_apply] at this
  exact this

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfFiniteProjectiveAlgebra
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.FinProjComplete

theorem smodEq_span_singleton_pow_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (n : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule R M)] ↔ ∃ z : M, x - y = a ^ n • z := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, hz⟩; exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩; exact ⟨z, Submodule.mem_top, hz.symm⟩

end GlobalTheory.FinProjComplete

namespace GlobalTheory.FinProjComplete

theorem isAdicComplete_of_finite_projective : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  intro p O A _ _ _ _ _ hO
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective O A
  have hfg' : ∀ x, f (g x) = x := fun x => LinearMap.congr_fun hfg x
  have key : ∀ (k : ℕ) (z : A), (p : A) ^ k • z = ((p : O) ^ k) • z := by
    intro k z
    rw [smul_eq_mul, Algebra.smul_def, map_pow, map_natCast]
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun s hs => ?_⟩ }
  · have hc : ∀ i, g x i = 0 := by
      intro i
      refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) _ (fun k => ?_)
      obtain ⟨z, hz⟩ := (smodEq_span_singleton_pow_iff _ k x 0).1 (hx k)
      rw [smodEq_span_singleton_pow_iff]
      refine ⟨g z i, ?_⟩
      have := congrArg (fun y => g y i) hz
      simpa only [sub_zero, key, map_smul, Pi.smul_apply] using this
    have h0 : g x = 0 := funext hc
    rw [← hfg' x, h0, map_zero]
  · have hL : ∀ i, ∃ L : O, ∀ k,
        g (s k) i ≡ L [SMOD ((Ideal.span {(p : O)}) ^ k • ⊤ : Submodule O O)] := by
      intro i
      refine IsPrecomplete.prec' (I := Ideal.span {(p : O)}) _ (fun {m k} hmk => ?_)
      obtain ⟨z, hz⟩ := (smodEq_span_singleton_pow_iff _ m _ _).1 (hs hmk)
      rw [smodEq_span_singleton_pow_iff]
      refine ⟨g z i, ?_⟩
      have := congrArg (fun y => g y i) hz
      simpa only [map_sub, key, map_smul, Pi.smul_apply, Pi.sub_apply] using this
    choose L hL using hL
    refine ⟨f L, fun k => ?_⟩
    have hz' : ∀ i, ∃ z : O, g (s k) i - L i = (p : O) ^ k • z :=
      fun i => (smodEq_span_singleton_pow_iff _ k _ _).1 (hL i k)
    choose z hz using hz'
    have h2 : g (s k) - L = (p : O) ^ k • z := funext fun i => by simpa using hz i
    rw [smodEq_span_singleton_pow_iff]
    refine ⟨f z, ?_⟩
    calc s k - f L = f (g (s k) - L) := by rw [map_sub, hfg']
      _ = (p : A) ^ k • f z := by rw [h2, map_smul, key]

end GlobalTheory.FinProjComplete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultiple
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.MapLaw

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem hasSubst_elim {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun i => by cases i with
    | inl i => exact hu i
    | inr i => exact hv i

theorem constantCoeff_powerSeriesEvalTwoGroups_eq_zero {c : MvPowerSeries (Fin d ⊕ Fin d) R} (hc : constantCoeff c = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : constantCoeff (at2 c u v) = 0 := by
  unfold at2
  exact constantCoeff_subst_eq_zero (hasSubst_elim hu hv)
    (fun i => by cases i with
      | inl i => exact hu i
      | inr i => exact hv i) hc

theorem mvPowerSeriesMap_evalTwoGroups (r : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map r (at2 c u v) = at2 (map r c) (fun i => map r (u i)) (fun i => map r (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_elim hu hv)]
  congr 1
  funext i
  cases i <;> rfl

theorem map_op (r : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map r (op μ u v i) = op (fun j => map r (μ j)) (fun j => map r (u j)) (fun j => map r (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups r (μ i) hu hv

theorem constantCoeff_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 :=
  constantCoeff_powerSeriesEvalTwoGroups_eq_zero (hμ i) hu hv

end GlobalTheory.MapLaw

open GlobalTheory.MapLaw in
theorem GlobalTheory.isLaw_map_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (S : Type) [CommRing S] (r : R →+* S), IsLaw (fun i => map r (μ i)) ∧ ∀ n i, constantCoeff (nmul μ n i) = 0 ∧ map r (nmul μ n i) = nmul (fun i => map r (μ i)) n i := by
  intro R _ d μ hμ S _ r
  have hX : ∀ {σ : Type} (i : σ), constantCoeff (X i : MvPowerSeries σ R) = 0 :=
    fun i => constantCoeff_X i
  have h0 : ∀ i : Fin d, constantCoeff (0 : MvPowerSeries (Fin d) R) = 0 := fun _ => map_zero _
  refine ⟨⟨fun i => ?_, ?_, fun i => ?_, ?_⟩, ?_⟩
  · rw [constantCoeff_map, hμ.const i, map_zero]
  · funext i
    have := congrArg (map r) (congrFun hμ.unit i)
    rw [map_op r μ (fun j => hX j) h0] at this
    simpa [map_X] using this
  · have := congrArg (map r) (hμ.comm i)
    unfold swap at this ⊢
    rw [mvPowerSeriesMap_evalTwoGroups r (μ i) (fun j => hX _) (fun j => hX _)] at this
    simpa [map_X] using this
  · have hx1 : ∀ j, constantCoeff (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have hx2 : ∀ j, constantCoeff (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have hx3 : ∀ j, constantCoeff (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 :=
      fun j => hX _
    have m1 : (fun j => map r (x1 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x1 := by
      funext j; simp [x1, map_X]
    have m2 : (fun j => map r (x2 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x2 := by
      funext j; simp [x2, map_X]
    have m3 : (fun j => map r (x3 j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) = x3 := by
      funext j; simp [x3, map_X]
    funext i
    have := congrArg (map r) (congrFun hμ.assoc i)
    rw [map_op r μ (constantCoeff_op hμ.const hx1 hx2) hx3,
      map_op r μ hx1 (constantCoeff_op hμ.const hx2 hx3)] at this
    have e12 : (fun j => map r (op μ x1 x2 j)) = op (fun j => map r (μ j)) x1 x2 := by
      funext j; rw [map_op r μ hx1 hx2, m1, m2]
    have e23 : (fun j => map r (op μ x2 x3 j)) = op (fun j => map r (μ j)) x2 x3 := by
      funext j; rw [map_op r μ hx2 hx3, m2, m3]
    rw [e12, e23, m1, m3] at this
    exact this
  · intro n
    induction n with
    | zero => intro i; simp [nmul]
    | succ n ih =>
      intro i
      have hc : ∀ j, constantCoeff (nmul μ n j) = 0 := fun j => (ih j).1
      have e : ∀ (m : ℕ) (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S), nmul ν (m + 1) =
          op ν (nmul ν m) (fun j => X j) := by
        intro m ν
        unfold nmul
        rw [Function.iterate_succ_apply']
      have e' : nmul μ (n + 1) = op μ (nmul μ n) (fun j => X j) := by
        unfold nmul
        rw [Function.iterate_succ_apply']
      rw [e', e]
      refine ⟨constantCoeff_op hμ.const hc (fun j => hX j) i, ?_⟩
      rw [map_op r μ hc (fun j => hX j)]
      have hn : (fun j => map r (nmul μ n j)) = nmul (fun i => map r (μ i)) n := funext fun j => (ih j).2
      rw [hn]
      simp only [map_X]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionDifference
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem isIntegral_sq_mul_wp_sub_div : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x y : Fin 2 → ZMod N, x ≠ 0 → y ≠ 0 →
      IsIntegral ℤ ((N : ℂ) ^ 2 * (wp N x τ - wp N y τ) / ω ^ 2) := by
  intro N _ τ ω hj hω x y hx hy
  obtain ⟨hR, -, -, -, hz, -⟩ := _root_.GlobalTheory.WpFam.Act.rightActions N
  have hvz : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)), vact N v γ = 0 ↔ v = 0 := fun v γ => hz v _
  let ι := {p : (Fin 2 → ZMod N) × (Fin 2 → ZMod N) // p.1 ≠ 0 ∧ p.2 ≠ 0}
  let act : ι → SL(2, ℤ) → ι := fun p γ =>
    ⟨(vact N p.1.1 γ, vact N p.1.2 γ), by simp only [ne_eq, hvz]; exact p.2⟩
  have hRA : IsRAct act :=
    ⟨fun p => Subtype.ext (Prod.ext (hR.1 _) (hR.1 _)),
     fun p γ δ => Subtype.ext (Prod.ext (hR.2 _ _ _) (hR.2 _ _ _))⟩
  have h1 : IsFam act 2 (fun p => wp N p.1.1) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.1) 2 (wp N) (fun _ _ => rfl) (_root_.GlobalTheory.WpFam.isFam_wp_wpd N).1
  have h2 : IsFam act 2 (fun p => wp N p.1.2) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.2) 2 (wp N) (fun _ _ => rfl) (_root_.GlobalTheory.WpFam.isFam_wp_wpd N).1
  have hsub := ((GlobalTheory.QFam.isFam_algebra ι act).2.1 2 _ _ h1 h2).2
  have hfam : IsFam act ((2 : ℕ) : ℤ) (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    have := (GlobalTheory.QFam.isFam_algebra ι act).2.2.1 2 ((N : ℂ) ^ 2) _ hsub
    simpa using this
  let R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  have hmem : ∀ z : ℂ, z ∈ R ↔ IsIntegral ℤ z := fun z => by
    simp [R, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  have hNx : ∀ v : Fin 2 → ZMod N, N • v = 0 := fun v => by
    funext i; simp [nsmul_eq_mul, ZMod.natCast_self]
  have hQ : ∀ p : ι, QAll (· ∈ R) N (fun τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    intro p
    refine ⟨fun n => (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n), ?_, fun n => ?_⟩
    · exact (GlobalTheory.QFam.hasQ_linear N).2.2.1 _ _ _ ((GlobalTheory.QFam.hasQ_linear N).2.1 _ _ _ _ (_root_.GlobalTheory.WpFam.ExpP.main N _) (_root_.GlobalTheory.WpFam.ExpP.main N _))
    · show (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) ∈ R
      rw [hmem]
      have e : (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) =
          (N : ℂ) ^ 2 * cB N p.1.1 n - (N : ℂ) ^ 2 * cB N p.1.2 n := by
        simp only [cP, if_neg p.2.1, if_neg p.2.2]; ring
      rw [e]
      exact (_root_.GlobalTheory.WpFam.isIntegral_coefficients N N p.1.1 n (NeZero.pos N) (hNx _)).1.sub
        (_root_.GlobalTheory.WpFam.isIntegral_coefficients N N p.1.2 n (NeZero.pos N) (hNx _)).1
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hT := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act 2 N (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) R τ ω
    (NeZero.pos N) hRA.actBij hfam hQ hjR hω ⟨(x, y), hx, hy⟩
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ ((r : ℂ)) := (hmem _).1 r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).1 h⟩
  exact isIntegral_trans _ hT

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssocStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCupProduct_assoc : ∀ (q : ℕ) [NeZero q] (E : Spc) {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l), cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring) := by
  first
  | exact @GlobalTheory.EtC.CupAssoc.main
  | exact GlobalTheory.EtC.CupAssoc.main
  | (intros; apply GlobalTheory.EtC.CupAssoc.main <;> assumption)
end

