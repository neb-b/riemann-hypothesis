module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodEqZeroOfVanishingOnKFiniteValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.KFinPer

open Formalism.MainNotions.S
open scoped Classical

variable {D : D7}

theorem isMultMap_bound (hP : GlobalTheory.Published.CuspRapidDecay) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M)
    (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have hPu := M.fr_unit τ
  have hG := M.fr_gram τ
  choose ℓ hℓ hℓT using fun g : GA D V => hT.cont τ v g
  have hsm : ∀ u : M.H τ, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) u → u ∈ M.sm τ := fun u hu =>
    Submodule.subset_span ((GlobalTheory.SmoothCyclic.smoothVec_transport hPu hG u).2 hu)
  obtain ⟨L, C, hL, hC⟩ := GlobalTheory.SobUnif.unif_model hσ ℓ
    (fun g => GlobalTheory.SmoothCyclic.sobCont_transport hPu hG (hℓ g))
    (fun u hu => by
      obtain ⟨B, hB⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut (Function.update v τ ⟨u, hsm u hu⟩))
        (hT.cusp (Function.update v τ ⟨u, hsm u hu⟩))
      exact ⟨B, fun g => by rw [hℓT g ⟨u, hsm u hu⟩]; exact hB g⟩)
  refine ⟨L.map fun l => l.map fun X => (M.fr τ)⁻¹ * X * M.fr τ, C, ?_, fun w g => ?_⟩
  · intro l hl Y hY
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.1 hl
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
    exact GlobalTheory.SmoothCyclic.conj_lie (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hPu)) hG
      (hL l0 hl0 X hX)
  · have hw := (GlobalTheory.SmoothCyclic.smoothVec_transport hPu hG (w : M.H τ)).1
      (GlobalTheory.HolRead.MultDer.smoothVec_of_mem M τ w.2)
    have h1 := hC g (w : M.H τ) hw
    rw [hℓT g w] at h1
    refine h1.trans_eq ?_
    congr 1
    rw [GlobalTheory.SmoothGlob.sobNorm, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun l _ => ?_)
    exact congrArg norm (GlobalTheory.SobUnif.foldr_conj_eq (M.σ τ) hPu l (w : M.H τ)).symm

theorem mult_bound (hP : GlobalTheory.Published.CuspRapidDecay) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {T : MMap M}
    (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact isMultMap_bound hP θ hθ M J χ T hT τ v
  | zero => exact ⟨[], 0, by simp, fun w g => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    obtain ⟨L₁, C₁, hL₁, hb₁⟩ := h₁
    obtain ⟨L₂, C₂, hL₂, hb₂⟩ := h₂
    refine ⟨L₁ ++ L₂, max C₁ 0 + max C₂ 0, fun l hl => ?_, fun w g => ?_⟩
    · rcases List.mem_append.1 hl with h | h
      exacts [hL₁ l h, hL₂ l h]
    · set s₁ := (L₁.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      set s₂ := (L₂.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      have hs₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      have hs₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [List.map_append, List.sum_append, MultilinearMap.add_apply, Pi.add_apply]
      calc _ ≤ ‖T₁ (Function.update v τ w) g‖ + ‖T₂ (Function.update v τ w) g‖ := norm_add_le _ _
        _ ≤ C₁ * s₁ + C₂ * s₂ := add_le_add (hb₁ w g) (hb₂ w g)
        _ ≤ max C₁ 0 * s₁ + max C₂ 0 * s₂ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₁)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₂)
        _ ≤ (max C₁ 0 + max C₂ 0) * (s₁ + s₂) := by
          have := le_max_right C₁ 0; have := le_max_right C₂ 0; nlinarith
  | smul c T _ h =>
    obtain ⟨L, C, hL, hb⟩ := h
    refine ⟨L, ‖c‖ * C, hL, fun w g => ?_⟩
    rw [MultilinearMap.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb w g) (norm_nonneg _)

theorem per_eq_zero_of_kF : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ y ∈ MultT θ M J χ, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (e : X → GA D V) (u : X → ℂ), Measurable e → Integrable u ν → (∀ a ∈ KF M, ∫ x, y a (e x) * u x ∂ν = 0) → ∀ a, ∫ x, y a (e x) * u x ∂ν = 0 := by
  intro hP hHC D θ hθ V S M J χ y hy X _ ν e u he hu h0 a
  have : BorelSpace (GA D V) := ⟨rfl⟩
  set T' : MMap M := PiTensorProduct.lift.symm y with hT'
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ y).1 hy
  have hTt : ∀ w : M.Vec, y (PiTensorProduct.tprod ℂ w) = T' w := by
    intro w
    have : y = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply y).symm
    rw [this, PiTensorProduct.lift.tprod]
  have hval : ∀ b, Continuous (y b) ∧ ∃ B : ℝ, ∀ g, ‖y b g‖ ≤ B := by
    intro b
    obtain ⟨h1, h2, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J χ y hy b
    exact ⟨h1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ h1 h2⟩
  have hint : ∀ b, Integrable (fun x => y b (e x) * u x) ν := by
    intro b
    obtain ⟨hc, B, hB⟩ := hval b
    have hm : AEStronglyMeasurable (fun x => y b (e x)) ν :=
      (hc.measurable.comp he).aestronglyMeasurable
    first
      | exact hu.bdd_mul hm ⟨B, fun x => hB (e x)⟩
      | exact hu.bdd_mul hm (Filter.Eventually.of_forall fun x => hB (e x))
  let Λ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun b => ∫ x, y b (e x) * u x ∂ν
      map_add' := fun b c => by
        simp only [map_add (f := _), Pi.add_apply, add_mul]
        exact integral_add (hint b) (hint c)
      map_smul' := fun c b => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hsep : GlobalTheory.Core.Mi.SepCont M Λ := by
    intro τ v
    obtain ⟨L, Cu, hL, hb⟩ := mult_bound hP θ hθ M J χ hT'm τ v
    let ℓ₀ : M.sm τ →ₗ[ℂ] ℂ := (Λ.compMultilinearMap (PiTensorProduct.tprod ℂ)).toLinearMap v τ
    obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
    have hℓw : ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w)) := by
      intro w
      have := congrArg (fun m => m w) hℓ
      simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
    refine ⟨ℓ, ⟨L, Cu * ∫ x, ‖u x‖ ∂ν, hL, fun w hw => ?_⟩, hℓw⟩
    have hw' : w ∈ M.sm τ := Submodule.subset_span hw
    rw [hℓw ⟨w, hw'⟩]
    change ‖∫ x, y (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩)) (e x) * u x ∂ν‖ ≤ _
    rw [hTt]
    set s := (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum
    have hpt : ∀ x, ‖T' (Function.update v τ ⟨w, hw'⟩) (e x) * u x‖ ≤ Cu * s * ‖u x‖ := by
      intro x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb ⟨w, hw'⟩ (e x)) (norm_nonneg _)
    calc _ ≤ ∫ x, Cu * s * ‖u x‖ ∂ν :=
          norm_integral_le_of_norm_le (hu.norm.const_mul _) (Filter.Eventually.of_forall hpt)
      _ = Cu * s * ∫ x, ‖u x‖ ∂ν := integral_const_mul _ _
      _ = _ := by ring
  have hΛ : Λ = 0 := GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D V S M Λ hsep fun v hv =>
    h0 _ (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  exact congrArg (fun L : SmT M →ₗ[ℂ] ℂ => L a) hΛ

end GlobalTheory.SepPer.KFinPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdemEqSingle
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceIdem

variable {D : D7}

theorem AF_ext {F : Type} [Field F] [NumberField F] {x y : AF F} (h1 : fstA F x = fstA F y)
    (h2 : sndA F x = sndA F y) : x = y := Prod.ext h1 h2

theorem fstA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : fstA F (pairA F a b) = a := rfl

theorem sndA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : sndA F (pairA F a b) = b := rfl

theorem placeIdem_eq_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε = pairA D.host.F 0 (singleV D.host.F v 1) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  change evalV D.host.F u α = evalV D.host.F u (singleV D.host.F v 1)
  by_cases huv : u = v
  · subst huv; rw [h1, (hsv u).2.1]
  · rw [h0 u huv, (hsv v).2.2 u huv]

theorem single_mul_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v w : HeightOneSpectrum (𝓞 D.host.F)} (hvw : v ≠ w) :
    pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 (singleV D.host.F w 1) = 0 := by
  refine AF_ext ?_ ?_
  · rw [map_mul, fstA_pairA, fstA_pairA, map_zero, mul_zero]
  · rw [map_mul, sndA_pairA, sndA_pairA, map_zero]
    refine Subtype.ext (funext fun u => ?_)
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F w 1) = evalV D.host.F u 0
    rw [map_mul, map_zero]
    by_cases huv : u = v
    · subst huv; rw [(hsv w).2.2 u hvw, mul_zero]
    · rw [(hsv v).2.2 u huv, zero_mul]

theorem finPart_algebraMap (x : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) x) = sndA D.host.F x ⊗ₜ[D.host.F] (1 : D.host.E) := by
  change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (algebraMap (AF D.host.F) (AE D) x) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  rfl

set_option maxHeartbeats 1000000 in
theorem exists_idem_half : ∀ (D : D7), ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧ finPart D e ∈ intAE D ∧
    finPart D (cA D e) ∈ intAE D ∧ ∃ h : AE D, finPart D h ∈ intAE D ∧ 2 * h = 1 - e - cA D e := by
  intro D
  obtain ⟨P, hP2, hsv, β, hβ, h1⟩ := GlobalTheory.LatVac.one_eq_sum_singleV_add_two_mul D.host.F
  have H : ∀ v ∈ P, ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    obtain ⟨e, ε, he, hε, hs⟩ := Formalism.IndefR.Fin.twoSplitIdem D v (hP2 v hv)
    exact ⟨e, he.1, he.2.1, by rw [hs, placeIdem_eq_single hsv hε]⟩
  choose! E hEE hEc hEs using H
  have absE : ∀ v ∈ P, E v = E v * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv; rw [← hEs v hv, mul_add, hEE v hv, hEc v hv, add_zero]
  have absC : ∀ v ∈ P, cA D (E v) = cA D (E v) * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    rw [← hEs v hv, mul_add, mul_comm (cA D (E v)) (E v), hEc v hv, ← map_mul, hEE v hv, zero_add]
  have cross : ∀ (x y : AE D) (v w : HeightOneSpectrum (𝓞 D.host.F)), v ≠ w →
      x = x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) →
      y = y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1)) → x * y = 0 := by
    intro x y v w hvw hx hy
    calc x * y = (x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))) *
          (y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1))) := by rw [← hx, ← hy]
      _ = x * y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1) *
          pairA D.host.F 0 (singleV D.host.F w 1)) := by rw [map_mul]; ring
      _ = 0 := by rw [single_mul_single hsv hvw, map_zero, mul_zero]
  have hee : (∑ v ∈ P, E v) * (∑ v ∈ P, E v) = ∑ v ∈ P, E v := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absE w hw))
      (fun h => absurd hv h), hEE v hv]
  have hec : (∑ v ∈ P, E v) * cA D (∑ v ∈ P, E v) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absC w hw))
      (fun h => absurd hv h), hEc v hv]
  have hsum : (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) =
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
    have hcs : cA D (∑ v ∈ P, E v) = ∑ v ∈ P, cA D (E v) := map_sum (cA D) E P
    calc (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) = (∑ v ∈ P, E v) + ∑ v ∈ P, cA D (E v) := congrArg (fun z => (∑ v ∈ P, E v) + z) hcs
      _ = ∑ v ∈ P, (E v + cA D (E v)) := Finset.sum_add_distrib.symm
      _ = ∑ v ∈ P, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) :=
          Finset.sum_congr rfl fun v hv => hEs v hv
      _ = algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := (map_sum _ _ _).symm
  have hi1 : finPart D (∑ v ∈ P, E v) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans (congrArg (finPart D) hee))
  have hi2 : finPart D (cA D (∑ v ∈ P, E v)) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans
      (congrArg (finPart D) ((map_mul (cA D) _ _).symm.trans (congrArg (cA D) hee))))
  refine ⟨∑ v ∈ P, E v, hee, hec, hi1, hi2, ?_⟩
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β), ?_, ?_⟩
  · rw [finPart_algebraMap, sndA_pairA]
    exact AddSubgroup.subset_closure ⟨β, hβ, 1, by simp⟩
  · have key : 2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β =
        1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1) := by
      refine AF_ext ?_ ?_
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, map_sub, map_sum, map_one, map_ofNat, fstA_pairA]
        simp only [fstA_pairA, Finset.sum_const_zero, sub_zero]
        rw [← map_ofNat (algebraMap D.host.F (Ainf D.host.F)) 2, ← map_mul]
        norm_num
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, map_sub, map_sum, map_one, map_ofNat, sndA_pairA]
        simp only [sndA_pairA]
        linear_combination -h1
    calc (2 : AE D) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β)
        = algebraMap (AF D.host.F) (AE D) (2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β) := by
          rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) 2 from (map_ofNat _ 2).symm]
          exact (map_mul _ _ _).symm
      _ = algebraMap (AF D.host.F) (AE D) (1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) :=
          congrArg _ key
      _ = 1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
          rw [map_sub, map_one]
      _ = 1 - ((∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v)) := by rw [hsum]
      _ = 1 - ∑ v ∈ P, E v - cA D (∑ v ∈ P, E v) := by rw [sub_sub]

end GlobalTheory.TwoPlaceIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalCongruenceMemLatticeCongruenceLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CongLevelInst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_hatL_iff (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) :
    x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ x ∈ Formalism.MainNotions.S.lamAf (F := F) Λ := by
  show x ∈ Submodule.span _ _ ↔ x ∈ Submodule.span _ _
  rw [Set.image_eq_range]
  rfl

theorem natCast_smul_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (g : ℕ)
    (z : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ((g : E ⊗[F] Formalism.MainNotions.S.Af F)) • z ∈ Formalism.L2.Herm.hatL (F := F) (Ideal.span {((g : ℕ) : 𝓞 E)} • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨((g : ℕ) : 𝓞 E) • l, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl, ?_⟩
    funext i
    have h1 : ((g : ℕ) : 𝓞 E) • l i = (g : E) * l i := by
      rw [Algebra.smul_def]; simp
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1, map_mul, map_natCast]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

theorem mem_congLev (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (g : ℕ)
    (k : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) (hU : k ∈ Formalism.UG.UPts hc.sig J (Formalism.MainNotions.S.Af F))
    (hs : k ∈ Formalism.UG.stabGL (Formalism.MainNotions.S.lamAf (F := F) Λ))
    (hd : ∀ y ∈ Formalism.MainNotions.S.lamAf (F := F) Λ, ∃ z ∈ Formalism.MainNotions.S.lamAf (F := F) Λ,
      ((k : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) - 1) *ᵥ y = (g : E ⊗[F] Formalism.MainNotions.S.Af F) • z) :
    k ∈ congLev hc J Λ (Ideal.span {((g : ℕ) : 𝓞 E)}) := by
  refine ⟨hU, ?_, ?_⟩
  · intro x
    rw [mem_hatL_iff, mem_hatL_iff]
    exact hs x
  · intro x hx
    obtain ⟨z, hz, e⟩ := hd x ((mem_hatL_iff Λ x).1 hx)
    have e2 : (k : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) *ᵥ x - x = (g : E ⊗[F] Formalism.MainNotions.S.Af F) • z := by
      rw [← e, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e2]
    exact natCast_smul_mem_hatL Λ g z ((mem_hatL_iff Λ z).2 hz)

end GlobalTheory.CongLevelInst

namespace GlobalTheory.CongLevelInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem kg_mem_levA : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (g : ℕ), 1 ≤ g → ∀ k ∈ (Formalism.IndefR.Eqv.UI.instV fr).Kg g, Formalism.IndefR.Eqv.UI.brg fr (1, k) ∈ Formalism.IndefR.Lev.levA V (congLev D.sp.cm V.gram fr.Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})) := by
  intro D V fr g _ k hk
  rw [Formalism.IndefR.Eqv.brg_mem_levA]
  exact ⟨rfl, mem_congLev D.sp.cm V.gram fr.Λ g k.1 k.2 hk.1 hk.2⟩

end GlobalTheory.CongLevelInst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankAlgebraicDataSchrodingerModelLeAleph0Statement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_algebraicData_schrodingerModel_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    Module.rank ℂ (M.Pol ψ emb) ≤ Cardinal.aleph0 →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), Module.rank ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ≤ Cardinal.aleph0) →
    Module.rank ℂ (GlobalTheory.SquareAgree.algD M ψ emb) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.AlgCountDim.rank_algD_le_aleph0 | exact GlobalTheory.AlgCountDim.rank_algD_le_aleph0 | (intros; apply GlobalTheory.AlgCountDim.rank_algD_le_aleph0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SBCount

theorem countable_compact_open (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    {U : Set X | IsCompact U ∧ IsOpen U}.Countable := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  refine ((Set.countable_setOf_finite_subset hbc).image Set.sUnion).mono ?_
  rintro U ⟨hUc, hUo⟩
  obtain ⟨S, hSb, rfl⟩ := hb.open_eq_sUnion hUo
  obtain ⟨t, htS, htf, hcov⟩ := hUc.elim_finite_subcover_image (b := S) (c := id)
    (fun s hs => hb.isOpen (hSb hs)) (by intro x hx; simpa using hx)
  refine ⟨t, ⟨htf, htS.trans hSb⟩, ?_⟩
  refine le_antisymm (Set.sUnion_subset_sUnion htS) ?_
  intro x hx
  simpa using hcov hx

theorem SB_le_span (X : Type) [TopologicalSpace X] :
    GlobalTheory.WeilM.SB X ≤ Submodule.span ℂ
      ((fun U : Set X => U.indicator (fun _ => (1 : ℂ))) '' {U : Set X | IsCompact U ∧ IsOpen U}) := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  obtain ⟨s, hs⟩ := hcs.isCompact.elim_finite_subcover (fun a : ℂ => f ⁻¹' {a})
    (fun a => hlc.isOpen_fiber a) (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  have hf_eq : f = ∑ a ∈ s, a • (f ⁻¹' {a}).indicator (fun _ => (1 : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator, Set.mem_preimage,
      Set.mem_singleton_iff, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_cases hx : x ∈ tsupport f
      · exact absurd (by simpa using hs hx) h
      · exact image_eq_zero_of_notMem_tsupport hx
  rw [hf_eq]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a = 0
  · simp [ha]
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨f ⁻¹' {a}, ⟨?_, hlc.isOpen_fiber a⟩, rfl⟩)
    refine hcs.isCompact.of_isClosed_subset (hlc.isClosed_fiber a) ?_
    intro x hx
    refine subset_tsupport f ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [Function.mem_support, hx, ha]

theorem rank_SB_le (X : Type) [TopologicalSpace X] [SecondCountableTopology X] :
    Module.rank ℂ (GlobalTheory.WeilM.SB X) ≤ Cardinal.aleph0 := by
  refine (Submodule.rank_mono (SB_le_span X)).trans ((rank_span_le _).trans ?_)
  exact Cardinal.mk_le_aleph0_iff.2 ((countable_compact_open X).image _).to_subtype

end GlobalTheory.SBCount

namespace GlobalTheory.TripleAssembly

theorem rank_SB_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : HeightOneSpectrum (𝓞 F)),
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ≤ Cardinal.aleph0 := by
  intro F _ _ κ _ v
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨_, Set.countable_range _, v.denseRange_algebraMap F⟩
  exact GlobalTheory.SBCount.rank_SB_le _

end GlobalTheory.TripleAssembly
end
end

