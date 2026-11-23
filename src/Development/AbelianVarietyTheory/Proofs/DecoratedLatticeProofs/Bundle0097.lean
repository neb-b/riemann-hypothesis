module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardCharacterConductorAlmostAll
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer NumberField Filter
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.Conductor

theorem exists_denominator (E : Type) [Field E] [NumberField E] :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x : E, (∀ o : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (x * o) = n) → ∃ o : 𝓞 E, (o : E) = N • x := by
  classical
  let b := NumberField.integralBasis E
  obtain ⟨N, hN, h⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image b.traceDual)
  refine ⟨N, hN, fun x hx => ?_⟩
  have hi : IsIntegral ℤ (N • x) := by
    rw [← b.traceDual.sum_repr x, Finset.smul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    obtain ⟨n, hn⟩ := hx (RingOfIntegers.basis E i)
    have e : b.traceDual.repr x i = (n : ℚ) := by
      rw [← hn, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
      simp [b]
    rw [e, Int.cast_smul_eq_zsmul, smul_comm]
    exact (h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))).zsmul n
  exact ⟨⟨_, hi⟩, rfl⟩

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem af_ext {a b : Af F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  DFunLike.ext _ _ h

theorem ev_same (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 :=
  GlobalTheory.LatVac.evalV_singleV_same F v

theorem ev_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v 1) = 0 :=
  GlobalTheory.LatVac.evalV_singleV_ne F v w h

theorem idem_mul (v : HeightOneSpectrum (𝓞 F)) (z : Af F ⊗[F] E)
    (h : ∀ w, w ≠ v → Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) z = 0) :
    (singleV F v 1 ⊗ₜ[F] (1 : E)) * z = z := by
  classical
  let b := Module.finBasis F E
  have key : ∀ (w) (z : Af F ⊗[F] E) i,
      (Algebra.TensorProduct.basis (Fv F w) b).repr (Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) z) i =
        evalV F w ((Algebra.TensorProduct.basis (Af F) b).repr z i) := by
    intro w z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  have e : (singleV F v 1 ⊗ₜ[F] (1 : E)) * z = singleV F v 1 • z := by
    rw [Algebra.smul_def]; rfl
  rw [e]
  refine (Algebra.TensorProduct.basis (Af F) b).ext_elem fun i => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [ev_same, one_mul]
  · rw [ev_ne hw, zero_mul, ← key, h w hw, map_zero, Finsupp.zero_apply]

theorem idem_mul_mem {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h : evalV F v α ∈ v.adicCompletionIntegers F) :
    singleV F v 1 * α ∈ intAf F := fun w => by
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rwa [ev_same, one_mul]
  · rw [ev_ne hw, zero_mul]; exact zero_mem _

theorem tmul_denominator {A : Type} [CommRing A] [Algebra F A] (a : A) {N : ℤ} (hN : N ≠ 0) (x : E) :
    (a ⊗ₜ[F] (1 : E)) * (1 ⊗ₜ[F] x) = (a * algebraMap F A (N : F)⁻¹) ⊗ₜ[F] (N • x) := by
  have hN' : (N : F) ≠ 0 := Int.cast_ne_zero.2 hN
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
    ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hN', one_smul]

theorem trace_map {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (f : A →ₐ[F] B) (z : A ⊗[F] E) :
    Algebra.trace B (B ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) z) = f (Algebra.trace A (A ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, GlobalTheory.LatVac.trace_tmul, GlobalTheory.LatVac.trace_tmul, map_mul, AlgHom.commutes]; rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end General

variable {D : D7}

theorem trace_parts (s : AE D) : Algebra.trace (AF D.host.F) (AE D) s =
    pairA D.host.F (Algebra.trace (Ainf D.host.F) _ (infPart D s)) (Algebra.trace (Af D.host.F) _ (finPart D s)) :=
  Prod.ext (trace_map (fstA D.host.F) s).symm (trace_map (sndA D.host.F) s).symm

def chi (ψ : AddChar (AF D.host.F) ℂ) (z : Af D.host.F ⊗[D.host.F] D.host.E) : ℂ :=
  ψ (pairA D.host.F 0 (Algebra.trace (Af D.host.F) _ z))

theorem chi_add (ψ : AddChar (AF D.host.F) ℂ) (x y : Af D.host.F ⊗[D.host.F] D.host.E) :
    chi ψ (x + y) = chi ψ x * chi ψ y := by
  rw [chi, map_add (f := _), GlobalTheory.LatVac.pair_add, ψ.map_add_eq_mul]; rfl

theorem chi_zero (ψ : AddChar (AF D.host.F) ℂ) : chi ψ 0 = 1 := by
  rw [chi, map_zero]; exact ψ.map_zero_eq_one

theorem psiE_eq_chi (ψ : AddChar (AF D.host.F) ℂ) {s : AE D} (h : infPart D s = 0) : psiE ψ s = chi ψ (finPart D s) := by
  rw [psiE, trace_parts, h, map_zero]; rfl

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : D.host.E) :
    chi ψ (1 ⊗ₜ[D.host.F] x) = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ D.host.E x = n := by
  rw [chi, GlobalTheory.LatVac.trace_tmul, one_mul, GlobalTheory.LatVac.char_rat hψ]

theorem chi_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ intAE D) : chi ψ z = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [chi, GlobalTheory.LatVac.trace_tmul]
    refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hα
    rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
    have hi : IsIntegral ℤ ((a : D.host.F) • (o : D.host.E)) := by
      rw [Algebra.smul_def]
      exact (a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)).mul o.isIntegral_coe
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hi)
    exact ⟨n, hn.symm⟩
  | zero => exact chi_zero ψ
  | add x y _ _ hx hy => rw [chi_add, hx, hy, one_mul]
  | neg x _ hx =>
    have := chi_add ψ x (-x)
    rwa [add_neg_cancel, chi_zero, hx, one_mul, eq_comm] at this

theorem tmul_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (o : 𝓞 D.host.E) :
    α ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩

theorem mul_mem_int {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβ, o', rfl⟩ := hw
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem (GlobalTheory.LatVac.mul_mem_intAf hα hβ) (o * o')
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem approx (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ x : D.host.E, ∃ u ∈ intAE D, z = 1 ⊗ₜ[D.host.F] x + u := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, u, hu, rfl⟩ := hx
    obtain ⟨b, u', hu', rfl⟩ := hy
    exact ⟨a + b, u + u', add_mem hu hu', by rw [TensorProduct.tmul_add, add_add_add_comm]⟩
  | tmul a x =>
    obtain ⟨N, hN, h⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset D.host.E)
    have hi : IsIntegral ℤ (N.natAbs • x) := by
      have := h x (Finset.mem_singleton_self x)
      rcases Int.natAbs_eq N with e | e
      · rwa [e, natCast_zsmul] at this
      · rw [e, neg_smul, natCast_zsmul] at this
        simpa using this.neg
    obtain ⟨a0, β, hβ, hab⟩ :=
      (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F N.natAbs (Int.natAbs_pos.2 hN)).1 a
    refine ⟨a0 • x, _, tmul_mem (α := β) hβ ⟨_, hi⟩, ?_⟩
    rw [hab]
    exact GlobalTheory.LatVac.approx_tmul a0 _ β x

theorem lift_mem (v : Pl D) (o : 𝓞 D.host.E) :
    pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨⟨GlobalTheory.LatVac.infPart_pair _ _, ?_⟩, ?_⟩
  · refine (Submodule.mem_iInf _).2 fun w => ?_
    have : compAt D w.1 (pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E)) =
        evalV D.host.F w.1 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (o : D.host.E) := rfl
    rw [RingHom.mem_ker, this, ev_ne w.2, TensorProduct.zero_tmul]
  · rw [GlobalTheory.LatVac.finPart_pair]
    have := idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
    rw [mul_one] at this
    exact tmul_mem this o

theorem eventually_conductor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ᶠ v : Pl D in cofinite, ∀ s ∈ idAt D (· = v),
      (∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = v) := by
  intro D ψ hψ
  obtain ⟨N, hN, hden⟩ := exists_denominator D.host.E
  have hev : ∀ᶠ v : Pl D in cofinite,
      evalV D.host.F v (algebraMap D.host.F (Af D.host.F) (N : D.host.F)⁻¹) ∈ v.adicCompletionIntegers D.host.F :=
    (algebraMap D.host.F (Af D.host.F) (N : D.host.F)⁻¹).2
  filter_upwards [hev] with v hv s hs
  have hinf : ∀ o, infPart D (s * o) = 0 := fun o => by
    have : infPart D s = 0 := hs.1
    rw [RingHom.map_mul, this, zero_mul]
  refine ⟨fun h => ⟨hs, ?_⟩, fun h o ho => ?_⟩
  · have hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D s = finPart D s :=
      idem_mul v _ fun w hw => (Submodule.mem_iInf _).1 hs.2 ⟨w, hw⟩
    obtain ⟨x, u, hu, e⟩ := approx (finPart D s)
    have hε : singleV D.host.F v 1 ∈ intAf D.host.F := by
      have := idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
      rwa [mul_one] at this
    obtain ⟨y, hy⟩ := hden x fun o => by
      have h1 := h _ (lift_mem v o)
      have e1 : singleV D.host.F v 1 ⊗ₜ[D.host.F] (o : D.host.E) =
          (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (o : D.host.E)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [psiE_eq_chi ψ (hinf _), RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, e1, ← mul_assoc, mul_comm (finPart D s), hz, e,
        add_mul, chi_add, chi_int hψ (mul_mem_int hu (tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
      exact (chi_rat hψ _).1 h1
    rw [← hz, e, mul_add]
    refine add_mem ?_ (mul_mem_int (tmul_mem hε 1) hu)
    rw [tmul_denominator _ hN, ← hy]
    exact tmul_mem (idem_mul_mem hv) y
  · rw [psiE_eq_chi ψ (hinf _), RingHom.map_mul]
    exact chi_int hψ (mul_mem_int h.2 ho.2)

end GlobalTheory.FinPl.Conductor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoUnitaryAdelicPointsAgreeOnGrowingFinset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AdelicLimit

section Basis

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]


set_option maxHeartbeats 800000 in
theorem repr_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra F R] [Algebra F R'] (α : R →ₐ[F] R')
    (z : R ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis R' (Module.finBasis F E)).repr (Algebra.TensorProduct.map α (AlgHom.id F E) z) k =
      α ((Algebra.TensorProduct.basis R (Module.finBasis F E)).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

end Basis

section Fin

variable {F : Type} [Field F] [NumberField F]

theorem tendsto_finAdele (f : Finset (HeightOneSpectrum (𝓞 F)) → FiniteAdeleRing (𝓞 F) F)
    (y g : FiniteAdeleRing (𝓞 F) F) (hin : ∀ T, ∀ v ∈ T, f T v = y v) (hout : ∀ T, ∀ v, v ∉ T → f T v = g v) :
    Tendsto f atTop (𝓝 y) := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | y v ∈ v.adicCompletionIntegers F ∧ g v ∈ v.adicCompletionIntegers F}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact y.2.and g.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal S)
  let f' : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T => ⟨fun v => f T v, by
    rw [Filter.eventually_principal]
    intro w hw
    show f T w ∈ (w.adicCompletionIntegers F : Set (w.adicCompletion F))
    by_cases h : w ∈ T
    · rw [hin T w h]; exact hw.1
    · rw [hout T w h]; exact hw.2⟩
  let y' : P := ⟨fun v => y v, by rw [Filter.eventually_principal]; exact fun w hw => hw.1⟩
  have hf : Tendsto f' atTop (𝓝 y') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change y v = f T v
    rw [hin T v this]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto y').comp hf

end Fin

section Entry

variable {D : D7}

set_option maxHeartbeats 800000 in
theorem repr_infPart (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr (infPart D z) k =
      fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z k) := by
  change (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z) k = _
  rw [repr_map]

set_option maxHeartbeats 800000 in
theorem repr_compAt (w : Pl D) (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr (compAt D w z) k =
      evalV D.host.F w (sndA D.host.F
        ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z k)) := by
  change (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
    (Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z)) k = _
  rw [repr_map, repr_map]


set_option maxHeartbeats 800000 in
theorem tendsto_entry (a : Finset (Pl D) → AE D) (b c : AE D) (hinf : ∀ T, infPart D (a T) = infPart D b)
    (hin : ∀ T, ∀ w ∈ T, compAt D w (a T) = compAt D w b)
    (hout : ∀ T w, w ∉ T → compAt D w (a T) = compAt D w c) : Tendsto a atTop (𝓝 b) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  set Bs := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E) with hBs
  have hc : ∀ k, Tendsto (fun T => Bs.repr (a T) k) atTop (𝓝 (Bs.repr b k)) := by
    intro k
    have h1 : ∀ T, (Bs.repr (a T) k).1 = (Bs.repr b k).1 := fun T => by
      have h := congrArg (fun z => (Algebra.TensorProduct.basis (Ainf D.host.F)
        (Module.finBasis D.host.F D.host.E)).repr z k) (hinf T)
      simp only [repr_infPart] at h
      exact h
    have h2 : Tendsto (fun T => (Bs.repr (a T) k).2) atTop (𝓝 (Bs.repr b k).2) := by
      refine tendsto_finAdele _ _ (Bs.repr c k).2 (fun T w hw => ?_) (fun T w hw => ?_)
      · have h := congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w)
          (Module.finBasis D.host.F D.host.E)).repr z k) (hin T w hw)
        simp only [repr_compAt] at h
        exact h
      · have h := congrArg (fun z => (Algebra.TensorProduct.basis (Fv D.host.F w)
          (Module.finBasis D.host.F D.host.E)).repr z k) (hout T w hw)
        simp only [repr_compAt] at h
        exact h
    have h3 := (tendsto_const_nhds (x := (Bs.repr b k).1)).prodMk_nhds h2
    refine h3.congr fun T => ?_
    exact Prod.ext (h1 T).symm rfl
  have := tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank D.host.F D.host.E)))
    (fun k _ => (hc k).smul_const (Bs k))
  simpa only [Bs.sum_repr] using this

theorem map_inv_entries {A R : Type} [CommRing A] [Ring R] {n : ℕ} (φ : A →+* R) (u v : GL (Fin n) A)
    (h : ∀ i j, φ ((u : Matrix (Fin n) (Fin n) A) i j) = φ ((v : Matrix (Fin n) (Fin n) A) i j)) :
    ∀ i j, φ (((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) =
      φ (((v⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j) := by
  have hM : φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = φ.mapMatrix (v : Matrix (Fin n) (Fin n) A) :=
    Matrix.ext fun i j => h i j
  have e1 : φ.mapMatrix ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * φ.mapMatrix (u : Matrix (Fin n) (Fin n) A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e2 : φ.mapMatrix (v : Matrix (Fin n) (Fin n) A) * φ.mapMatrix ((v⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [← hM] at e2
  have e := left_inv_eq_right_inv e1 e2
  intro i j
  exact congrArg (fun M => M i j) e

end Entry


set_option maxHeartbeats 800000 in
theorem tendsto_of_agree (D : D7) (S : HSp D) (κ : GA D S) (x : Finset (Pl D) → GA D S)
    (h1 : ∀ Fs i j, infPart D (Formalism.L2.Theta.mt S (x Fs) i j) = infPart D (Formalism.L2.Theta.mt S κ i j))
    (h2 : ∀ Fs, ∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) =
      GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j))
    (h3 : ∀ Fs w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S (x Fs) i j) =
      GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) :
    Filter.Tendsto x Filter.atTop (nhds κ) := by
  let u : Finset (Pl D) → GL (Fin S.rank) (AE D) := fun T => matHom S (x T)
  have hv : Tendsto (fun T => (u T).val) atTop
      (𝓝 (matHom S κ).val) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_entry (fun T => mt S (x T) i j) (mt S κ i j) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)
        (fun T => h1 T i j) (fun T w hw => h2 T w hw i j) (fun T w hw => h3 T w hw i j)
  have hi : Tendsto (fun T => ((u T)⁻¹).val) atTop
      (𝓝 ((matHom S κ)⁻¹).val) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine tendsto_entry _ _ ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)
      (fun T => map_inv_entries (infPart D) (u T) (matHom S κ) (h1 T) i j)
      (fun T w hw => map_inv_entries (compAt D w) (u T) (matHom S κ) (h2 T w hw) i j)
      (fun T w hw => ?_)
    have h := map_inv_entries (compAt D w) (u T) 1 (fun i j => by rw [Units.val_one]; exact h3 T w hw i j) i j
    simpa using h
  have key : Tendsto u atTop (𝓝 (matHom S κ)) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact hv.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hi)
  exact tendsto_subtype_rng.2 key

end GlobalTheory.AdelicLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.VolExist

theorem nonempty_vol {D : D7} (V : HSp D) : Nonempty (Vol V) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V
    (Measure.haar : Measure (GA D V)) inferInstance
  exact ⟨⟨Measure.haar, 𝓕, inferInstance, h𝓕⟩⟩

theorem nonempty_volN {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Nonempty (VolN d) :=
  let ⟨ν, 𝓝, h⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D S ρ d.e (isIsoSub_e d)
  ⟨⟨ν, 𝓝, h⟩⟩

theorem nonempty_volM (D : D7) (m n : ℕ) : Nonempty (VolM D m n) :=
  let ⟨μ, 𝓕, h⟩ := exists_isCovolOne D m n
  ⟨⟨μ, 𝓕, h⟩⟩

theorem nonempty_volU (D : D7) (ρ : ℕ) : Nonempty (VolU D ρ) :=
  let ⟨ν, h⟩ := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).1
  ⟨⟨ν, h⟩⟩

theorem measures_exist : ∀ D : D7, (∀ V : HSp D, Nonempty (Vol V)) ∧
    (∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), Nonempty (VolN d)) ∧ (∀ m n, Nonempty (VolM D m n)) ∧
    ∀ ρ, Nonempty (VolU D ρ) :=
  fun D => ⟨nonempty_vol, fun _ _ _ d => nonempty_volN d, nonempty_volM D, nonempty_volU D⟩

end GlobalTheory.Unf.VolExist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem jointCont_all : ∀ D : D7, JointCont D := by
  intro D ψ S T χS χT om hom f hf
  exact GlobalTheory.ThetaJointCont.continuous_om_oriented hom hf

end GlobalTheory.Unf
end

