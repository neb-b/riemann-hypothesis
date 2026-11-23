module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165

@[expose] public section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.SplitWeil
open scoped ENNReal NNReal Topology Pointwise ComplexConjugate ContDiff InnerProductSpace

noncomputable section

namespace GlobalTheory.Orb

section Conv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {f f' f'' : G → ℂ}

theorem indicator_mem_SB {X : Type*} [TopologicalSpace X] [T2Space X] {U : Set X} (ho : IsOpen U)
    (hc : IsCompact U) : U.indicator (1 : X → ℂ) ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun g => ?_, .intro hc fun x hx => indicator_of_notMem hx _⟩
  by_cases hg : g ∈ U
  · exact ⟨U, ho, hg, fun x hx => by simp [hx, hg]⟩
  · exact ⟨Uᶜ, hc.isClosed.isOpen_compl, hg, fun x hx => by rw [indicator_of_notMem hx, indicator_of_notMem hg]⟩

theorem comp_mem_SB {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) (e : X ≃ₜ Y) :
    φ ∘ e ∈ SB X := ⟨h.1.comp_continuous e.continuous, h.2.comp_homeomorph e⟩

theorem starFn_mem_SB (h : f ∈ SB G) : starFn f ∈ SB G :=
  ⟨(h.1.comp_continuous continuous_inv).comp conj, hasCompactSupport_starFn h.2⟩

theorem exists_biinvariant (h : f ∈ SB G) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g, f (k * g) = f g ∧ f (g * k) = f g := by
  refine ⟨leftStabilizer f ⊓ leftStabilizer (starFn f), (isOpen_leftStabilizer h.1 h.2).inter
    (isOpen_leftStabilizer (starFn_mem_SB h).1 (starFn_mem_SB h).2), fun k hk g => ⟨hk.1 g, ?_⟩⟩
  exact (starRingEnd ℂ).injective (by simpa [starFn] using (leftStabilizer (starFn f)).inv_mem hk.2 g⁻¹)

variable [MeasurableSpace G] {μ : Measure G}


omit [IsTopologicalGroup G] in
theorem conv_eq_zero {y : G} (h : y ∉ tsupport f * tsupport f') : conv μ f f' y = 0 := by
  have : ∀ x, f x * f' (x⁻¹ * y) = 0 := fun x => by
    by_contra hne
    exact h ⟨x, subset_tsupport f (left_ne_zero_of_mul hne), _, subset_tsupport f' (right_ne_zero_of_mul hne), by simp⟩
  simp [conv, this]

theorem hasCompactSupport_conv (hc : HasCompactSupport f) (hc' : HasCompactSupport f') :
    HasCompactSupport (conv μ f f') := .intro (IsCompact.mul hc hc') fun _ => conv_eq_zero

theorem conv_mem_SB (h : f ∈ SB G) (h' : f' ∈ SB G) : conv μ f f' ∈ SB G := by
  obtain ⟨U, hU, hf⟩ := exists_biinvariant h'
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(g⁻¹ * ·) ⁻¹' U, hU.preimage (by fun_prop), by simp,
    fun x hx => ?_⟩, hasCompactSupport_conv h.2 h'.2⟩
  refine integral_congr_ae (.of_forall fun z => ?_)
  simpa [mul_assoc] using congrArg (f z * ·) (hf _ hx (z⁻¹ * g)).2

variable [BorelSpace G]

theorem starFn_conv [μ.IsMulLeftInvariant] (f f' : G → ℂ) :
    starFn (conv μ f f') = conv μ (starFn f') (starFn f) := by
  funext y
  rw [starFn, conv, conv, ← integral_conj, ← integral_mul_left_eq_self _ y⁻¹]
  simp [starFn, mul_comm]

variable [IsFiniteMeasureOnCompacts μ]

theorem conv_assoc [μ.IsMulLeftInvariant] (hf : Continuous f) (hc : HasCompactSupport f) (hf' : Continuous f')
    (hc' : HasCompactSupport f') (hf'' : Continuous f'') :
    conv μ (conv μ f f') f'' = conv μ f (conv μ f' f'') := by
  funext z
  have hF : Continuous (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * f'' (y⁻¹ * z)) :=
    ((hf.comp continuous_fst).mul (hf'.comp (continuous_fst.inv.mul continuous_snd))).mul
      (hf''.comp (continuous_snd.inv.mul continuous_const))
  have hFc : HasCompactSupport (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * f'' (y⁻¹ * z)) := by
    refine .intro (IsCompact.prod hc (IsCompact.mul hc hc')) fun p hp => ?_
    by_contra hne
    have h0 : f p.1 * f' (p.1⁻¹ * p.2) ≠ 0 := left_ne_zero_of_mul hne
    have h1 := subset_tsupport f (left_ne_zero_of_mul h0)
    exact hp ⟨h1, _, h1, _, subset_tsupport f' (right_ne_zero_of_mul h0), by simp⟩
  simp only [conv, ← integral_mul_const, ← integral_const_mul]
  rw [← integral_integral_swap_of_hasCompactSupport hF hFc]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only
  rw [← integral_mul_left_eq_self _ x]
  simp [mul_assoc]

end Conv

section Type_

variable {G Q W : Type} [Group G] [Group Q] [AddCommGroup W] [Module ℂ W] [MeasurableSpace G] (μ : Measure G)
  {K : Subgroup G} (r : K →* Q) (τ : Representation ℂ Q W)


open Classical in
def typeIdem : G → ℂ := fun g =>
  if h : g ∈ K then (Module.finrank ℂ W : ℂ) * (μ.real K : ℂ)⁻¹ * conj (τ.character (r ⟨g, h⟩)) else 0

theorem typeIdem_coe (k : K) :
    typeIdem μ r τ k = (Module.finrank ℂ W : ℂ) * (μ.real K : ℂ)⁻¹ * conj (τ.character (r k)) := dif_pos k.2

theorem typeIdem_of_notMem {g : G} (h : g ∉ K) : typeIdem μ r τ g = 0 := dif_neg h

theorem typeIdem_mul_ker {k : K} (hk : r k = 1) (g : G) :
    typeIdem μ r τ (k * g) = typeIdem μ r τ g ∧ typeIdem μ r τ (g * k) = typeIdem μ r τ g := by
  by_cases h : g ∈ K
  · have h1 := typeIdem_coe μ r τ (k * ⟨g, h⟩)
    have h2 := typeIdem_coe μ r τ (⟨g, h⟩ * k)
    rw [map_mul, hk] at h1 h2
    rw [one_mul] at h1
    rw [mul_one] at h2
    exact ⟨h1.trans (typeIdem_coe μ r τ ⟨g, h⟩).symm, h2.trans (typeIdem_coe μ r τ ⟨g, h⟩).symm⟩
  · rw [typeIdem_of_notMem μ r τ h, typeIdem_of_notMem, typeIdem_of_notMem]
    · exact ⟨rfl, rfl⟩
    · rwa [K.mul_mem_cancel_right k.2]
    · rwa [K.mul_mem_cancel_left k.2]

theorem starFn_typeIdem [Finite Q] [FiniteDimensional ℂ W] : starFn (typeIdem μ r τ) = typeIdem μ r τ := by
  funext g
  by_cases h : g ∈ K
  · have h1 := typeIdem_coe μ r τ (⟨g, h⟩⁻¹)
    have h2 : τ.character (r ⟨g, h⟩)⁻¹ = conj (τ.character (r ⟨g, h⟩)) := by
      have := Fintype.ofFinite Q
      exact GlobalTheory.BadShare.ZCalc.character_inv (FDRep.of τ) _
    rw [map_inv, h2] at h1
    refine (congrArg conj h1).trans (Eq.trans ?_ (typeIdem_coe μ r τ ⟨g, h⟩).symm)
    simp
  · rw [starFn, typeIdem_of_notMem μ r τ h, typeIdem_of_notMem μ r τ (by simpa using h), map_zero]

theorem typeIdem_mem_SB [TopologicalSpace G] [IsTopologicalGroup G] (ho : IsOpen (K : Set G))
    (hc : IsCompact (K : Set G)) (hr : IsOpen (r.ker : Set K)) : typeIdem μ r τ ∈ SB G := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(g⁻¹ * ·) ⁻¹' ((↑) '' (r.ker : Set K)),
    (ho.isOpenMap_subtype_val _ hr).preimage (by fun_prop), ⟨1, one_mem _, by simp⟩, ?_⟩,
    .intro hc fun x => typeIdem_of_notMem μ r τ⟩
  rintro x ⟨k, hk, e⟩
  rw [← (typeIdem_mul_ker μ r τ hk g).2, e, mul_inv_cancel_left]

end Type_

section Smooth

variable {H X : Type*} [TopologicalSpace H] [NormedAddCommGroup X] [NormedSpace ℝ X]

def CcSmooth (c : H → X) : Submodule ℂ (H → ℂ) where
  carrier := {f | HasCompactSupport f ∧ ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g)}
  zero_mem' := ⟨HasCompactSupport.zero, 0, contDiff_const, fun _ => rfl⟩
  add_mem' := by
    rintro f f' ⟨h, Φ, hΦ, e⟩ ⟨h', Φ', hΦ', e'⟩
    exact ⟨h.add h', Φ + Φ', hΦ.add hΦ', fun g => by simp [e, e']⟩
  smul_mem' := by
    rintro a f ⟨h, Φ, hΦ, e⟩
    exact ⟨h.smul_left (f := fun _ => a), a • Φ, hΦ.const_smul a, fun g => by simp [e]⟩

variable {c : H → X} {f : H → ℂ}

theorem mem_ccSmooth : f ∈ CcSmooth c ↔ HasCompactSupport f ∧ ∃ Φ : X → ℂ, ContDiff ℝ ∞ Φ ∧ ∀ g, f g = Φ (c g) :=
  Iff.rfl

theorem continuous_of_mem_ccSmooth (hc : Continuous c) (h : f ∈ CcSmooth c) : Continuous f := by
  obtain ⟨-, Φ, hΦ, e⟩ := h
  exact (hΦ.continuous.comp hc).congr fun g => (e g).symm

theorem ccSmooth_le {X' : Type*} [NormedAddCommGroup X'] [NormedSpace ℝ X'] {c' : H → X'} {p : X' → X}
    (hp : ContDiff ℝ ∞ p) (e : ∀ g, c g = p (c' g)) : CcSmooth c ≤ CcSmooth c' := by
  rintro f ⟨h, Φ, hΦ, e'⟩
  exact ⟨h, Φ ∘ p, hΦ.comp hp, fun g => by simp [e, e']⟩

theorem exists_bump [LocallyCompactSpace H] [T2Space H] [FiniteDimensional ℝ X] (hc : Topology.IsInducing c) {g : H}
    {U : Set H} (hU : U ∈ 𝓝 g) : ∃ φ : H → ℝ, (fun x => (φ x : ℂ)) ∈ CcSmooth c ∧ φ g = 1 ∧ (∀ x, φ x ∈ Icc 0 1) ∧
      tsupport φ ⊆ U := by
  obtain ⟨C, hC, hCU, hCc⟩ := local_compact_nhds hU
  rw [hc.nhds_eq_comap] at hC
  obtain ⟨s, hs, hsC⟩ := hC
  obtain ⟨Φ, h1, -, h3, h4, h5⟩ := exists_contDiff_tsupport_subset (n := ⊤) hs
  have h0 : ∀ x ∉ C, Φ (c x) = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hsC (h1 h))
  exact ⟨fun x => Φ (c x), ⟨.intro hCc fun x hx => by simp [h0 x hx], fun y => Φ y,
    Complex.ofRealCLM.contDiff.comp h3, fun _ => rfl⟩, h5, fun x => h4 ⟨_, rfl⟩,
    (closure_minimal (Function.support_subset_iff'.2 h0) hCc.isClosed).trans hCU⟩

end Smooth

def IsRegSS {A n : Type*} [CommRing A] [Fintype n] [DecidableEq n] (M : Matrix n n A) : Prop := M.charpoly.Separable

section Real

variable {H n : Type} [Group H] [TopologicalSpace H] [Fintype n] [DecidableEq n]
  {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def matCoord (ι : H →* Matrix n n ℂ) (g : H) : n → n → ℂ := fun i j => ι g i j

abbrev CcMat (ι : H →* Matrix n n ℂ) : Submodule ℂ (H → ℂ) := CcSmooth (matCoord ι)

def IsBiFinite (K : Subgroup H) (f : H → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')})

def IsUnitEquiv (π : H →* (V →L[ℂ] V)) (π' : H →* (W →L[ℂ] W)) : Prop :=
  ∃ A : V ≃ₗᵢ[ℂ] W, ∀ g v, A (π g v) = π' g (A v)

variable [MeasurableSpace H]

def IsTempered (μ : Measure H) (π : H →* (V →L[ℂ] V)) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ (2 + ε)) μ

variable [CompleteSpace V] [CompleteSpace W]

def IsCharFn (ι : H →* Matrix n n ℂ) (μ : Measure H) (π : H →* (V →L[ℂ] V)) (Θ : H → ℂ) : Prop :=
  LocallyIntegrable Θ μ ∧ (∀ s, IsRegSS (ι s) → ContinuousAt Θ s) ∧
    ∀ f ∈ CcMat ι, HasTrace (repOp π μ f) (∫ g, f g * Θ g ∂μ)

structure IsPseudoCoeff (ι : H →* Matrix n n ℂ) (μ : Measure H) (D : H →* (V →L[ℂ] V)) (f : H → ℂ) : Prop where

  mem : f ∈ CcMat ι

  trace_self : HasTrace (repOp D μ f) 1

  trace_other : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    (π : H →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → IsTempered μ π → ¬ IsUnitEquiv π D →
      HasTrace (repOp π μ f) 0

  orb_noncompact : ∀ s, IsRegSS (ι s) → ¬ IsCompact (cent s : Set H) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant], HasOrbInt μ s dt f 0

  orb_compact : ∃ Θ, IsCharFn ι μ D Θ ∧ ∀ s, IsRegSS (ι s) → IsCompact (cent s : Set H) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
      HasOrbInt μ s dt f (conj (Θ s) / dt.real univ)

variable {ι : H →* Matrix n n ℂ} {μ : Measure H} {π : H →* (V →L[ℂ] V)} [BorelSpace H]



def circleMat : Circle →* Matrix (Fin 1) (Fin 1) ℂ := (Matrix.scalar (Fin 1)).toMonoidHom.comp Circle.coeHom

end Real

end GlobalTheory.Orb
