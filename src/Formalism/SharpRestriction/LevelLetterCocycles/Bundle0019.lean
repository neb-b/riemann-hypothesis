module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0017
public import Formalism.SharpRestriction.LevelLetterCocycles.LengthRestrictNat
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0016

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section CoreW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem cancel_unit_mul_uniformizer_pow {w : (LetA O n)ˣ} {k : ℕ} {a b : LetA O n}
    (h : (w : LetA O n) * letπ ^ k * a = (w : LetA O n) * letπ ^ k * b) : a = b := by
  unfold letπ at h
  have h' : (fun _ => PowerSeries.X) ^ k * a = (fun _ => PowerSeries.X) ^ k * b := by
    have := congrArg (fun x => (↑w⁻¹ : LetA O n) * x) h
    simpa [← mul_assoc, Units.inv_mul] using this
  funext i
  have hi := congrFun h' i
  simp only [Pi.mul_apply, Pi.pow_apply] at hi
  ext m
  have hm := congrArg (PowerSeries.coeff (m + k)) hi
  rwa [mul_comm, PowerSeries.coeff_mul_X_pow, mul_comm, PowerSeries.coeff_mul_X_pow] at hm

theorem pi0Core_of (W : LocWach PD LL O v n) (w : (LetA O n)ˣ) (k : ℕ) (h1 : W.π₀ ∈ W.AΔ)
    (h3 : W.π₀ = (w : LetA O n) * letπ ^ k) : Pi0LatticeCondition W := by
  intro g
  obtain ⟨t, ht⟩ := Formalism.MainNotions.LiftingTheory.gamma_X_eq W g
  obtain ⟨Uc, hUc⟩ : ∃ Uc : LetA O n,
      Uc = fun _ => PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t := ⟨_, rfl⟩
  have hπ : W.γA g letπ = letπ * Uc := by
    funext i
    rw [hUc]
    show W.γ₀ g PowerSeries.X = PowerSeries.X * (PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t)
    exact ht
  obtain ⟨u, hu⟩ : ∃ u : LetA O n, u = (↑w⁻¹ : LetA O n) * W.γA g (w : LetA O n) * Uc ^ k :=
    ⟨_, rfl⟩
  have heq : W.γA g W.π₀ = W.π₀ * u := by
    rw [h3, map_mul, map_pow, hπ, hu,
      show (↑w : LetA O n) * letπ ^ k * (↑w⁻¹ * W.γA g ↑w * Uc ^ k) =
        (↑w * ↑w⁻¹) * (W.γA g ↑w * (letπ * Uc) ^ k) by ring,
      Units.mul_inv, one_mul]
  refine ⟨u, ?_, heq⟩
  have hmem : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := h1
  show ∀ δ ∈ W.DelF, W.γA δ u = u
  intro δ hδ
  have e1 : W.γA δ (W.γA g W.π₀) = W.γA g W.π₀ := by
    rw [Formalism.MainNotions.LiftingTheory.gammaA_comm W δ g, hmem δ hδ]
  rw [heq, map_mul, hmem δ hδ, h3] at e1
  exact cancel_unit_mul_uniformizer_pow e1

end CoreW

theorem finrank_K0_eq_one_of_le_Kur {l : ℕ} [Fact l.Prime] {K : FinExt l} (hK : K.1 ≤ MaximalUnramifiedExtension l) :
    Module.finrank ↥(K0 K) ↥K.1 = 1 := by
  unfold K0
  rw [finrank_eq_one_iff_of_nonzero' (1 : ↥K.1) one_ne_zero]
  intro x
  refine ⟨⟨(x : Om l), IntermediateField.mem_inf.mpr ⟨x.2, hK x.2⟩⟩, ?_⟩
  first
    | exact Subtype.ext (mul_one _)
    | exact Subtype.ext (by simp)
    | rfl

theorem ring_condition_uniformizer_polynomial (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL h.2.2) 1 (((D.loc l).PD K).p - 1) ((HW l).W K 1 LL h.2.2).π₀
      (fun _ => Polynomial.X + Polynomial.C ((((D.loc l).PD K).p : ℕ) : ↥(OL LL))) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h9W := h9 l K 1 LL h.2.2
  have hp := h9W _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL h.2.2))
  refine ((hp ?_ ?_).2.2 ?_).1
  · exact (HW l).W_s K 1 LL h.2.2
  · rw [(D.loc l).PD_p K]
    exact h.2.1
  · exact finrank_K0_eq_one_of_le_Kur h.1

theorem gamma_uniformizer_divisible_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : UniformiserGammaTheorem D HW F := by
  intro h9 l _ K LL h _
  obtain ⟨h1, -, ⟨w, hw⟩, -⟩ := ring_condition_uniformizer_polynomial D HW F h9 l K LL h
  exact pi0Core_of _ w _ h1 hw

end Formalism.MainNotions.UnusedSlot80
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.BcAtDesc
section
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Asm

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem bcAt_desc (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) {ι : Type} [Fintype ι] (bO : Module.Basis ι O O')
    (bL : Module.Basis ι LL LL') (hb : ∀ i, bL i = algebraMap O' LL' (bO i))
    (hlin : ∀ φ : LL' →ₗ[LL] LL, Continuous φ) [IsLocalRing O'] (hk : lenOl PD (O := O) ≠ ⊤) :
    Formalism.MainNotions.WachCoordinates.BCAt PD (LL := LL) (O := O) (O' := O') (IsScalarTower.toAlgHom Qp LL LL') :=
  bcAt_of PD hc hO' hJ (descLift_at PD hc hO' bO bL hb hlin) (descCol_at PD hc hO' bO bL hb hlin hk)

end Asm

end Formalism.MainNotions.UnusedSlot80.BCW
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def B1 (l h η S : ℕ) : ℝ :=
  (2 * (aN l (h + η) : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) + lam l (h + η)

def B2 (l h η : ℕ) : ℝ := 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + 2

theorem bound_sum_eq (l h η S : ℕ) : B1 l h η S + B2 l h η = cocyclesToWachVectorsExponent l h η S := by
  unfold B1 B2 cocyclesToWachVectorsExponent; ring

def uOf (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N s₁ : ℕ) {FF : Type} [AddCommGroup FF]
    [Module O FF] (μ ms : ZMod n → FF →ₗ[O] W.DD T) (c : ZMod n) (f : FF) : W.DD T :=
  ((PD.p : ℕ) : O) ^ N • ms c f - ((PD.p : ℕ) : O) ^ s₁ • μ c f

def Step1Out [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d a N s₁ : ℕ) {FF : Type}
    [AddCommGroup FF] [Module O FF] (z : FF →ₗ[O] W.DD T) (μ : ZMod n → FF →ₗ[O] W.DD T)
    (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T) : Prop :=
  ∀ c ∈ evens n d, ∀ f : FF,
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (ms c f) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1
      (((PD.p : ℕ) : O) ^ s₁ • ((letE c : LetA O n) • z f) + (W.γ T (ms c f) - ms c f)) ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ a • uOf W T N s₁ μ ms c f ∈ W.N T ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (W.γ T (uOf W T N s₁ μ ms c f) - uOf W T N s₁ μ ms c f) ∧
    (f ∈ F₁ → uOf W T N s₁ μ ms c f ∈ W.N T)

def Step1 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ s₁ : ℕ, (s₁ : ℝ) ≤ B1 PD.p (hpar n b S) η S ∧
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∃ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) ⊤ F₁
          (evens n d).card 0 ∧
        (m = 0 → F₁ = ⊤) ∧
        Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms

def Step2 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ sg : ℕ, (sg : ℝ) ≤ B2 PD.p (hpar n b S) η ∧
    ∀ (s₁ : ℕ) (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∀ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
      Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms →
      ∃ (F₂ : Submodule O FF) (w : ZMod n → ↥F₂ →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) F₁ F₂
          (evens n d).card 0 ∧
        (m = 0 → F₂ = F₁) ∧
        (∀ c ∈ evens n d, ∀ f : ↥F₂, QPowSmulMemPullback W T₂ c η (w c f)) ∧
        ∀ f : ↥F₂, ∃ κ : ZMod n → G → T₂.V,
          (∀ c ∈ evens n d, RhoCoc W T₂ c (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (hpar n b S)) η
            (sigC PD.p (hpar n b S) η) (w c f) (κ c)) ∧
          (((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) - (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L ∨
            ((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) + (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L)

theorem cocyclesToWachVectorsBound_of_extTool [NeZero n] (W : LocWach PD LL O v n) (hE : Sh.ExtTool W) (h1 : Step1 W)
    (h2 : Step2 W) : CocyclesToWachVectorsBound W := by
  intro d T₁ T₂ F b S η m hS
  obtain ⟨s₁, hs₁, H1⟩ := h1 d T₁ T₂ F b S η m hS
  obtain ⟨sg, hsg, H2⟩ := h2 d T₁ T₂ F b S η m hS
  refine ⟨s₁ + sg, ?_, ?_⟩
  · have := bound_sum_eq PD.p (hpar n b S) η S
    push_cast
    linarith
  · intro FF _ _ _ _ g
    obtain ⟨N, y, z, μ, ν, hX⟩ := hE d T₁ T₂ F b S η m hS FF g
    obtain ⟨F₁, ms, hc1, hm1, ho⟩ := H1 FF g N y z μ ν hX
    obtain ⟨F₂, w, hc2, hm2, h36, hid⟩ := H2 s₁ FF g N y z μ ν hX F₁ ms ho
    refine ⟨F₂, w, ?_, ?_, h36, hid⟩
    · have hn : Even n := hS.2.2.1
      have := two_mul_card_evens_le hn d
      exact (hc1.trans hc2).mono (by omega) le_rfl
    · intro h0
      rw [hm2 h0, hm1 h0]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CompleteOfPow
section
noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.OL

open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

theorem complete_of_pow {R : Type*} [CommRing R] (J : Ideal R) {n : ℕ} (hn : 0 < n)
    (h : IsAdicComplete (J ^ n) R) : IsAdicComplete J R := by
  let : WithIdeal R := ⟨J⟩
  have hJ : IsAdic J := rfl
  have hJn : IsAdic (J ^ n) := is_ideal_adic_pow hJ hn
  rw [hJ.isAdicComplete_iff]
  exact hJn.isAdicComplete_iff.mp h

variable {l : ℕ} [Fact l.Prime]

theorem l_ne_zero (LL : FinExt l) : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
  intro h
  have h2 := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h
  simp only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

theorem l_not_unit (P : LocPrime l) (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  have h0 := Formalism.MainNotions.LiftingTheory.zl_v_unit P LL hu.unit
  have h1 := Formalism.MainNotions.LiftingTheory.zl_v_pow P LL 1
  rw [IsUnit.unit_spec, map_natCast] at h0
  rw [pow_one, h0] at h1
  exact absurd h1 (by simp)

theorem l_mem_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
  let := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 (l_not_unit P LL))

theorem OL_dvr (P : LocPrime l) (LL : FinExt l) : IsDiscreteValuationRing ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hded : IsDedekindDomain ↥(OL LL) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have hnf : ¬ IsField ↥(OL LL) := fun hf => by
    have hm := l_mem_max P LL
    rw [isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hm
    exact l_ne_zero LL hm
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 3).mpr hded

theorem OL_complete_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    IsAdicComplete (maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have := OL_dvr P LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hl0 : Ideal.span {((l : ℕ) : ↥(OL LL))} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact l_ne_zero LL
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hl0 hϖ
  have hC := Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  rw [he, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at hC
  refine complete_of_pow _ (n := e) (Nat.pos_of_ne_zero ?_) hC
  rintro rfl
  rw [pow_zero, Ideal.one_eq_top] at hC
  exact not_subsingleton _ hC.subsingleton

end Formalism.MainNotions.CrystallineLiftingInputs.OL
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusCocycleOfRhoData
section
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

def mapZ (F : LatHom T₁.L T₂.L) : ↥(W.wachCocyclesDelta T₁) →ₗ[O] ↥(W.wachCocyclesDelta T₂) :=
  (((W.map F).restrictScalars O).prodMap ((W.map F).restrictScalars O)).restrict
    (fun w hw => map_mem_Z1DΔ F ⟨w, hw⟩)

theorem mapZ_coe (F : LatHom T₁.L T₂.L) (w : ↥(W.wachCocyclesDelta T₁)) :
    (mapZ F w : W.DD T₂ × W.DD T₂) =
      (W.map F (w : W.DD T₁ × W.DD T₁).1, W.map F (w : W.DD T₁ × W.DD T₁).2) := rfl

def ZfDN (F : LatHom T₁.L T₂.L) : Submodule O (W.DD T₁ × W.DD T₁) :=
  ((latticeFiniteCohomology PD T₁.L).comap (W.clK T₁) ⊓
    LinearMap.eqLocus (F.H1map.comp (W.clK T₁)) ((W.clK T₂).comp (mapZ F))).map (W.wachCocyclesDelta T₁).subtype

def ZfN (C₁ : Coord W I T₁) (F : LatHom T₁.L T₂.L) :
    AddSubgroup ((ZMod n → C₁.V) × (ZMod n → C₁.V)) :=
  (ZfDN F).toAddSubgroup.comap (totP C₁)

theorem mem_ZfN (C₁ : Coord W I T₁) (F : LatHom T₁.L T₂.L)
    (κ : (ZMod n → C₁.V) × (ZMod n → C₁.V)) :
    κ ∈ ZfN C₁ F ↔ ∃ w : ↥(W.wachCocyclesDelta T₁), (W.clK T₁ w ∈ latticeFiniteCohomology PD T₁.L ∧
      F.H1map (W.clK T₁ w) = W.clK T₂ (mapZ F w)) ∧
      (w : W.DD T₁ × W.DD T₁) = (tot C₁ κ.1, tot C₁ κ.2) := by
  exact Iff.rfl

theorem ZfN_smul (C₁ : Coord W I T₁) (F : LatHom T₁.L T₂.L) (m : O)
    (κ : (ZMod n → C₁.V) × (ZMod n → C₁.V)) (h : κ ∈ ZfN C₁ F) :
    (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) ∈ ZfN C₁ F := by
  show totP C₁ (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) ∈ ZfDN F
  have e : totP C₁ (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) = m • totP C₁ κ := by
    show (tot C₁ (PowerSeries.C m • κ.1), tot C₁ (PowerSeries.C m • κ.2)) =
      m • (tot C₁ κ.1, tot C₁ κ.2)
    rw [tot_smulC, tot_smulC]
    rfl
  rw [e]
  exact (ZfDN F).smul_mem m h

theorem liftF_ofN {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hs : W.s = 1) (hp : PD.p ≠ 2) (herr : Formalism.MainNotions.DeltaInvariantLattices.p2aK W T₂) (e : ℕ)
    (key : ∀ κ ∈ Zf C₂, ∃ κ₁ ∈ ZfN C₁ F,
      (latOf C₂).IsCobound (I.Bs.lc ^ e • κ.1 - fun i => (latHomOf h).f (κ₁.1 i))
        (I.Bs.lc ^ e • κ.2 - fun i => (latHomOf h).f (κ₁.2 i))) :
    F.LiftF PD e := by
  intro c hc
  have hcZ : c ∈ latticeCocycles T₂.L := hc.1
  have hcls : (Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) : LatticeCohomology T₂.L) ∈ latticeFiniteCohomology PD T₂.L :=
    ⟨⟨c, hcZ⟩, hc, rfl⟩
  obtain ⟨hsurj, hker⟩ := herr hs hp
  obtain ⟨w, hw⟩ : ∃ w : ↥(W.wachCocyclesDelta T₂), W.clK T₂ w =
      Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) := hsurj _
  obtain ⟨-, hwa, hwb⟩ := (mem_Z1DΔ (w : W.DD T₂ × W.DD T₂).1 (w : W.DD T₂ × W.DD T₂).2).1 w.2
  obtain ⟨y, hy⟩ := tot_surj C₂ _ hwa
  obtain ⟨z, hz⟩ := tot_surj C₂ _ hwb
  have hκ : (y, z) ∈ Zf C₂ := (mem_Zf C₂ _).2 ⟨w, hw ▸ hcls, Prod.ext hy.symm hz.symm⟩
  obtain ⟨κ₁, hκ₁, m, hm1, hm2⟩ := key _ hκ
  obtain ⟨w₁, ⟨hw₁f, hnat⟩, hw₁⟩ := (mem_ZfN C₁ F _).1 hκ₁
  have hzero : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w - mapZ F w₁) = 0 := by
    refine (hker _).2 ⟨tot C₂ m, fun δ hδ => tot_Δ C₂ m δ hδ, ?_⟩
    have e1 := congrArg (tot C₂) hm1
    have e2 := congrArg (tot C₂) hm2
    rw [tot_sub, lc_pow, tot_smulC, tot_map, tot_dφ] at e1
    rw [tot_sub, lc_pow, tot_smulC, tot_map, tot_dγ] at e2
    have a1 : tot C₁ κ₁.1 = (w₁ : W.DD T₁ × W.DD T₁).1 := by rw [hw₁]
    have a2 : tot C₁ κ₁.2 = (w₁ : W.DD T₁ × W.DD T₁).2 := by rw [hw₁]
    rw [a1] at e1
    rw [a2] at e2
    simp only at e1 e2
    rw [hy] at e1
    rw [hz] at e2
    exact Prod.ext e1 e2
  have e3 : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w - mapZ F w₁) =
      (((PD.p : ℕ) : O) ^ e) • W.clK T₂ w - W.clK T₂ (mapZ F w₁) :=
    ((W.clK T₂).map_sub ((((PD.p : ℕ) : O) ^ e) • w) (mapZ F w₁)).trans
      (congrArg (· - W.clK T₂ (mapZ F w₁)) ((W.clK T₂).map_smul _ w))
  have hz2 : (((PD.p : ℕ) : O) ^ e) • (Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) : LatticeCohomology T₂.L) =
      F.H1map (W.clK T₁ w₁) := by
    rw [hnat, ← hw]
    exact sub_eq_zero.1 (e3.symm.trans hzero)
  obtain ⟨c₁, hc₁, hc₁e⟩ := hw₁f
  rw [← hc₁e] at hz2
  have hq : (Submodule.Quotient.mk ((((PD.p : ℕ) : O) ^ e) • (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L))) : LatticeCohomology T₂.L) =
      Submodule.Quotient.mk (⟨F.post c₁, F.post_Z1T _ c₁.2⟩ : ↥(latticeCocycles T₂.L)) := hz2
  have hB := (Submodule.Quotient.eq _).1 hq
  have hB' : (((PD.p : ℕ) : O) ^ e) • c - F.post c₁ ∈ latticeCoboundaries T₂.L := hB
  have : (((PD.p : ℕ) : O) ^ e) • c = F.post c₁ + ((((PD.p : ℕ) : O) ^ e) • c - F.post c₁) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc₁) hB'

theorem map_NΔ (F : LatHom T₁.L T₂.L) (h₁ : IsCrys PD T₁.ρ) (h₂ : IsCrys PD T₂.ρ) {x : W.DD T₁}
    (hx : x ∈ W.NΔ T₁) : W.map F x ∈ W.NΔ T₂ := by
  unfold Formalism.BasicNotions.LocWach.NΔ at hx ⊢
  obtain ⟨hN, hΔ⟩ := hx
  refine ⟨W.map_N F h₁ h₂ _ hN, fun δ hδ => ?_⟩
  rw [← W.map_γ, hΔ δ hδ]

theorem map_mulSet (F : LatHom T₁.L T₂.L) (h₁ : IsCrys PD T₁.ρ) (h₂ : IsCrys PD T₂.ρ) (a : LetA O n) {x : W.DD T₁}
    (hx : x ∈ mulSet W T₁ a (W.NΔ T₁)) : W.map F x ∈ mulSet W T₂ a (W.NΔ T₂) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨W.map F y, map_NΔ F h₁ h₂ hy, map_smulA W F a y⟩

theorem frobenius_cocycle_map (F : LatHom T₁.L T₂.L) (h₁ : IsCrys PD T₁.ρ) (h₂ : IsCrys PD T₂.ρ) (M : ℕ) (c : ZMod n) (x : ↥(W.wachCocyclesDelta T₁))
    (hx : HerrCocycleAtLetter W T₁ M c x) : HerrCocycleAtLetter W T₂ M c (mapZ F x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  unfold HerrCocycleAtLetter
  simp only [mapZ_coe]
  refine ⟨?_, ?_, ?_⟩
  · unfold InLetter at h1 ⊢
    rw [← map_smulA W F, h1]
  · rw [← W.map_γ, ← map_sub]
    exact map_mulSet F h₁ h₂ _ h2
  · exact map_mulSet F h₁ h₂ _ h3

theorem frobenius_cocycle_of_rho_data {T : LocLat G Qp LL O} (hF1 : F1 W) (hcr : IsCrys PD T.ρ) (hh M : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(hh : ℤ)) hh))
    (hM : hh < (PD.p - 1) * M) (C : Coord W I T) (c : ZMod n) (w : C.V) (j g sig : ℕ)
    (y z : ZMod n → C.V) (hρ : (latOf C).IsRho c j M g sig w y z)
    (hZ : (tot C y, tot C z) ∈ W.wachCocyclesDelta T) : HerrCocycleAtLetter W T M (c + (j : ZMod n)) ⟨_, hZ⟩ := by
  obtain ⟨τ, -, hy, -, hz⟩ := hρ
  have hzM := tot_sm C M z hz
  refine ⟨?_, ?_, hzM⟩
  · change (letE (c + (j : ZMod n)) : LetA O n) • tot C y = tot C y
    rw [hy, tot_single]
    exact C.t_letter _ _
  · change W.γD T W.gamK (tot C y) - tot C y ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T)
    rw [((mem_Z1DΔ _ _).1 hZ).1]
    obtain ⟨x, hx, hxz⟩ := hzM
    obtain ⟨x', hx', hφ⟩ := ((hF1 hh M hM).1 T hcr hJ).1 x hx
    refine ⟨I.d I.Bs.q • x' - x, (W.NΔ T).sub_mem (d_smul_NΔ _ hx') hx, ?_⟩
    rw [hxz, hφ, smul_sub, I.d_q, mul_smul]

theorem rho_fieldN (hF1 : F1 W) (hF2 : F2 W) (F : LatHom T₁.L T₂.L) (hcr₁ : IsCrys PD T₁.ρ)
    (hcr₂ : IsCrys PD T₂.ρ) (hh : ℕ)
    (hJ₁ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(hh : ℤ)) hh))
    (hJ₂ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₂.ρ τ (Set.Icc (-(hh : ℤ)) hh)) (hp : 2 ≤ PD.p)
    (C : Coord W I T₁) (h5 : ∀ i, (latOf C).P5M i hh) (Cu : Formalism.ExponentWindows.E.Cuts n) (H : ZMod n → ℕ → ℕ)
    (j g sig : ℕ) :
    ∀ c ∈ Cu.cuts, ∀ w, (latOf C).Wc Cu (Formalism.ExponentWindows.E.LamOf I.Bs Cu H) c w →
      ∀ y z, (latOf C).IsRho c j (Formalism.ExponentWindows.E.parM I.Bs.ℓ hh g) g sig w y z → (y, z) ∈ ZfN C F := by
  intro c hc w hw y z hρ
  have hM : hh < (PD.p - 1) * Formalism.ExponentWindows.E.parM I.Bs.ℓ hh g := by
    rw [Formalism.ExponentWindows.E.parM, I.ℓ_eq]
    have := Nat.lt_mul_div_succ (hh + 2 * g) (show 0 < PD.p - 1 by omega)
    omega
  obtain ⟨x, hxf, hx⟩ := (mem_Zf C _).1 (rho_field hF1 hF2 hcr₁ hh hJ₁ hp C h5 Cu H j g sig c hc w hw y z hρ)
  have hZ : (tot C y, tot C z) ∈ W.wachCocyclesDelta T₁ := hx ▸ x.2
  have hxe : x = ⟨_, hZ⟩ := Subtype.ext hx
  have hcoc := frobenius_cocycle_of_rho_data hF1 hcr₁ hh _ hJ₁ hM C c w j g sig y z hρ hZ
  rw [← hxe] at hcoc
  refine (mem_ZfN C F _).2 ⟨x, ⟨hxf, ?_⟩, hx⟩
  exact ((hF1 hh _ hM).2 T₁ T₂ F hcr₁ hcr₂ hJ₁ hJ₂ (c + (j : ZMod n)) x (mapZ F x) hcoc
    (frobenius_cocycle_map F hcr₁ hcr₂ _ _ x hcoc) rfl).symm

end Formalism.MainNotions.WachCoordinates.Br
end
end

