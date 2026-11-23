module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubspaceTrivialOutsideSplitPlac
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocS
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocalRows

open Formalism.IndefR.principalLevelFrame

theorem fixed_fd_of_isotIn {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A)
    (hadm : ∀ N : ℕ, 0 < N →
      FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, NG.Cong D.host.E n N κ → ρ κ x = x}))
    (π : NG.FinTyp D.host.E n) (hne : isotIn (D := D) ρ C π ≠ ⊥) (N : ℕ) (hN : 0 < N) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E n N κ → NG.rt D.host.E n κ f = f}) := by
  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : π.S →ₗ[ℂ] A,
      (IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold isotIn
    exact iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ (GAf D.host.E n → ℂ) := (LinearMap.ker Φ).map π.S.subtype
    have hS'le : S' ≤ π.S := by
      rintro f ⟨k, _, rfl⟩
      exact k.2
    have hS'st : ∀ h, ∀ f ∈ S', NG.rt D.host.E n h f ∈ S' := by
      rintro h f ⟨k, hk, rfl⟩
      refine ⟨⟨NG.rt D.host.E n h k, π.stable h k k.2⟩, ?_, rfl⟩
      show Φ _ = 0
      rw [hΦe h k, LinearMap.mem_ker.1 hk, map_zero]
    rcases π.irr S' hS'le hS'st with h0 | hall
    · rw [eq_bot_iff]
      intro k hk
      have : (k : GAf D.host.E n → ℂ) ∈ S' := ⟨k, hk, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E n → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      rw [show y = k from Subtype.ext hky.symm]
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 hk)
  set F := Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong D.host.E n N κ → NG.rt D.host.E n κ f = f} with hF
  set T := Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, NG.Cong D.host.E n N κ → ρ κ x = x} with hT
  have := hadm N hN
  have hFS : F ≤ π.S := Submodule.span_le.2 fun f hf => hf.1
  have hFT : ∀ f (hf : f ∈ F), Φ ⟨f, hFS hf⟩ ∈ T := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨hΦC ⟨_, rfl⟩, fun κ hκ => ?_⟩
      rw [← hΦe κ]
      congr 1
      exact Subtype.ext (hx.2 κ hκ)
    | zero =>
      have : (⟨0, hFS F.zero_mem⟩ : π.S) = 0 := rfl
      rw [this, map_zero]
      exact T.zero_mem
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hFS (F.add_mem hx hy)⟩ : π.S) = ⟨x, hFS hx⟩ + ⟨y, hFS hy⟩ := rfl
      rw [this, map_add (f := _)]
      exact T.add_mem ihx ihy
    | smul a x hx ih =>
      have : (⟨a • x, hFS (F.smul_mem a hx)⟩ : π.S) = a • ⟨x, hFS hx⟩ := rfl
      rw [this, map_smul]
      exact T.smul_mem a ih
  let g : F →ₗ[ℂ] T := LinearMap.codRestrict T (Φ ∘ₗ Submodule.inclusion hFS) (fun f => hFT f f.2)
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : Φ (Submodule.inclusion hFS a) = Φ (Submodule.inclusion hFS b) := congrArg Subtype.val hab
    exact Submodule.inclusion_injective hFS (hinj h1)
  exact Module.Finite.of_injective g hg

section Conj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem fixed_fd_of_conjT (π : NG.FinTyp L n) (N : ℕ)
    (h : FiniteDimensional ℂ ↥(Submodule.span ℂ
      {f | f ∈ (FinTyp.conjT π).S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f})) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f}) := by
  set S1 := Submodule.span ℂ {f | f ∈ π.S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f} with hS1
  set S2 := Submodule.span ℂ {f | f ∈ (FinTyp.conjT π).S ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f} with hS2
  have hmap : ∀ f ∈ S1, (fun g => star (f g)) ∈ S2 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨?_, fun κ hκ => ?_⟩
      · rw [conjT_S, mem_conjSub]
        simpa using hx.1
      · rw [← conj_rt, hx.2 κ hκ]
    | zero =>
      have : (fun g => star ((0 : GAf L n → ℂ) g)) = 0 := by
        funext g
        simp
      rw [this]
      exact S2.zero_mem
    | add x y _ _ hx hy =>
      have : (fun g => star ((x + y) g)) = (fun g => star (x g)) + (fun g => star (y g)) := by
        funext g
        simp
      rw [this]
      exact S2.add_mem hx hy
    | smul a x _ hx =>
      have : (fun g => star ((a • x) g)) = star a • (fun g => star (x g)) := by
        funext g
        simp [mul_comm]
      rw [this]
      exact S2.smul_mem _ hx
  let c : S1 →ₗ[ℝ] S2 :=
    { toFun := fun f => ⟨fun g => star ((f : GAf L n → ℂ) g), hmap f f.2⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by simp)
      map_smul' := fun r a => Subtype.ext (funext fun g => by simp) }
  have hc : Function.Injective c := by
    intro a b hab
    apply Subtype.ext
    funext g
    have := congrFun (congrArg Subtype.val hab) g
    exact star_injective this
  haveI : FiniteDimensional ℝ S2 := Module.Finite.trans ℂ S2
  haveI : FiniteDimensional ℝ S1 := Module.Finite.of_injective c hc
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ S1

theorem form_of_conjT (π : NG.FinTyp L n) (B' : (FinTyp.conjT π).S → (FinTyp.conjT π).S → ℂ)
    (hlin : ∀ x y z (c : ℂ), B' x (y + c • z) = B' x y + c * B' x z)
    (hherm : ∀ x y, B' x y = starRingEnd ℂ (B' y x))
    (hpos : ∀ x, x ≠ 0 → 0 < (B' x x).re)
    (hinv : ∀ h (x y x' y' : (FinTyp.conjT π).S), (x' : GAf L n → ℂ) = NG.rt L n h x →
      (y' : GAf L n → ℂ) = NG.rt L n h y → B' x' y' = B' x y) :
    ∃ B : π.S → π.S → ℂ, (∀ x y z (c : ℂ), B x (y + c • z) = B x y + c * B x z) ∧
      (∀ x y, B x y = starRingEnd ℂ (B y x)) ∧ (∀ x, x ≠ 0 → 0 < (B x x).re) ∧
      ∀ h (x y x' y' : π.S), (x' : GAf L n → ℂ) = NG.rt L n h x →
        (y' : GAf L n → ℂ) = NG.rt L n h y → B x' y' = B x y := by
  let c : π.S → (FinTyp.conjT π).S := fun f =>
    ⟨fun g => star ((f : GAf L n → ℂ) g), by rw [conjT_S, mem_conjSub]; simpa using f.2⟩
  have hc : ∀ f : π.S, ((c f : (FinTyp.conjT π).S) : GAf L n → ℂ) = fun g => star ((f : GAf L n → ℂ) g) := fun _ => rfl
  refine ⟨fun x y => starRingEnd ℂ (B' (c x) (c y)), ?_, ?_, ?_, ?_⟩
  · intro x y z a
    have e : c (y + a • z) = c y + (starRingEnd ℂ a) • c z := by
      apply Subtype.ext
      funext g
      simp [hc, mul_comm]
    simp only
    rw [e, hlin, map_add (f := _), map_mul, Complex.conj_conj]
  · intro x y
    simp only
    rw [hherm (c x) (c y)]
  · intro x hx
    simp only
    rw [Complex.conj_re]
    apply hpos
    intro h0
    apply hx
    apply Subtype.ext
    funext g
    have := congrFun (congrArg Subtype.val h0) g
    rw [hc] at this
    simpa using this
  · intro h x y x' y' hx hy
    simp only
    congr 1
    apply hinv h
    · rw [hc, hc, hx]
      rfl
    · rw [hc, hc, hy]
      rfl

end Conj

end GlobalTheory.RowLocalRows

namespace GlobalTheory.RowLocalRows

open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult


end GlobalTheory.RowLocalRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixedAtSplit

open Filter Topology IsDedekindDomain

theorem exists_ne_zero_norm_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletion F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F), ?_, ?_⟩
  · intro h0
    have := v.valuedAdicCompletion_eq_valuation' π
    rw [h0, map_zero, hπ] at this
    exact WithZero.coe_ne_zero this.symm
  · rw [Valued.toNormedField.norm_lt_one_iff, v.valuedAdicCompletion_eq_valuation', hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem valued_lt_one_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) (z : v.adicCompletion F)
    (hz : Valued.v (c z) < 1) : Valued.v z < 1 := by
  rw [← Valued.toNormedField.norm_lt_one_iff] at hz ⊢
  have h1 : ∀ y : v.adicCompletion F, ‖y‖ < 1 → ‖c y‖ < 1 := fun y hy => by
    have h2 := (hc.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.2 hy)
    rw [map_zero] at h2
    refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ?_
    simpa [Function.comp_def, map_pow] using h2
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_ne_zero_norm_lt_one v
  by_contra h
  push_neg at h
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    norm_num at h
  have hcz0 : 0 < ‖c z‖ := norm_pos_iff.2 ((map_ne_zero c).2 hz0)
  have hcϖ : 0 < ‖c ϖ‖ := norm_pos_iff.2 ((map_ne_zero c).2 hϖ0)
  have key : ∀ N : ℕ, ‖c ϖ‖ < ‖c z‖ ^ N := by
    intro N
    have hzN : 1 ≤ ‖z‖ ^ N := one_le_pow₀ h
    have hq : ‖ϖ / z ^ N‖ < 1 := by
      rw [norm_div, norm_pow, div_lt_one (by positivity)]
      exact lt_of_lt_of_le hϖ1 hzN
    have := h1 _ hq
    rw [map_div₀, map_pow, norm_div, norm_pow, div_lt_one (by positivity)] at this
    exact this
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (c z)) hz
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hcϖ)).exists
  exact lt_asymm hN (key N)

end GlobalTheory.FixedAtSplit

namespace GlobalTheory.FixedAtSplit

open IsDedekindDomain ValuativeRel

theorem mem_KOne_iff' {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (κ : GL (Fin n) (w.adicCompletion E)) :
    κ ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n) ↔
      ∀ a b, Valued.v (((κ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) - 1) a b) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [GlobalTheory.StepData.mem_KOne]
  exact forall_congr' fun a => forall_congr' fun b => he.lt_one_iff_lt_one

theorem mem_KOne_of_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : Continuous c) {n : ℕ}
    (A : GL (Fin n) (v.adicCompletion F))
    (h : Matrix.GeneralLinearGroup.map c.toRingHom A ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin n)) :
    A ∈ GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n) := by
  refine (mem_KOne_iff' A).2 fun a b => valued_lt_one_of_map c hc _ ?_
  have := (mem_KOne_iff' _).1 h a b
  convert this using 2
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.GeneralLinearGroup.map_apply]
  split_ifs <;> simp

end GlobalTheory.FixedAtSplit

namespace GlobalTheory.FixedAtSplit

theorem fixed_ne_bot_of_fixed_vector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.FinTyp L n) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS π.S s τ → ∀ f ∈ π.S, f ≠ 0 → (∀ κ : Formalism.AUTREP.GAf L n, TrivOutside {s.v} κ → s.loc n κ ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n) → NG.rt L n κ f = f) → GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥ := by
  intro L _ _ _ n π s τ hloc f hf hf0 hfix
  classical
  obtain ⟨c, _, hc, hci, _⟩ := id hloc
  have hspan := _root_.GlobalTheory.FinTypSpanLoc.main L n π s τ hloc c hc hci hf
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun {x y} hx hy v hv => by
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, mul_one]
      one_mem' := fun v _ => by simp
      inv_mem' := fun {x} hx v hv => by
        have h1 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
        have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
        simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
        exact h2 }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map c.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, hx, e⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = h
    rw [e]
    ext i j
    simp
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.CuspRep.ParLaws.isIrreducible_comp τ.irr φ hφ
  let ρ' : Representation ℂ H (GAf L n → ℂ) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [iSup_subtype'] at hspan
  obtain ⟨t, ht⟩ := Submodule.mem_iSup_iff_exists_finset.1 hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    LinearMap.intertwiningMap_of_isIntertwiningMap σ' ρ' j.1.1 fun g v => j.1.2.2 g.1 g.2 v
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)).comap φ
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk =>
    hfix k.1 k.2 (mem_KOne_of_map c hc _ hk)
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne ⊢
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hy0⟩
  obtain ⟨x, rfl⟩ := hφ h
  exact GlobalTheory.Parabolic.mem_fixed.1 hy x hh

end GlobalTheory.FixedAtSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalGlobal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SysFin

open GlobalTheory.CoefDuty

section Places
variable {R : Ranks} {H : Host R}

theorem intCast_mem_conj {v w : PlE H} (h : IsConjPl H v w) (n : ℤ) :
    (n : 𝓞 H.E) ∈ v.asIdeal ↔ (n : 𝓞 H.E) ∈ w.asIdeal :=
  h _ _ (by simp [map_intCast])

theorem intCast_mem_over {w : PlE H} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield H.E))}
    (h : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield H.E)) (𝓞 H.E)) = v.asIdeal) (n : ℤ) :
    (n : 𝓞 H.E) ∈ w.asIdeal ↔ (n : 𝓞 (maximalRealSubfield H.E)) ∈ v.asIdeal := by
  rw [← h, Ideal.mem_comap, map_intCast]

end Places

theorem finite_intCast_mem {K : Type} [Field K] [NumberField K] (N : ℤ) (hN : N ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | (N : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(N : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem exists_intCast_mem {K : Type} [Field K] [NumberField K] (q : HeightOneSpectrum (𝓞 K)) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : 𝓞 K) ∈ q.asIdeal := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot q.ne_bot
  have h := Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral (R := ℤ) x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨n, hn0, ?_⟩
  rw [Ideal.mem_comap, eq_intCast] at hn
  exact hn

theorem intCast_mem_of_dvd {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)} {n N : ℤ} (hd : n ∣ N)
    (h : (n : 𝓞 K) ∈ v.asIdeal) : (N : 𝓞 K) ∈ v.asIdeal := by
  obtain ⟨b, rfl⟩ := hd
  push_cast
  exact Ideal.mul_mem_right _ _ h

section Eig
variable {D : D7}

theorem genAt_mono {l : ℕ} {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q') {v : PlE D.host} {k : ℕ}
    (h : GenAt D l Q' v k) : GenAt D l Q v k :=
  ⟨h.1, h.2.1, h.2.2.1, fun hv => h.2.2.2.1 (hQ hv), h.2.2.2.2⟩

open Classical in
theorem eigSet_restrict {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) (l : ℕ) {Q Q' : Finset (PlE D.host)} (hQ : Q ⊆ Q')
    {c : PlE D.host → ℕ → ℂ} (hc : c ∈ EigSet X l Q) :
    (fun v k => if GenAt D l Q' v k then c v k else 0) ∈ EigSet X l Q' := by
  obtain ⟨-, y, hy, hy'⟩ := hc
  refine ⟨fun v k hg => if_neg hg, y, hy, fun v k s ϖ hg hcj hu => ?_⟩
  simp only [if_pos hg]
  exact hy' v k s ϖ (genAt_mono hQ hg) hcj hu

theorem eigSet_transport (M : MtFam D) {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m) (l : ℕ) (Q : Finset (PlE D.host))
    (c : PlE D.host → ℕ → ℂ) : c ∈ EigSet (M μ j a1 a2) l Q → c ∈ EigSet (M μ' j' b1 b2) l Q := by
  subst hμ hj; exact id

end Eig


end GlobalTheory.SysFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdentityIntegralUnitaryFrameCoordinatesOfUnitGra
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

namespace GlobalTheory.Mem.R3.LiftBrg

theorem castGL_mem_UA_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {m n : ℕ} (h : m = n) (x : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    castGL h x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin n) (Fin n) E) ↔
      x ∈ Formalism.L2.DIV.UA hc (1 : Matrix (Fin m) (Fin m) E) := by
  subst h
  have : castGL (rfl : m = m) x = x := by
    ext i j
    rfl
  rw [this]

theorem frameOK_one_of_gram_eq_one (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (i : Fin X.toD7.R.m) (t : TupU I U) (hg : (Vc X.toD7 i).gram = 1) : LiftBrg.FrameOK X I U i t 1 1 := by
  refine ⟨⟨1, (map_one _).symm⟩, one_mem _, fun x => ?_, one_mem _, one_mem _, fun PP _ => ?_⟩
  · rw [hg, one_mul, inv_one, mul_one]
    exact (castGL_mem_UA_one X.toD7.sp.cm (rkEq X i) x).symm
  · rw [one_mul]; exact one_mem _

end GlobalTheory.Mem.R3.LiftBrg
end

