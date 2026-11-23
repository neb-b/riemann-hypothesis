module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImage
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.IsoSub

theorem nonempty_equiv_of_isotypic {A M T Q S : Type*} [Ring A] [AddCommGroup M] [Module A M]
    [AddCommGroup T] [Module A T] [AddCommGroup Q] [Module A Q] [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (h : isotypicComponent A M S = ⊤) (j : T →ₗ[A] M)
    (hj : Function.Injective j) (f : T →ₗ[A] Q) (hf : Function.Surjective f) :
    IsSimpleModule A Q → Nonempty (Q ≃ₗ[A] S) := by
  intro hQ
  have hiso : IsIsotypicOfType A M S := IsIsotypicOfType.of_isotypicComponent_eq_top h
  have hss : IsSemisimpleModule A M := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.1 ?_)
    rw [← h]
    exact sSup_le_sSup fun m (hm : Nonempty (m ≃ₗ[A] S)) => IsSimpleModule.congr hm.some
  have hT : IsSemisimpleModule A T := IsSemisimpleModule.of_injective j hj
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker f)
  let e₁ : C ≃ₗ[A] Q :=
    (Submodule.quotientEquivOfIsCompl _ _ hC).symm.trans (f.quotKerEquivOfSurjective hf)
  have hC' : IsSimpleModule A C := IsSimpleModule.congr e₁
  let e₂ : C ≃ₗ[A] C.map j := Submodule.equivMapOfInjective j hj C
  have hCj : IsSimpleModule A (C.map j) := IsSimpleModule.congr e₂.symm
  obtain ⟨e₃⟩ := hiso (C.map j)
  exact ⟨e₁.symm.trans (e₂.trans e₃)⟩

def inclusion {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] {R : Representation ℂ G Y}
    (S : Subrepresentation R) : S.toRepresentation.IntertwiningMap R :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem equiv_of_isSubquotient (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hR : ⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤)
    (hsq : IsSubquotient σ R) : Nonempty (σ.Equiv ρ) := by
  have hρs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  have hσs : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).1 hσ
  have htop : Subrepresentation.asSubmodule (GlobalTheory.CuspFactor.spanRep R ρ) = ⊤ := by
    have hX : (GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule = ⊤ := hR
    apply SetLike.coe_injective
    show ((GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule : Set Y) = Set.univ
    rw [hX]
    first
      | rfl
      | exact Submodule.top_coe
      | simp
  have h : isotypicComponent (MonoidAlgebra ℂ G) R.asModule ρ.asModule = ⊤ := by
    rw [← GlobalTheory.CuspFactor.spanRep_asSubmodule R ρ hρ]
    exact htop
  obtain ⟨S, f, hf⟩ := hsq
  let j := Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (GlobalTheory.CompanionTheory.IsoSub.inclusion S)
  have hj : Function.Injective j := by
    first
      | exact Subtype.val_injective
      | (intro x y hxy; exact Subtype.val_injective hxy)
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  have hf' : Function.Surjective f' := by
    first
      | exact hf
      | (intro y; obtain ⟨x, hx⟩ := hf y; exact ⟨x, hx⟩)
  exact (GlobalTheory.CuspFactor.nonempty_equiv_iff σ ρ).2
    (GlobalTheory.CompanionTheory.IsoSub.nonempty_equiv_of_isotypic h j hj f' hf' hσs)

end GlobalTheory.CompanionTheory.IsoSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntLtrSubThetaCConst
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

namespace ThcInt

theorem scalC_mul (a b : IdeleGroup k) :
    (scalC (a * b) : GL ι 𝔸[k]) = scalC a * scalC b := by
  simp only [scalC, map_mul]

theorem scalC_commute (a : IdeleGroup k) (A : GL ι 𝔸[k]) :
    (scalC a : GL ι 𝔸[k]) * A = A * scalC a := by
  apply Units.ext
  simp only [Units.val_mul, scalC, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact (Matrix.scalar_commute _ (fun r ↦ Commute.all _ r) _)

theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  refine Continuous.units_map _ ?_
  refine continuous_matrix fun i j ↦ ?_
  by_cases h : i = j
  · subst h
    simpa [Matrix.scalar_apply] using continuous_id'
  · simpa [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h] using continuous_const

theorem thetaC_ltr (A h : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    thetaC (ltr A F) h = thetaC F (A * h) := by
  simp only [thetaC, ltr, Units.val_mul, Matrix.mulVec_mulVec]

theorem ltr_apply_zero (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) : ltr A F 0 = F 0 := by
  simp [ltr]

theorem continuousOn_thetaC {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι))
    {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) : ContinuousOn (thetaC F) C := by
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF hC
  refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hb h hh ξ
  refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
  exact Units.continuous_val.matrix_mulVec continuous_const

theorem continuous_char (ω : HeckeCharacter k) :
    Continuous fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ) :=
  continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_subtype_val)

theorem integrableOn_thetaCIntegrand {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι))
    (A : GL ι 𝔸[k]) (ω : HeckeCharacter k) (s : IdeleGroup k) :
    IntegrableOn (fun u : normOneSubgroup k ↦
      thetaC (ltr A F) (scalC (s * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hφ : Continuous fun u : normOneSubgroup k ↦
      A * (scalC (s * (u : IdeleGroup k)) : GL ι 𝔸[k]) :=
    continuous_const.mul (continuous_scalC.comp (continuous_const.mul continuous_subtype_val))
  have h1 : ContinuousOn (fun u : normOneSubgroup k ↦
      thetaC (ltr A F) (scalC (s * (u : IdeleGroup k))))
      (closure (normOneFundamentalDomain k)) := by
    simp only [thetaC_ltr]
    exact (continuousOn_thetaC hF (hE.image hφ)).comp hφ.continuousOn (Set.mapsTo_image _ _)
  exact ((h1.mul (continuous_char ω).continuousOn).integrableOn_compact hE).mono_set subset_closure

theorem integrableOn_char' (ω : HeckeCharacter k) :
    IntegrableOn (fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) :=
  ((continuous_char ω).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain k)).mono_set subset_closure

theorem thetaCInt_ltr_sub_thetaCConst (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}) :
    thetaCInt w (ltr A F) ω t - thetaCConst (ltr A F) ω =
      ∫ u in normOneFundamentalDomain k,
        (thetaC (ltr A F) (scalC (moduleSection w t * (u : IdeleGroup k))) - ltr A F 0) *
          (ω.toIdele (u : IdeleGroup k) : ℂ) ∂normOneMeasure k := by
  rw [thetaCInt, thetaCConst, volChar, ← integral_const_mul,
    ← integral_sub (integrableOn_thetaCIntegrand hF A ω _) ((integrableOn_char' ω).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp only []
  ring

end ThcInt


open ThcInt in
theorem exists_norm_thetaCInt_sub_le (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) {C : Set (GL ι 𝔸[k])}
    (hC : IsCompact C) (r : ℕ) :
    ∃ M : ℝ, ∀ A ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaCInt w (ltr A Ψ) ω t - thetaCConst (ltr A Ψ) ω‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hS : Continuous fun p : normOneSubgroup k × GL ι 𝔸[k] ↦
      p.2 * (scalC (p.1 : IdeleGroup k) : GL ι 𝔸[k]) :=
    continuous_snd.mul (continuous_scalC.comp (continuous_subtype_val.comp continuous_fst))
  obtain ⟨M, hM⟩ := GlobalTheory.T.theta_sub_value_zero_rapid_decay w hΨ ((hE.prod hC).image hS) r
  refine ⟨M * (normOneMeasure k).real (normOneFundamentalDomain k), fun A hA t ht ↦ ?_⟩
  rw [thetaCInt_ltr_sub_thetaCConst w hΨ A ω t, ← mul_assoc]
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top k)
    fun u hu ↦ ?_
  have hc : A * (scalC (moduleSection w t * (u : IdeleGroup k)) : GL ι 𝔸[k]) =
      scalC (moduleSection w t) * (A * scalC (u : IdeleGroup k)) := by
    rw [scalC_mul, ← mul_assoc, ← mul_assoc, scalC_commute]
  rw [norm_mul, Circle.norm_coe, mul_one, thetaC_ltr, ltr_apply_zero, hc]
  exact hM _ ⟨(u, A), ⟨subset_closure hu, hA⟩, rfl⟩ t ht

end GlobalTheory.CompanionTheory.AdelicThetaSeries
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrETransposeEqPhiSeq
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.GlTranspose

variable {n : ℕ} {A : Type} [Ring A]

theorem epw_zero (e : Fin n → Fin n → A) (a b : Fin n) :
    Epw e 0 a b = if a = b then 1 else 0 := by
  rw [Epw]

theorem epw_succ (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, e a c * Epw e m c b := by
  rw [Epw]

theorem epw_succ_right (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, Epw e m a c * e c b := by
  induction m generalizing a b with
  | zero =>
    simp [epw_succ, epw_zero]
  | succ m ih =>
    calc Epw e (m + 1 + 1) a b = ∑ c, e a c * ∑ d, Epw e m c d * e d b := by
          rw [epw_succ]
          exact sum_congr rfl fun c _ => by rw [ih]
      _ = ∑ d, (∑ c, e a c * Epw e m c d) * e d b := by
          simp only [mul_sum, sum_mul, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ c, Epw e (m + 1) a c * e c b := sum_congr rfl fun d _ => by rw [epw_succ]

theorem bco_zero_zero (N : A) (τ : ℕ → A) : bco N τ 0 0 = 1 := by rw [bco]

theorem bco_zero_succ (N : A) (τ : ℕ → A) (j : ℕ) : bco N τ 0 (j + 1) = 0 := by rw [bco]

theorem bco_succ_zero (N : A) (τ : ℕ → A) (m : ℕ) :
    bco N τ (m + 1) 0 = N * bco N τ m 0 - τ m := by rw [bco]

theorem bco_succ_succ (N : A) (τ : ℕ → A) (m j : ℕ) :
    bco N τ (m + 1) (j + 1) = bco N τ m j + N * bco N τ m (j + 1) := by rw [bco]

theorem bco_eq_zero (N : A) (τ : ℕ → A) (m j : ℕ) (h : m < j) : bco N τ m j = 0 := by
  induction m generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact bco_zero_succ N τ j
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [bco_succ_succ, ih j (by omega), ih (j + 1) (by omega)]
    simp

theorem bco_self (N : A) (τ : ℕ → A) (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => exact bco_zero_zero N τ
  | succ m ih =>
    rw [bco_succ_succ, ih, bco_eq_zero N τ m (m + 1) (by omega)]
    simp

theorem phiSeq_eq (N : A) (τ : ℕ → A) (m : ℕ) :
    phiSeq N τ m = τ m - ∑ j ∈ range m, bco N τ m j * phiSeq N τ j := by
  rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m]

section Gl

variable (e : Fin n → Fin n → A)
  (he : ∀ a b c d, e a b * e c d - e c d * e a b =
    (if b = c then e a d else 0) - (if a = d then e c b else 0))
include he

theorem comm_epw (m : ℕ) (a b c d : Fin n) :
    e a b * Epw e m c d - Epw e m c d * e a b =
      (if b = c then Epw e m a d else 0) - (if a = d then Epw e m c b else 0) := by
  induction m generalizing c d with
  | zero =>
    simp only [epw_zero]
    by_cases h1 : c = d
    · subst h1
      by_cases h2 : b = c
      · subst h2; simp
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h2, h3]
    · by_cases h2 : b = c
      · subst h2
        by_cases h3 : a = d
        · subst h3; simp [h1]
        · simp [h1, h3]
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h1, h2, h3]
  | succ m ih =>
    have step : ∀ f, e a b * (e c f * Epw e m f d) - (e c f * Epw e m f d) * e a b =
        ((if b = c then e a f else 0) - (if a = f then e c b else 0)) * Epw e m f d +
          e c f * ((if b = f then Epw e m a d else 0) - (if a = d then Epw e m f b else 0)) := by
      intro f
      rw [← he a b c f, ← ih f d]
      noncomm_ring
    rw [epw_succ e m c d, mul_sum, sum_mul, ← sum_sub_distrib, sum_congr rfl (fun f _ => step f)]
    simp only [sub_mul, mul_sub, sum_add_distrib, sum_sub_distrib, ite_mul, mul_ite, zero_mul,
      mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : a = d <;>
      simp only [h1, h2, if_true, if_false, ← epw_succ, sum_const_zero] <;> abel

theorem transpose_step (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) b a =
      ∑ c, Epw e m c a * e b c + (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
  have h : Epw e (m + 1) b a - ∑ c, Epw e m c a * e b c =
      (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
    rw [epw_succ, ← sum_sub_distrib,
      sum_congr rfl (fun c _ => comm_epw e he m b c c a), sum_sub_distrib]
    by_cases h1 : a = b
    · subst h1; simp [trE]
    · have h2 : ¬ b = a := fun h => h1 h.symm
      simp [h1, h2]
  rw [add_sub_assoc, ← h]
  abel

theorem transpose_poly (m : ℕ) (a b : Fin n) :
    Epw e m b a =
      ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * Epw (fun a b => e b a) j a b := by
  induction m generalizing a b with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, bco_zero_zero, one_mul, epw_zero]
    simp only [eq_comm]
  | succ m ih =>
    set f : Fin n → Fin n → A := fun a b => e b a with hf
    set N : A := (n : A) with hN
    set τ : ℕ → A := trE e with hτ
    have key : ∑ c, Epw e m c a * e b c =
        ∑ j ∈ range (m + 1), bco N τ m j * Epw f (j + 1) a b := by
      simp only [epw_succ_right f, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun c _ => ?_
      rw [ih a c, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_assoc]
    have hn : N * Epw e m b a =
        ∑ j ∈ range (m + 1), N * bco N τ m (j + 1) * Epw f (j + 1) a b +
          N * bco N τ m 0 * Epw f 0 a b := by
      rw [← sum_range_succ' (fun j => N * bco N τ m j * Epw f j a b) (m + 1),
        sum_range_succ _ (m + 1), bco_eq_zero N τ m (m + 1) (by omega), ih a b, mul_sum]
      simp [mul_assoc]
    rw [transpose_step e he, key, hn, sum_range_succ' _ (m + 1), bco_succ_zero]
    simp only [bco_succ_succ, add_mul, sum_add_distrib, sub_mul, epw_zero f]
    by_cases h1 : a = b
    · simp [h1]
      try abel
    · simp [h1]
      try abel

theorem trE_eq_sum (m : ℕ) :
    trE e m = ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * trE (fun a b => e b a) j := by
  have h : trE e m = ∑ a, Epw e m a a := rfl
  rw [h, sum_congr rfl (fun a _ => transpose_poly e he m a a), sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [trE, mul_sum]

end Gl

theorem trE_transpose_eq_phiSeq (n : ℕ) {A : Type} [Ring A] [Algebra ℂ A]
    (e : Fin n → Fin n → A)
    (he : ∀ a b c d, e a b * e c d - e c d * e a b =
      (if b = c then e a d else 0) - (if a = d then e c b else 0)) (m : ℕ) :
    trE (fun a b => e b a) m = phiSeq (n : A) (trE e) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h := trE_eq_sum e he m
    rw [sum_range_succ, bco_self, one_mul] at h
    have hs : ∑ j ∈ range m, bco (n : A) (trE e) m j * phiSeq (n : A) (trE e) j =
        ∑ j ∈ range m, bco (n : A) (trE e) m j * trE (fun a b => e b a) j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
    rw [phiSeq_eq, hs, h, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.WaveMult.GlTranspose
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TranslatedLengthBoundedDerivative
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

variable {n : ℕ}

def lmulCLM (a : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y
      map_add' := mul_add a
      map_smul' := fun r y => by simp }

theorem lmulCLM_apply (a y : Mat n) : lmulCLM a y = a * y := rfl

theorem inv_mul_mem_GLs {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x⁻¹ * y ∈ GLs n := by
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have h1 : IsUnit (x⁻¹).det := Matrix.isUnit_nonsing_inv_det x hxu
  show (x⁻¹ * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero h1.ne_zero hy

theorem lg_left_facts : LgFacts → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ GLs n,
    ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧
    (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧
    ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C := by
  intro hL n
  obtain ⟨-, -, -, hsm, hcpt, -, C₀, hC₀⟩ := hL n
  refine ⟨2 * |C₀|, by positivity, fun x hx => ?_⟩
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have hsm' : ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) :=
    hsm.comp (lmulCLM x⁻¹).contDiff.contDiffOn (fun y hy => inv_mul_mem_GLs hx hy)
  refine ⟨hsm', fun R => ?_, fun y hy p => ?_⟩
  · have hxU : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hxu
    let X : G n := hxU.unit
    have hXv : (X : Mat n) = x := rfl
    have hXi : ((X⁻¹ : G n) : Mat n) = x⁻¹ := by
      rw [Matrix.coe_units_inv, hXv]
    have hset : {y : G n | lg (x⁻¹ * y.val) ≤ R} = (fun z : G n => X * z) '' {z : G n | lg z.val ≤ R} := by
      ext y
      constructor
      · intro hy
        refine ⟨X⁻¹ * y, ?_, by simp⟩
        show lg ((X⁻¹ * y : G n) : Mat n) ≤ R
        rw [Units.val_mul, hXi]
        exact hy
      · rintro ⟨z, hz, rfl⟩
        show lg (x⁻¹ * ((X * z : G n) : Mat n)) ≤ R
        rw [Units.val_mul, ← hXi, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
        exact hz
    rw [hset]
    exact (hcpt R).image (continuous_const.mul continuous_id)
  · have hw : x⁻¹ * y ∈ GLs n := inv_mul_mem_GLs hx hy
    have hdiff : DifferentiableAt ℝ lg (x⁻¹ * y) :=
      (hsm.contDiffAt (isOpen_GLs.mem_nhds hw)).differentiableAt (by simp)
    have hder : fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y
        = (fderiv ℝ lg (x⁻¹ * y)).comp (lmulCLM x⁻¹) :=
      ((hdiff.hasFDerivAt).comp y (lmulCLM x⁻¹).hasFDerivAt).fderiv
    have hCle : C₀ ≤ |C₀| := le_abs_self C₀
    rw [hder, ContinuousLinearMap.comp_apply, lmulCLM_apply, ← mul_assoc]
    obtain ⟨b, i, j⟩ := p
    have h1 := abs_le.1 (hC₀ _ hw (b, i, j))
    have h2 := abs_le.1 (hC₀ _ hw (b, j, i))
    cases b
    · have e : hm ((false, i, j) : Ix n) = bs (false, i, j) - bs (false, j, i) := by
        simp [hm, bs]
      rw [e, mul_sub, map_sub, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have e : hm ((true, i, j) : Ix n) = bs (true, i, j) + bs (true, j, i) := by
        simp [hm, bs]
      rw [e, mul_add, map_add (f := _), abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end GlobalTheory.CompanionTheory.WaveSpd
end
end

