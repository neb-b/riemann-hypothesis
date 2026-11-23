module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.TwistNewform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THolLift
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
namespace UpperTheory.V.Sd
variable {F : Type} [Field F] [NumberField F]
private theorem val_pow (ω : HChar F) (w : Pl F) (n : ℕ) : (ω ^ n).val w = ω.val w ^ n := by
  induction n with
  | zero => simp [HChar.val, HChar.locK, HChar.loc]
  | succ n ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]
private theorem norm_chiI {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ω : HChar F) (hω : IsOfFinOrder ω) (c : Pl F → ℕ)
    (I : Ideal (𝓞 F)) : ‖ι.symm (chiI ω c I)‖ ≤ 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
  refine finprod_induction (fun x : ℂ => ‖ι.symm x‖ ≤ 1) (by simp) ?_ ?_
  · intro x y hx hy
    rw [map_mul, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  · intro w
    rw [map_pow, norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    split_ifs
    · have h1 : (ι.symm ((ω.val w : ℂˣ) : ℂ)) ^ n = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, ← val_pow, h, ← pow_zero ω, val_pow]; simp
      have h2 := congrArg norm h1
      rw [norm_pow, norm_one] at h2
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2).le
    · simp
private abbrev Idx (F : Type) [Field F] : Type := {𝔪 : Ideal (𝓞 F) // 𝔪 ≠ ⊥}
open Classical in
private def fT {K : Type} [Field K] (w : Pl F) (e : K) : Module.End K (Idx F → K) where
  toFun v 𝔪 := v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0
  map_add' c d := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;> simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.add_apply] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;>
      simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring
open Classical in
omit [NumberField F] in
private theorem fT_apply {K : Type} [Field K] (w : Pl F) (e : K) (v : Idx F → K) (𝔪 : Idx F) :
    fT w e v 𝔪 = v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0 := rfl
variable [IsTotallyReal F]
private def SS (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) : Submodule ℂ (TR.Sm F 2) where
  carrier := {φ | IsHol k c ω φ ∧ ∃ c₀ a, HasExp φ.1 k c₀ a}
  zero_mem' := ⟨(holLin F k c ω).1, _, _, (holLin F k c ω).2.1⟩
  add_mem' := by
    rintro φ ψ ⟨h1, c₀, a, h2⟩ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 φ ψ 1 h1 h3
    have e2 := (holLin F k c ω).2.2.2.1 φ.1 ψ.1 1 _ _ _ _ h2 h4
    rw [one_smul] at e1 e2
    exact ⟨e1, _, _, e2⟩
  smul_mem' := by
    rintro z ψ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 0 ψ z (holLin F k c ω).1 h3
    have e2 := (holLin F k c ω).2.2.2.1 0 ψ.1 z _ _ _ _ (holLin F k c ω).2.1 h4
    rw [zero_add] at e1 e2
    exact ⟨e1, _, _, e2⟩
private def cf {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : Ideal (𝓞 F) → ℂ := φ.2.2.choose_spec.choose
private theorem cf_spec {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : ∃ c₀, HasExp φ.1.1 k c₀ (cf φ) :=
  ⟨_, φ.2.2.choose_spec.choose_spec⟩
private theorem cf_eq {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a} (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) :
    cf φ 𝔪.1 = a 𝔪.1 := by
  obtain ⟨d, hd⟩ := cf_spec φ
  exact (expUnique F _ k _ _ _ _ hd h).2 _ 𝔪.2
private def Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) :
    SS k c ω →ₛₗ[(ι.symm : ℂ →+* Qbar l)] (Idx F → Qbar l) where
  toFun φ 𝔪 := ι.symm (cf φ 𝔪.1)
  map_add' φ ψ := by
    funext 𝔪
    obtain ⟨_, h2⟩ := cf_spec φ
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 _ _ 1 _ _ _ _ h2 h4
    simp only [one_smul] at e2
    rw [cf_eq (φ + ψ) e2]
    simp
  map_smul' z ψ := by
    funext 𝔪
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 0 _ z _ _ _ _ (holLin F k c ω).2.1 h4
    simp only [zero_add] at e2
    rw [cf_eq (z • ψ) e2]
    simp
private theorem Phi_eq {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) : Phi ι k c ω φ 𝔪 = ι.symm (a 𝔪.1) := congrArg ι.symm (cf_eq φ h 𝔪)
private theorem fT_Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (w : Pl F) (𝔪 : Idx F) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) 𝔪 = ι.symm (hkCoef k c ω w a 𝔪.1) := by
  rw [fT_apply, Phi_eq ι φ h, hkCoef, map_add (f := _), map_mul ι.symm _ (coefDiv _ _ _), coefDiv]
  split_ifs with hd
  · rw [Phi_eq ι φ h]
  · rw [map_zero]
private def hkS {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F} (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) : SS k c ω :=
  ⟨hk k w (c w) φ.1, (holHk F k hk1 c ω hω φ.1 φ.2.1 w).1, by
    obtain ⟨_, h⟩ := cf_spec φ
    obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
    exact ⟨d, _, hd⟩⟩
private theorem Phi_hkS {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) = Phi ι k c ω (hkS hk1 c hω w φ) := by
  funext 𝔪
  obtain ⟨_, h⟩ := cf_spec φ
  obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
  rw [fT_Phi ι φ h, Phi_eq ι (hkS hk1 c hω w φ) hd]
private theorem Phi_inj {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) : Function.Injective (Phi ι k c ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro φ h0
  obtain ⟨_, h⟩ := cf_spec φ
  refine Subtype.ext (expInj F k hk1 c ω hω φ.1 φ.2.1 _ _ h fun 𝔪 h𝔪 => ?_)
  have := congrFun h0 ⟨𝔪, h𝔪⟩
  rw [Phi_eq ι φ h] at this
  simpa using this
end UpperTheory.V.Sd
open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.holLift_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.HolLift := by
  intro hP F _ _ _ l _ ι k hk1 c hc ω hω φ c₀ a t hφ hexp hint h1 ht hcong
  haveI : RingHomSurjective (ι.symm : ℂ →+* Qbar l) := ⟨ι.symm.surjective⟩
  haveI := _root_.UpperTheory.V.Sd.holomorphic_finite_of_printed_hida hP F k c hc ω hω
  haveI : FiniteDimensional ℂ (SS k c ω) :=
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ : TR.Sm F 2 | IsHol k c ω φ})
      fun ψ hψ => Submodule.subset_span hψ.1
  set V : Submodule (Qbar l) (Idx F → Qbar l) := (⊤ : Submodule ℂ (SS k c ω)).map (Phi ι k c ω) with hV
  have hfd : FiniteDimensional (Qbar l) V :=
    Module.Finite.iff_fg.2 (Submodule.FG.map _ (IsNoetherian.noetherian _))
  let e : Pl F → Qbar l := fun w => ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))
  have he : ∀ p, ‖e p‖ ≤ 1 := by
    intro p
    simp only [e, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    exact mul_le_one₀ (norm_chiI ι ω hω c _) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
  have hmem : ∀ p : Pl F, ∀ v ∈ V, fT p (e p) v ∈ V := by
    rintro p _ ⟨g, -, rfl⟩
    exact ⟨hkS hk1 c hω p g, trivial, (Phi_hkS ι hk1 c hω p g).symm⟩
  let T : Pl F → Module.End (Qbar l) V := fun p => (fT p (e p)).restrict (hmem p)
  have hT : ∀ p (v : V), (T p v).1 = fT p (e p) v.1 := fun _ _ => rfl
  let f : SS k c ω := ⟨φ, hφ, _, _, hexp⟩
  obtain ⟨h, b, hne, -, heig, hb⟩ := delSerre l (Idx F) (Pl F) V hfd T
    (by
      intro p q
      ext1 v
      apply Subtype.ext
      obtain ⟨_, g, -, rfl⟩ := v
      simp only [Module.End.mul_apply, hT, e, Phi_hkS ι hk1 c hω]
      exact congrArg _ (Subtype.ext ((holHk F k hk1 c ω hω g.1 g.2.1 p).2.1 q)))
    (by
      intro p v hv n
      rw [hT, fT_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv _) ?_)
      rw [norm_mul]
      refine mul_le_one₀ (he p) (norm_nonneg _) ?_
      split_ifs
      · exact hv _
      · simp)
    (by
      intro p v hv n
      rw [hT, fT_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hv _) ?_)
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) (he p)).trans_lt ?_
      split_ifs
      · exact hv _
      · simp)
    ⟨Phi ι k c ω f, f, trivial, rfl⟩ (fun p => ι.symm (t p))
    (by
      intro n
      show ‖Phi ι k c ω f n‖ ≤ 1
      rw [Phi_eq ι f hexp]
      exact hint _ n.2)
    ⟨⟨⊤, top_ne_bot⟩, by
      show ‖Phi ι k c ω f _‖ = 1
      rw [Phi_eq ι f hexp]; exact h1⟩
    ht
    (by
      intro p n
      rw [hT]
      show ‖fT p (e p) (Phi ι k c ω f) n - ι.symm (t p) * Phi ι k c ω f n‖ < 1
      rw [fT_Phi ι f hexp, Phi_eq ι f hexp, ← map_mul, ← map_sub]
      exact hcong p _ n.2)
  obtain ⟨_, g, hg, rfl⟩ := h
  refine ⟨g.1, fun w => ι (b w), ⟨g.2.1, fun h0 => hne ?_, fun w => ?_⟩, fun w => ?_⟩
  · apply Subtype.ext
    show Phi ι k c ω g = 0
    rw [show g = 0 from Subtype.ext h0, map_zero]
  · have h2 : fT w (e w) (Phi ι k c ω g) = b w • Phi ι k c ω g := congrArg Subtype.val (heig w)
    have h3 : hkS hk1 c hω w g = ι (b w) • g := by
      apply Phi_inj ι hk1 c hω
      rw [← Phi_hkS, LinearMap.map_smulₛₗ]
      refine h2.trans ?_
      simp
    exact congrArg Subtype.val h3
  · rw [map_sub, RingEquiv.symm_apply_apply]
    exact hb w
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TOrdAbove
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Sd.OrdinaryAbove
section Loc
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
end Loc
private theorem norm_fin {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    (ξ : G F Ω →* (Qbar l)ˣ) (hξ : IsOpen (ξ.ker : Set (G F Ω))) (g : G F Ω) : ‖(ξ g : Qbar l)‖ = 1 := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : Finite (G F Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ hξ
  have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ξ (g ^ ξ.ker.index) = 1 := Subgroup.pow_index_mem ξ.ker g
  have h2 : ‖(ξ g : Qbar l)‖ ^ ξ.ker.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 h2
private theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem cont_cyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cont_cyc F Ω l
theorem central_weil_ordinary_above (hP : _root_.UpperTheory.V.Af.HypothesesH') {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {ξ : G F Ω →* (Qbar l)ˣ} {s c m a π r}
    (H : OrdForm ι ξ s c m a π r) {w : HeightOneSpectrum (𝓞 F)} (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {ar : Weil h →* (w.adicCompletion F)ˣ} (har : IsLocalArtin h ar)
    {σ : SmIrr (GL (Fin 2) (w.adicCompletion F))} (hσ : LocIsotypic π.finPart w σ) (t : Weil h) (z : ℂ)
    (hz : ∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (ar t)) v = z • v) :
    ‖ι.symm z‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ ((s + 1) * deg t) := by
  have e : Matrix.GeneralLinearGroup.det.comp r * cycBar F Ω l ^ (((2 : ℕ) : ℤ) - 1) = cycBar F Ω l ^ (s + 1) * ξ := by
    rw [H.det, _root_.zpow_add, mul_right_comm]
    norm_num
  have hc : Continuous (cycBar F Ω l ^ (s + 1) * ξ : G F Ω →* (Qbar l)ˣ) := by
    rw [← e]
    exact (Matrix.GeneralLinearGroup.continuous_det.comp H.cont).mul ((cont_cyc F Ω l).zpow _)
  obtain ⟨χ, hχ⟩ := (_root_.UpperTheory.V.Af.algOfCyc_s hP F Ω l ι).1 _ hc fun v hv => by
    have hA := isPlaceOver_placeOf Ω v
    refine ⟨_, hA, s + 1, 1, one_pos, fun g hg => ?_⟩
    have h1 : ξ g = 1 := (H.ram v _ hA).2 (Or.inr hv) hg
    rw [pow_one, MonoidHom.mul_apply, h1, mul_one, MonoidHom.zpow_apply, ← _root_.zpow_add, add_neg_cancel, zpow_zero]
  have hd := (_root_.UpperTheory.V.Af.self_dual_real_of_printed_hida hP F Ω l ι 2 one_le_two r π H.att _ χ (dualTw_det r) (e ▸ hχ)).1
  have h1 := UpperTheory.central_char_sq_eq_of_isSelfDualBy F π χ hd w σ hσ _ z hz
  rw [_root_.UpperTheory.heckeChar_localArtin_eq_cyclotomic_twist' hP.litN F Ω l ι χ ξ (s + 1) H.ξ_open hχ w hw A h ar har t] at h1
  have h2 := congrArg (fun x => ‖ι.symm x‖) h1
  simp only [map_pow, map_mul, map_zpow₀, map_natCast, RingEquiv.symm_apply_apply, norm_pow, norm_mul, norm_zpow,
    norm_fin ξ H.ξ_open, mul_one] at h2
  exact (pow_left_inj₀ (norm_nonneg _) (zpow_nonneg (norm_nonneg _) _) two_ne_zero).1 h2
end UpperTheory.V.Sd.OrdinaryAbove
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPhiEx
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
private theorem chi_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (E : W.GDet n A G) (f : A →+* A') (g : G) :
    (E.map f).chi (MonoidAlgebra.single g 1) = (E.chi (MonoidAlgebra.single g 1)).map f := by
  rw [← (AlgebraTools.Det.mapApi E f).1, MonoidAlgebra.mapRingHom_single, map_one]
theorem UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), (∃ B : W.UniversalOrdinaryDeterminantRing K.r, True) ∧ ∀ B : W.UniversalOrdinaryDeterminantRing K.r, ∃ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X n B φ := by
  intro U Ω _ _ _ l _ c D T _ _ c' h K X n
  obtain ⟨hs, hq, hk⟩ := phiKer K.V
  obtain ⟨E, hE, hcp, hc⟩ := phiDet (maximalIdeal X.B) (algebraMap X.B X.A) X.inj K.V.pr hs hq (K.rho X n) (K.cpT X n)
    (fun g => (phiCpMap K X n g).2.2.2) (phiCpCont K X n)
    fun U hU hle => hk U hU fun A v hA hv => (phiUnr K X n A v hA hv).trans hle
  obtain ⟨ψ, hψ⟩ := phiPsiEx K X n
  obtain ⟨p, hD, hp⟩ := phiPair K.r X.inj (by norm_num) K.V.pr hs (K.rho X n) E ψ hE hc
    (fun g => (congrArg _ (hcp g)).trans (phiCpRed K X n g)) (phiIsPsi K X n ψ hψ) (phiPol K X n)
    (fun v => ⟨_, rfl, phiFlag K X n ψ hψ v⟩) (phiIne K X n)
  obtain ⟨B₀⟩ := U.b0 l T.L Ω K.s K.V c' 4 K.r X.B ⟨p⟩
  refine ⟨⟨B₀, trivial⟩, fun B => ?_⟩
  obtain ⟨φ, ⟨h1, h2⟩, -⟩ := B.univ X.B p
  refine ⟨φ, fun g => ?_, fun v i g => ?_⟩
  · have e := chi_map B.u.D (φ : B.B →+* X.B) (K.V.pr g)
    rw [h1, hD] at e
    exact e.symm.trans (hcp g)
  · have e := congrArg Units.val (DFunLike.congr_fun (h2 v i) g)
    rw [hp] at e
    exact e.trans (hψ v i g)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistNewform
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open Polynomial Pointwise
namespace GlobalTheory.Ord2
open TwDet SrcForm
private theorem sources_of_spherical (P : _root_.UpperTheory.V.Af.HypothesesH') (hT : TwNewQ) (hF : UpperTheory.V.Z.Kato.WeilSphericalRecords.FrobRoot) (l : ℕ) [hl : Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (hl2 : l ≠ 2) (he : 1 ≤ e) (h : admitted ι e W)
    (hS : UpperTheory.V.Z.Kato.SphAt ι e W) : GlobalTheory.Ord2.SrcL ι e W := by
  have hl0 : 0 < l := hl.out.pos
  obtain ⟨N, hN, hNk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (ker_open h.cont h.det2)
    (Abelianization.commutator_subset_ker (dt W))
  have hθN : KillsMu N (dt W) := fun s hs => hNk s hs
  obtain ⟨A, χ, κ, hA, hχ, hfl, hine, hk⟩ := h.flag
  set φ : G ℚ Ω →* (Qbar l)ˣ := (dt W)⁻¹ * χ⁻¹ with hφdef
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have hφ : KillsMu (N * l) φ :=
    killsMu_mul (killsMu_dvd (kills_inv hθN) (dvd_mul_right N l)) (killsMu_dvd (kills_inv hχ) (dvd_mul_left l N))
  obtain ⟨g, hg⟩ := hT l Ω ι e W hl2 he h (N * l) φ hNl hφ
  have hVc : Continuous (tw W φ) := tw_cont h.cont (cont_of_kills hNl hφ)
  have hVi : IsIrr (tw W φ) := irr_tw W φ _ h.irr
  have hVa : ∃ M : ℕ, 1 ≤ M ∧ LevelAway l M (tw W φ) := by
    obtain ⟨M, hM, hlev⟩ := h.away
    refine ⟨M * (N * l), Nat.mul_pos hM hNl, fun w hw => ?_⟩
    obtain ⟨B, hB, ψ, hψ, hd⟩ := hlev w hw
    exact ⟨B, hB, fun i => ψ i * φ, fun i => killsMu_mul (killsMu_dvd (hψ i) (dvd_mul_right _ _))
      (killsMu_dvd hφ (dvd_mul_left _ _)), diag_twist φ hd⟩
  have hVd : ∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt (tw W φ)) := by
    refine ⟨N * l, hNl, ?_⟩
    rw [dt_tw, pow_two]
    exact killsMu_mul (killsMu_mul hφ hφ) (killsMu_dvd hθN (dvd_mul_right N l))
  have hVf := flag_twist φ hfl
  have hVk : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (e : ℤ) ∧
      (κ 1 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (-(e : ℤ)) := by
    intro s hs
    have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
    obtain ⟨h0, h1'⟩ := hk s hs
    simp only [hφdef, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, Subgroup.coe_subtype, h1, inv_one,
      one_mul, h0, h1', mul_inv_cancel_right, and_self]
  obtain ⟨π, hreg, hatt, hsat⟩ := _root_.GlobalTheory.Ord2.SrcForm.exists_rep_alt P.toClassicalTheorems (by omega) g ι (tw W φ) (-(e : ℤ)) hg
  obtain ⟨v, hv, hlv⟩ := id hA
  have hnv : normV v = l := normV_of_mem hl.out hlv
  obtain ⟨Bs, hBs⟩ := hS (N * l) φ hNl hφ A v _ hv hlv hVf hVk π hreg hatt
  have hlev : ¬ l ∣ g.M := hnv ▸ _root_.GlobalTheory.NewLevel.not_dvd_level_of_satake_hecke_poly_cofinite P.toClassicalTheorems P.ssR _ (by omega) g _ π hsat v Bs hBs
  obtain ⟨σ, hσ⟩ := exists_isFrob (Ω := Ω) hv
  rw [hnv] at hσ
  obtain ⟨α, hroot, hα⟩ := hF l Ω ι e (tw W φ) A _ g hl2 he hVc hVi hVd hA ⟨hVf, hVk⟩ hg hlev ⟨σ, hσ.1⟩ hσ
  set u : (Qbar l)ˣ := (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) ⟨σ, hσ.1⟩ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) with hu
  have hun : ‖(u : Qbar l)‖ = 1 := by
    rw [hu, Units.val_mul, norm_mul, norm_flag hVc hVf 0, Units.val_zpow_eq_zpow_val, norm_zpow, norm_cyc, one_zpow, one_mul]
  have hα' : α = ι (u : Qbar l) ∨ α = (ι (u : Qbar l))⁻¹ := hα.imp id fun h => by rw [← h, inv_inv]
  have hαn : ‖ι.symm α‖ = 1 := by
    rcases hα' with h1 | h1
    · rw [h1, RingEquiv.symm_apply_apply, hun]
    · rw [h1, map_inv₀, RingEquiv.symm_apply_apply, norm_inv, hun, inv_one]
  obtain ⟨hal, hpow⟩ := GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight l ι e g α hl2 he hlev hroot hαn
  refine ⟨⟨g, χ⁻¹, A, κ, hlev, hal, kills_inv hχ, ?_, hA, hfl, fun s hs => ?_⟩, fun A' κ' hA' hfl' => ?_⟩
  · rw [tw_tw] at hg
    rw [mul_assoc]
    exact hg
  · have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
    have h2 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ≠ 0 := Units.ne_zero _
    have h3 : (χ (s : G ℚ Ω) : Qbar l) ≠ 0 := Units.ne_zero _
    have h4 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ^ (e : ℤ) ≠ 0 := zpow_ne_zero _ h2
    rw [(hk s hs).2, h1, MonoidHom.inv_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
      Units.val_one, inv_one, one_mul, zpow_neg]
    field_simp
  · by_contra hn
    push Not at hn
    obtain ⟨m, hm, hχm⟩ := pow_eq_one_of_kills hl0 hχ
    obtain ⟨t, ht, htk⟩ := cyc_inf hA
    obtain ⟨h0, h1⟩ := hk ⟨t, Ine_le_Dec A ht⟩ ht
    rcases eps_mem hA hA' hfl hfl' hn with hc | hc
    · rw [← hc] at h0
      simp only at h0
      have he1 : e = 1 := by
        by_contra hne
        obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
        refine htk (d * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
        have h2 : cycBar ℚ Ω l t ^ d * χ t = 1 := by
          rw [zpow_natCast, pow_succ', mul_assoc] at h0
          exact (left_eq_mul.1 h0)
        rw [pow_mul, eq_inv_of_mul_eq_one_left h2, inv_pow, hχm, inv_one]
      obtain ⟨m', hm', hφm⟩ := pow_eq_one_of_kills hNl hφ
      have hu' : u = φ σ := by
        rw [hu, MonoidHom.mul_apply, ← hc, he1]
        simp [mul_inv_cancel_comm]
      have hu1 : ι (u : Qbar l) ^ m' = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hu', hφm, Units.val_one, map_one]
      refine hpow m' hm' ?_
      rcases hα' with h1 | h1
      · rw [h1, hu1]
      · rw [h1, inv_pow, hu1, inv_one]
    · rw [← hc] at h1
      simp only at h1
      refine htk ((e + 1) * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
      have h2 : cycBar ℚ Ω l t ^ (e + 1) = χ t := by
        rw [pow_succ]
        nth_rewrite 2 [h1]
        rw [zpow_neg, zpow_natCast, mul_inv_cancel_left]
      rw [pow_mul, h2, hχm]
end GlobalTheory.Ord2
end
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.srcS_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → GlobalTheory.Ord2.TwNewQ → FrobRoot → SrcS :=
  fun P hT hF l _ Ω _ _ _ ι e W hl he hW hS => GlobalTheory.Ord2.sources_of_spherical P hT hF l Ω ι e W hl he hW hS
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open IsDedekindDomain UpperTheory.V.Af in
theorem UpperTheory.GalN.V.csdOf0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (F₀ F Ω : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω]
    [Algebra F Ω] [IsScalarTower F₀ F Ω] [IsAlgClosure F Ω], IsTotallyReal F₀ → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ),
    1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (c : G F₀ Ω) (P : GL (Fin n) (Qbar l)), IsConjEl c → IsAut ι r →
      IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ))) P → AutCsd0 ι r := by
  intro hP F₀ F Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn r c P hc haut hpair
  obtain ⟨π, hreg, hatt⟩ := ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP F Ω l ι n r).2.1).1 haut
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  obtain ⟨art, hart⟩ : ∃ art : Neutral.B1.Ideles (maximalRealSubfield F) →* Gab (maximalRealSubfield F) Ω,
      IsGlobalArtin art := hP.toClassicalTheorems.litN.aut.art _ Ω
  have h1 : IsLAdicCharOf (E := F) (Ω := Ω) ι 1 1 := by
    refine ⟨continuous_const, art, 0, hart, fun k _ => ?_, fun x σ _ => ?_⟩
    · simp [HChar.inf]
    · rw [infPow_zero, lPow_zero]
      change (1 : Qbar l) = ι.symm (1 * 1⁻¹) * 1
      simp
  obtain ⟨j, hj⟩ := hc
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hd := _root_.UpperTheory.V.Af.self_dual_complex_of_printed_hida hP F Ω l ι n hn r π hatt 1 1 h1 c' P ⟨j, hj⟩ (by
    intro s s' hs
    rw [MonoidHom.one_comp, mul_one]
    refine hpair s s' (AlgEquiv.ext fun x => ?_)
    exact DFunLike.congr_fun hs x)
  rw [map_one, GlobalTheory.ContraPair.dualIsConjBy_one] at hd
  exact ⟨π, hreg, hd, hatt⟩
end
end

