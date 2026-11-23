module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDiagonalIntegralExtendsLinearForm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.InertLagChar.LinForm

theorem hasCompactSupport_comp_of_leftInverse {X Y M : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [Zero M] {f : X → Y} {l : Y → X} (hl : Continuous l) (hlf : ∀ x, l (f x) = x) {g : Y → M}
    (hg : HasCompactSupport g) : HasCompactSupport (g ∘ f) := by
  refine IsCompact.of_isClosed_subset (hg.image hl) isClosed_closure ?_
  refine closure_minimal ?_ (hg.image hl).isClosed
  intro x hx
  exact ⟨f x, subset_tsupport _ hx, hlf x⟩

theorem integrable_of_cont_cs {X : Type} [TopologicalSpace X] (μ : @Measure X (borel X))
    [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f μ := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  exact hf.integrable_of_hasCompactSupport hcs

end GlobalTheory.InertLagChar.LinForm

open GlobalTheory.InertLagChar.LinForm in
theorem GlobalTheory.InertLagChar.lagInt_linForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  intro F _ _ v κ _ ψ hψ μ hμ N ν hν j hj hdiag

  have hd : Continuous (fun x : κ → Fv F v => (Sum.elim x x : κ ⊕ κ → Fv F v)) := by
    refine continuous_pi fun i => ?_
    cases i <;> exact continuous_apply _
  have hdl : Continuous (fun z : κ ⊕ κ → Fv F v => fun i => z (Sum.inl i)) :=
    continuous_pi fun i => continuous_apply _

  have hin : ∀ w : (κ → Fv F v) × (κ → Fv F v), ∀ Φ ∈ SB (κ ⊕ κ → Fv F v),
      Integrable (fun x => schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x)) μ := by
    intro w Φ hΦ
    have hs := GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ hΦ
    exact integrable_of_cont_cs μ (hs.1.continuous.comp hd)
      (hasCompactSupport_comp_of_leftInverse hdl (fun x => rfl) hs.2)
  have hschr_add : ∀ w (Φ Φ' : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (Φ + Φ') = schr ψ w Φ + schr ψ w Φ' := by
    intro w Φ Φ'; funext x; simp [schr, mul_add]
  have hschr_smul : ∀ w (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (c • Φ) = c • schr ψ w Φ := by
    intro w c Φ; funext x; simp [schr]; ring
  have hdiag_add : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), ∀ Φ' ∈ SB (κ ⊕ κ → Fv F v),
      diagW ψ μ (Φ + Φ') = diagW ψ μ Φ + diagW ψ μ Φ' := by
    intro Φ hΦ Φ' hΦ'
    funext w
    simp only [diagW, Pi.add_apply, hschr_add]
    exact integral_add (hin w Φ hΦ) (hin w Φ' hΦ')
  have hdiag_smul : ∀ (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), diagW ψ μ (c • Φ) = c • diagW ψ μ Φ := by
    intro c Φ
    funext w
    simp only [diagW, Pi.smul_apply, hschr_smul, smul_eq_mul]
    exact integral_const_mul (μ := μ) c _

  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hlc : Continuous l := IsModuleTopology.continuous_of_linearMap l
  have hlj : ∀ y, l (j y) = y := fun y => by
    have := LinearMap.congr_fun hl y
    simpa using this
  have hout : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Integrable (fun y => diagW ψ μ Φ (j y)) ν := by
    intro Φ hΦ
    have hs := hdiag Φ hΦ
    have hcs : HasCompactSupport (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hasCompactSupport_comp_of_leftInverse (f := (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v)))
        (l := (l : (κ → Fv F v) × (κ → Fv F v) → (Fin N → Fv F v))) hlc hlj hs.2
    have hc : Continuous (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hs.1.continuous.comp hjc
    exact integrable_of_cont_cs ν hc hcs
  let f : SB (κ ⊕ κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => lagInt ψ μ ν j Φ.1
      map_add' := by
        intro Φ Φ'
        simp only [Submodule.coe_add, lagInt, hdiag_add _ Φ.2 _ Φ'.2, Pi.add_apply]
        exact integral_add (hout _ Φ.2) (hout _ Φ'.2)
      map_smul' := by
        intro c Φ
        simp only [Submodule.coe_smul, lagInt, hdiag_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul (μ := ν) c _ }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  exact ⟨g, fun Φ hΦ => LinearMap.congr_fun hg ⟨Φ, hΦ⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistence
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

open MeasureTheory ComplexConjugate
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagLocForm

section
variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)}

theorem schr_adj (ψ₀ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ₀) {κ : Type} [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure]
    (w : (κ → Fv F v) × (κ → Fv F v)) (f g : (κ → Fv F v) → ℂ) :
    ∫ y, schr ψ₀ w f y * conj (g y) ∂μ = ∫ y, f y * conj (schr ψ₀ (-w) g y) ∂μ := by
  have h1 : ∀ s, conj (ψ₀ s) = ψ₀ (-s) := by
    intro s
    have h := GlobalTheory.norm_addChar_nonarch ψ₀ hψ s
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h]
    simp
  rw [← integral_add_right_eq_self (fun y => f y * conj (schr ψ₀ (-w) g y)) w.1]
  congr 1
  funext y
  have h2 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
  have e : -((y + w.1) ⬝ᵥ -w.2 + ⅟(2 : Fv F v) * (-w.1 ⬝ᵥ -w.2)) = y ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) := by
    simp only [add_dotProduct, dotProduct_neg, neg_dotProduct, neg_neg]
    linear_combination (-(w.1 ⬝ᵥ w.2)) * h2
  simp only [schr, Prod.fst_neg, Prod.snd_neg, map_mul, h1, add_neg_cancel_right]
  rw [e]; ring

theorem ip_self_ne {κ : Type} [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure] (g : (κ → Fv F v) → ℂ) (hg : g ∈ SB (κ → Fv F v))
    (h0 : g ≠ 0) : ∫ y, g y * conj (g y) ∂μ ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have e : (fun y => g y * conj (g y)) = fun y => ((Complex.normSq (g y) : ℝ) : ℂ) := by
    funext y; exact Complex.mul_conj (g y)
  rw [e, integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine ne_of_gt ?_
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (x := x)
    (Complex.continuous_normSq.comp hg.1.continuous) (hg.2.comp_left (g := Complex.normSq) (map_zero _))
    (fun y => Complex.normSq_nonneg _) ?_
  simpa using hx

end

theorem lagr_local_form : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  intro F _ _ v ψ₀ κ _ Λ Γ vac hψ hcond hiso hΓo hΓc hdual hvSB hv0 heig hfix
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  let μ : Measure (κ → Fv F v) := Measure.addHaar
  let c : ((κ → Fv F v) → ℂ) → ((κ → Fv F v) × (κ → Fv F v)) → ℂ :=
    fun φ w => ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ
  have hc : ∀ (φ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v)), c φ w = ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ := fun _ _ => rfl
  have schr_zero : ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ 0 φ = φ := by
    intro φ; funext x; simp [schr]
  have schr_add : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (φ₁ φ₂ : (κ → Fv F v) → ℂ), schr ψ₀ w (φ₁ + φ₂) = schr ψ₀ w φ₁ + schr ψ₀ w φ₂ := by
    intro w φ₁ φ₂; funext x; simp [schr, mul_add]
  have schr_smul : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (a : ℂ) (φ : (κ → Fv F v) → ℂ), schr ψ₀ w (a • φ) = a • schr ψ₀ w φ := by
    intro w a φ; funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  have comp_iso : ∀ w ∈ Λ, ∀ w' ∈ Λ, ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ w (schr ψ₀ w' φ) = schr ψ₀ (w + w') φ := by
    intro w hw w' hw' φ
    rw [GlobalTheory.ThetaQuasiRat.schr_schr, hiso w hw w' hw', mul_zero, AddChar.map_zero_eq_one, one_smul]

  have hconst : ∀ φ : (κ → Fv F v) → ℂ, ∀ l ∈ Λ, ∀ γ ∈ Γ, γ ∈ Λ → c φ (l + γ) = c φ l := by
    intro φ l hl γ hγ hγΛ
    rw [hc, hc, add_comm, ← comp_iso γ hγΛ l hl, schr_adj ψ₀ hψ μ γ (schr ψ₀ l φ) vac,
      hfix (-γ) (AddSubgroup.mem_inf.2 ⟨Γ.neg_mem hγ, Λ.neg_mem hγΛ⟩)]
  let H : AddSubgroup Λ := Γ.addSubgroupOf Λ
  let ct : ((κ → Fv F v) → ℂ) → Λ ⧸ H → ℂ := fun φ =>
    Quotient.lift (s := QuotientAddGroup.leftRel H) (fun l : Λ => c φ l) (by
      intro a b hab
      have hab : -a + b ∈ H := QuotientAddGroup.leftRel_apply.1 hab
      rw [AddSubgroup.mem_addSubgroupOf] at hab
      have e : (b : (κ → Fv F v) × (κ → Fv F v)) = a + ((-a + b : Λ) : (κ → Fv F v) × (κ → Fv F v)) := by
        simp
      show c φ a = c φ b
      rw [e, hconst φ a a.2 _ hab (-a + b).2])
  have hct : ∀ (φ : (κ → Fv F v) → ℂ) (l : Λ), ct φ (l : Λ ⧸ H) = c φ l := fun _ _ => rfl

  have hfin : ∀ φ ∈ SB (κ → Fv F v), (Function.support (ct φ)).Finite := by
    intro φ hφ
    obtain ⟨C, hCc, hC⟩ := GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace v ψ₀ κ μ hψ hcond φ hφ vac hvSB
    obtain ⟨t, ht⟩ := hCc.elim_finite_subcover (fun i : C => (fun z => z - (i : (κ → Fv F v) × (κ → Fv F v))) ⁻¹' Γ)
      (fun i => hΓo.preimage (continuous_sub_right _))
      (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, by simp [Set.mem_preimage, sub_self, zero_mem]⟩)
    refine Set.Finite.subset (t.finite_toSet.biUnion fun i _ =>
      (Set.Subsingleton.finite (s := (QuotientAddGroup.mk : Λ → Λ ⧸ H) ''
        {l : Λ | (l : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ}) ?_)) ?_
    · rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have := Γ.sub_mem (show (l₂ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₂)
        (show (l₁ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₁)
      simpa [sub_sub_sub_cancel_right, neg_add_eq_sub] using this
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H l =>
        rw [Function.mem_support, hct] at hq
        have hlC := hC _ hq
        obtain ⟨i, hi, hli⟩ := Set.mem_iUnion₂.1 (ht hlC)
        exact Set.mem_biUnion hi ⟨l, hli, rfl⟩
  have hint : ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v),
      Integrable (fun y => schr ψ₀ w φ y * conj (vac y)) μ := by
    intro w φ hφ
    have h1 := GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ
    exact (h1.1.continuous.mul (Complex.continuous_conj.comp hvSB.1.continuous)).integrable_of_hasCompactSupport
      (hvSB.2.comp_left (g := conj) (map_zero _)).mul_left
  have ct_add : ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), ct (φ₁ + φ₂) = ct φ₁ + ct φ₂ := by
    intro φ₁ h₁ φ₂ h₂
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.add_apply, hc, schr_add, add_mul]
      exact integral_add (hint _ _ h₁) (hint _ _ h₂)
  have ct_smul : ∀ (a : ℂ) (φ : (κ → Fv F v) → ℂ), ct (a • φ) = a • ct φ := by
    intro a φ
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.smul_apply, smul_eq_mul, hc, schr_smul, mul_assoc]
      exact integral_const_mul a _
  let l₀ : SB (κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∑ᶠ q, ct φ q
      map_add' := fun φ₁ φ₂ => by
        show ∑ᶠ q, ct ((φ₁ : (κ → Fv F v) → ℂ) + φ₂) q = ∑ᶠ q, ct φ₁ q + ∑ᶠ q, ct φ₂ q
        rw [ct_add _ φ₁.2 _ φ₂.2]
        exact finsum_add_distrib (hfin _ φ₁.2) (hfin _ φ₂.2)
      map_smul' := fun a φ => by
        show ∑ᶠ q, ct (a • (φ : (κ → Fv F v) → ℂ)) q = (RingHom.id ℂ) a • ∑ᶠ q, ct φ q
        rw [ct_smul, RingHom.id_apply, smul_eq_mul, mul_finsum]
        rfl }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  have hl' : ∀ φ (hφ : φ ∈ SB (κ → Fv F v)), l φ = ∑ᶠ q, ct φ q := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  refine ⟨l, fun w hw φ hφ => ?_, ?_⟩
  · rw [hl' _ (GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ), hl' φ hφ]
    have e : ct (schr ψ₀ w φ) = fun q => ct φ (q + ((⟨w, hw⟩ : Λ) : Λ ⧸ H)) := by
      funext q
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        rw [← QuotientAddGroup.mk_add, hct, hct, hc, hc, comp_iso m m.2 w hw]
        rfl
    rw [e]
    exact finsum_comp_equiv (Equiv.addRight _)
  · have hX0 : c vac 0 ≠ 0 := by
      rw [hc, schr_zero]; exact ip_self_ne μ vac hvSB hv0
    have hd : ∀ w, c vac w ≠ 0 → w ∈ Γ := by
      intro w hw
      rw [hdual]
      intro γ hγ
      obtain ⟨a, ha⟩ := heig γ hγ
      have hinv : a • schr ψ₀ (-γ) vac = vac := by
        rw [← schr_smul, ← ha, GlobalTheory.ThetaQuasiRat.schr_schr, neg_add_cancel, schr_zero]
        have : (-γ).1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ (-γ).2 = 0 := by
          simp only [Prod.fst_neg, Prod.snd_neg, neg_dotProduct, dotProduct_neg]; ring
        rw [this, mul_zero, AddChar.map_zero_eq_one, one_smul]
      have ha0 : a ≠ 0 := by
        rintro rfl; apply hv0; rw [← hinv, zero_smul]
      have hneg : schr ψ₀ (-γ) vac = a⁻¹ • vac := by
        rw [← hinv, smul_smul, inv_mul_cancel₀ ha0, one_smul, hinv]
      have key : ∀ w : (κ → Fv F v) × (κ → Fv F v),
          ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a * c vac w = conj a⁻¹ * c vac w := by
        intro w
        have e1 : schr ψ₀ γ (schr ψ₀ w vac) = (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) • schr ψ₀ w vac := by
          have h1 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ γ w vac
          have h2 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ w γ vac
          rw [ha, schr_smul, add_comm w γ] at h2
          rw [h1, mul_smul, h2, smul_smul, ← AddChar.map_add_eq_mul]
          have h3 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
          have e4 : ⅟(2 : Fv F v) * (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) =
              (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) := by
            linear_combination (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * h3
          rw [e4]
        have e3 : ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ =
            ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
          calc ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ
              = ∫ y, schr ψ₀ γ (schr ψ₀ w vac) y * conj (vac y) ∂μ := by
                congr 1; funext y; rw [e1, Pi.smul_apply, smul_eq_mul]; ring
            _ = ∫ y, schr ψ₀ w vac y * conj (schr ψ₀ (-γ) vac y) ∂μ := schr_adj ψ₀ hψ μ γ _ vac
            _ = ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
                congr 1; funext y; rw [hneg, Pi.smul_apply, smul_eq_mul, map_mul]; ring
        rw [integral_const_mul, integral_const_mul] at e3
        rw [hc]; exact e3
      have haa : a = conj a⁻¹ := by
        have k0 := key 0
        simp only [Prod.snd_zero, Prod.fst_zero, dotProduct_zero, zero_dotProduct, sub_zero,
          AddChar.map_zero_eq_one, one_mul] at k0
        exact mul_right_cancel₀ hX0 k0
      have hk := key w
      rw [← haa] at hk
      have hψω : ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) = 1 := by
        have := mul_right_cancel₀ hw hk
        exact mul_right_cancel₀ ha0 (by rw [this, one_mul])
      rw [show w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2 = -(γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) by ring, AddChar.map_neg_eq_inv, hψω, inv_one]
    rw [hl' vac hvSB, finsum_eq_single _ (0 : Λ ⧸ H)]
    · show ct vac ((0 : Λ) : Λ ⧸ H) ≠ 0
      rw [hct]; simpa using hX0
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        by_contra hm
        rw [hct] at hm
        exact hq ((QuotientAddGroup.eq_zero_iff m).2 (AddSubgroup.mem_addSubgroupOf.2 (hd m hm)))

end GlobalTheory.LagLocForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearHomKillsTorsionOfWeilPairingDivisible
section
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsKill

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O] (o : OAct O G) {T : Over S}

theorem comp_act_zero (x : T ⟶ G) : x ≫ o.act 0 = 1 := by
  have h : x ≫ o.act (0 + 0) = (x ≫ o.act 0) * (x ≫ o.act 0) := by rw [o.add, MonObj.comp_mul]
  rw [add_zero] at h
  exact mul_left_cancel (a := x ≫ o.act 0) (by rw [_root_.mul_one]; exact h.symm)

theorem comp_act_nat (x : T ⟶ G) (n : ℕ) : x ≫ o.act (n : O) = x ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, pow_zero, comp_act_zero]
  | succ n ih => rw [Nat.cast_succ, o.add, MonObj.comp_mul, ih, o.one, Category.comp_id, pow_succ]

theorem comp_act_nat_mul (x : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (r : O) : x ≫ o.act ((n : O) * r) = 1 := by
  have := o.hom r
  rw [o.mul, ← Category.assoc, comp_act_nat, hx, MonObj.one_comp]

end Act

theorem weilIs_one_left (hW : Out.WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}
    (k : ℕ) (y : T ⟶ P.A) (hy : y ^ k = 1) : Out.WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨e, he, hu⟩ := (hW S P k T).1 1 y (one_pow k) hy
  have h2 := (hW S P k T).2.1 1 1 y e e he he
  rw [_root_.one_mul] at h2
  have h3 : e * e = e := hu _ h2
  have he1 : e = 1 := mul_left_cancel (a := e) (by rw [_root_.mul_one]; exact h3)
  rwa [he1] at he

theorem kill : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (ψ : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act ψ → ∀ n : ℕ, 0 < n →
    (∀ f : (X.A true).t.G ⟶ X.B.t.G, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      ∃ r : 𝓞 E, GlobalTheory.CM.WeilEq X.B.t.PP.L f ψ (X.A true).t.PP.L ((X.A true).t.act.act ((n : 𝓞 E) * r)) (𝟙 _)
        (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) →
    ∀ u : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G, u ^ n = 1 → u ≫ ψ = 1 := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X ψ hψ n hn hWe u hu
  have laws := GlobalTheory.lawsFieldsSeparately
  have hWS : Out.WeilSt := laws.2.2.2.2.2.2.2.2.2.1
  have hND : Out.WeilNondegSt := laws.2.2.2.2.2.2.2.2.2.2.1
  have hBC : Out.PolBaseChangeSt := laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have u1 : unitOn (1 : ℂˣ) = 1 := map_one _

  have hgen : ∀ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G)
      (f : (X.A true).t.G ⟶ X.B.t.G), x ^ n = 1 → Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
      (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) →
      Out.WeilIs X.B.pol.A X.B.pol.L n (x ≫ f) (u ≫ ψ) 1 := by
    intro x f hx hf hm
    obtain ⟨r, hr⟩ := hWe f hf hm
    have h := (hr n x u 1 hn hx hu).2
    rw [u1] at h
    apply h
    rw [comp_act_nat_mul _ x n hx r, Category.comp_id]
    exact weilIs_one_left hWS (X.A true).pol n u hu
  have hall : ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
      Out.WeilIs X.B.pol.A X.B.pol.L n (u ≫ ψ) y 1 := by
    intro y hy
    have hψn : (u ≫ ψ) ^ n = 1 := GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu
    suffices h : Out.WeilIs X.B.pol.A X.B.pol.L n y (u ≫ ψ) 1 by
      have := GlobalTheory.CommPairing.weilIs_symm X.B.pol.isLB h
      rwa [inv_one] at this
    have hmem := _root_.GlobalTheory.FlatCM.TorsGen.gen E H hH K ρ σ₁ p X n hn y hy
    clear hy
    induction hmem using Submonoid.closure_induction with
    | mem w hw =>
      obtain ⟨x, f, hx, hf, hm, rfl⟩ := hw
      exact hgen x f hx hf hm
    | one => exact weilIs_one_left hWS X.B.pol n (u ≫ ψ) hψn
    | mul a b _ _ ha hb =>
      have := (hWS _ X.B.pol n _).2.1 a b (u ≫ ψ) 1 1 ha hb
      rwa [_root_.mul_one] at this
  exact GlobalTheory.LevelRigid.pairing_nondeg hWS hND hBC X.B.pol ℂ _ n (Nat.cast_ne_zero.2 hn.ne') (u ≫ ψ)
    (GlobalTheory.LevelRigid.pairing_tors u ψ hψ.isMonHom n hu) hall

end GlobalTheory.FlatCM.TorsKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqLatticeModelRepFundamentalDomain
section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatUnitF

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hS.2)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact GlobalTheory.SymplOInv.sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E))
    (JS.map (incAF F E)) (mtF σ JS g⁻¹) h1 h.2 (g⁻¹).2 x y

theorem gamFF_rhoFF (hS : IsHermND σ JS) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (p : GAF σ JS × GAF σ JT)
    (x y : XFF F E nS nT) :
    gamFF σ JS JT ξ₀ ψ (rhoFF σ JS JT p x) (rhoFF σ JS JT p y) = gamFF σ JS JT ξ₀ ψ x y := by
  unfold gamFF
  rw [coe_rhoFF, coe_rhoFF]
  unfold symplOF
  rw [hOF_actOF hS]

theorem sigma_sigma (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

theorem lintegral_sq_Om : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ hc Λ w lam Om h μ 𝓕 hμ h𝓕 p f
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hB.cm
  have hn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  obtain ⟨Bf, hB1, hB2⟩ := _root_.GlobalTheory.ThetaMeanSquareF.exists_invariant_form F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ
    (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) (fun _ hf => hf) μ 𝓕 hμ h𝓕
  rw [hB2, hB2, GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner (isHeis_opFF hσ hS hT hξ hc h.hw) (fun x y => hn _) lam h.good _ h.sd h.span
    (rhoFF σ JS JT p) (gamFF_rhoFF hS ξ₀ B.ψ p) (h.sd' p) (h.fin p) (Om p) (h.op p) (h.vac p) Bf]
  intro x u v
  have h1 : ∀ u : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, opFF hc w x u =
      phaseF σ JS JT ξ₀ B.ψ w x • (⟨heisOF σ JS JT ξ₀ B.ψ x u, hc x u u.2⟩ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) :=
    fun u => rfl
  have h2 : phaseF σ JS JT ξ₀ B.ψ w x * (starRingEnd ℂ) (phaseF σ JS JT ξ₀ B.ψ w x) = 1 := by
    rw [Complex.mul_conj', show ‖phaseF σ JS JT ξ₀ B.ψ w x‖ = 1 from hn _]; simp
  rw [h1, h1, Bf.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_smul, h2, one_smul]
  exact hB1 x u v _ _ rfl rfl

end GlobalTheory.FinLatUnitF

end
end

