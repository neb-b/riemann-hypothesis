module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftLowerBoundOffBasePlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDiagonalIntegralMemSchwartzBruhat
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DiagWSB

variable {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {κ : Type} [Fintype κ]

def diagG (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ℂ :=
  ∫ x, ψ (x ⬝ᵥ w.2) * Φ (Sum.elim (x + w.1) x) ∂μ

omit [Fintype κ] in
theorem elim_add_elim {R : Type} [AddCommGroup R] (a b c d : κ → R) :
    Sum.elim a b + Sum.elim c d = Sum.elim (a + c) (b + d) := by
  funext i; rcases i with i | i <;> rfl

theorem elim_dot_elim {R : Type} [CommRing R] (a b c d : κ → R) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem diagW_eq (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    diagW ψ μ Φ w = ψ (⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagG ψ μ Φ w := by
  unfold diagW diagG
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [schr, elim_add_elim, AddChar.map_add_eq_mul, mul_comm, mul_left_comm, mul_assoc]

omit [Fintype κ] in
theorem continuous_elim_add (a : κ → Fv F v) : Continuous fun x : κ → Fv F v => Sum.elim (x + a) x :=
  continuous_pi fun i => by rcases i with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem integrable_integrand (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (Φ : (κ ⊕ κ → Fv F v) → ℂ) (hΦ : Φ ∈ SB (κ ⊕ κ → Fv F v))
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    Integrable (fun x => ψ (x ⬝ᵥ w.2) * Φ (Sum.elim (x + w.1) x)) μ := by
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have _ : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have _ := hμ
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hψ.comp (continuous_id.dotProduct continuous_const)).mul
      (hΦ.1.continuous.comp (continuous_elim_add w.1))
  · apply HasCompactSupport.mul_left
    refine HasCompactSupport.intro (K := (fun y : κ ⊕ κ → Fv F v => y ∘ Sum.inr) '' tsupport Φ)
      (hΦ.2.image (by fun_prop)) ?_
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx ⟨_, h, rfl⟩

theorem diagG_zero (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) :
    diagG ψ μ (0 : (κ ⊕ κ → Fv F v) → ℂ) = 0 := by
  funext w; simp [diagG]

theorem diagG_add (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ Ψ : (κ ⊕ κ → Fv F v) → ℂ} (hΦ : Φ ∈ SB (κ ⊕ κ → Fv F v))
    (hΨ : Ψ ∈ SB (κ ⊕ κ → Fv F v)) : diagG ψ μ (Φ + Ψ) = diagG ψ μ Φ + diagG ψ μ Ψ := by
  funext w
  simp only [diagG, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand ψ hψ μ hμ Φ hΦ w) (integrable_integrand ψ hψ μ hμ Ψ hΨ w)

theorem diagG_smul (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (a : ℂ)
    (Φ : (κ ⊕ κ → Fv F v) → ℂ) : diagG ψ μ (a • Φ) = a • diagG ψ μ Φ := by
  funext w
  simp only [diagG, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext x; ring

theorem diagG_schr (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (Φ : (κ ⊕ κ → Fv F v) → ℂ) (p₁ p₂ q₁ q₂ : κ → Fv F v)
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    diagG ψ μ (schr ψ (Sum.elim p₁ p₂, Sum.elim q₁ q₂) Φ) w =
      ψ (-(p₂ ⬝ᵥ w.2) + (w.1 - p₂) ⬝ᵥ q₁ - p₂ ⬝ᵥ q₂ + ⅟(2 : Fv F v) * (p₁ ⬝ᵥ q₁ + p₂ ⬝ᵥ q₂)) *
        diagG ψ μ Φ (w + (p₁ - p₂, q₁ + q₂)) := by
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have _ : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have _ := hμ
  unfold diagG
  rw [← integral_sub_right_eq_self _ p₂, ← integral_const_mul]
  congr 1
  funext x
  simp only [schr, elim_dot_elim, elim_add_elim, Prod.fst_add, Prod.snd_add, Prod.fst, Prod.snd]
  have e : Sum.elim (x - p₂ + w.1 + p₁) (x - p₂ + p₂) = Sum.elim (x + (w.1 + (p₁ - p₂))) x := by
    congr 1 <;> abel
  rw [e, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

theorem sb_mul {X : Type} [TopologicalSpace X] {f g : X → ℂ} (hf : IsLocallyConstant f) (hg : g ∈ SB X) :
    (fun w => f w * g w) ∈ SB X :=
  ⟨hf.mul hg.1, hg.2.mul_left⟩

theorem sb_mul_translate {X : Type} [TopologicalSpace X] [AddGroup X] [ContinuousAdd X] {f g : X → ℂ}
    (hf : IsLocallyConstant f) (hg : g ∈ SB X) (t : X) : (fun w => f w * g (w + t)) ∈ SB X :=
  ⟨hf.mul (hg.1.comp_continuous (continuous_id.add continuous_const)), (hg.2.comp_homeomorph (Homeomorph.addRight t)).mul_left⟩

omit [Fintype κ] in
theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) (c : ℂ) :
    IsLocallyConstant (S.indicator fun _ => c) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ S
  · exact ⟨S, hS.isOpen, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Sᶜ, hS.compl.isOpen, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem diagW_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ₀ ∈ SB (κ ⊕ κ → Fv F v), ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U →
      0 ∈ U → (∀ w, diagW ψ μ Φ₀ w = U.indicator (fun _ => c) w) →
    ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
  intro F _ _ v κ _ ψ hψ h1 μ hμ Φ₀ hΦ₀ c hc U hUo hUc h0U hU Φ hΦ
  have _ := GlobalTheory.WeilM.nonarch_field (Fv F v)
  have hlc := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ

  have hph : ∀ a : Fv F v, IsLocallyConstant fun w : (κ → Fv F v) × (κ → Fv F v) => ψ (a * (w.1 ⬝ᵥ w.2)) :=
    fun a => hlc.comp_continuous (continuous_const.mul (continuous_fst.dotProduct continuous_snd))
  let N : Submodule ℂ ((κ ⊕ κ → Fv F v) → ℂ) :=
    { carrier := {Φ | Φ ∈ SB (κ ⊕ κ → Fv F v) ∧ diagG ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))}
      zero_mem' := ⟨zero_mem _, by rw [diagG_zero]; exact zero_mem _⟩
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by
        rw [diagG_add ψ hψ μ hμ ha.1 hb.1]; exact add_mem ha.2 hb.2⟩
      smul_mem' := fun a Φ h => ⟨Submodule.smul_mem _ a h.1, by
        rw [diagG_smul]; exact Submodule.smul_mem _ a h.2⟩ }
  have hNle : N ≤ SB (κ ⊕ κ → Fv F v) := fun Φ h => h.1
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    rintro ⟨P, Q⟩ φ ⟨hφ1, hφ2⟩
    refine ⟨GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (P, Q) φ hφ1, ?_⟩
    rw [← Sum.elim_comp_inl_inr P, ← Sum.elim_comp_inl_inr Q]
    have e : diagG ψ μ (schr ψ (Sum.elim (P ∘ Sum.inl) (P ∘ Sum.inr), Sum.elim (Q ∘ Sum.inl) (Q ∘ Sum.inr)) φ) =
        fun w => ψ (-((P ∘ Sum.inr) ⬝ᵥ w.2) + (w.1 - P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inl) - (P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inr) +
          ⅟(2 : Fv F v) * ((P ∘ Sum.inl) ⬝ᵥ (Q ∘ Sum.inl) + (P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inr))) *
          diagG ψ μ φ (w + (P ∘ Sum.inl - P ∘ Sum.inr, Q ∘ Sum.inl + Q ∘ Sum.inr)) :=
      funext fun w => diagG_schr ψ μ hμ φ _ _ _ _ w
    rw [e]
    refine sb_mul_translate (hlc.comp_continuous ?_) hφ2 _
    fun_prop

  have hUcl : IsClopen U := ⟨hUc.isClosed, hUo⟩
  have hW₀ : diagW ψ μ Φ₀ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
    rw [show diagW ψ μ Φ₀ = U.indicator (fun _ => c) from funext hU]
    exact ⟨isLocallyConstant_indicator hUcl c,
      HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
  have hG : ∀ Φ : (κ ⊕ κ → Fv F v) → ℂ, diagG ψ μ Φ =
      fun w => ψ (-⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagW ψ μ Φ w := by
    intro Φ
    funext w
    rw [diagW_eq, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have h0N : Φ₀ ∈ N := ⟨hΦ₀, by rw [hG]; exact sb_mul (hph _) hW₀⟩
  have hne : Φ₀ ≠ 0 := by
    rintro rfl
    have h := hU 0
    rw [Set.indicator_of_mem h0U, diagW_zero] at h
    simp at h
    exact hc h.symm
  have hN := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hNle hS Φ₀ h0N hne
  have hΦN : Φ ∈ N := hN ▸ hΦ
  rw [show diagW ψ μ Φ = fun w => ψ (⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagG ψ μ Φ w from funext (diagW_eq ψ μ Φ)]
  exact sb_mul (hph _) hΦN.2

end GlobalTheory.DiagWSB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.InductLagr

theorem schr_add_mem {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (N : Submodule ℂ ((κ → K) → ℂ)) (a b : (κ → K) × (κ → K))
    (ha : ∀ φ ∈ N, GlobalTheory.WeilM.schr ψ a φ ∈ N) (hb : ∀ φ ∈ N, GlobalTheory.WeilM.schr ψ b φ ∈ N) :
    ∀ φ ∈ N, GlobalTheory.WeilM.schr ψ (a + b) φ ∈ N := by
  intro φ hφ
  set c : K := ⅟(2 : K) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) with hc
  have law : GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ b φ) = ψ c • GlobalTheory.WeilM.schr ψ (a + b) φ := by
    funext x
    have key : (x ⬝ᵥ a.2 + ⅟(2 : K) * (a.1 ⬝ᵥ a.2)) + ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : K) * (b.1 ⬝ᵥ b.2)) =
        c + (x ⬝ᵥ (a + b).2 + ⅟(2 : K) * ((a + b).1 ⬝ᵥ (a + b).2)) := by
      have h2 : ⅟(2 : K) * 2 = 1 := invOf_mul_self 2
      simp only [hc, Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
      linear_combination (-(a.1 ⬝ᵥ b.2)) * h2
    show ψ _ * (ψ _ * φ (x + a.1 + b.1)) = ψ c * (ψ _ * φ (x + (a + b).1))
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, Prod.fst_add, add_assoc]
  have hne : ψ c ≠ 0 := by
    have h1 : ψ c * ψ (-c) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one h1
  have e : GlobalTheory.WeilM.schr ψ (a + b) φ = (ψ c)⁻¹ • GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ b φ) := by
    rw [law, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [e]
  exact N.smul_mem _ (ha _ (hb _ hφ))

theorem exists_at_locCo {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (p : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = p := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)), ?_, ?_⟩
  · intro r hr
    rw [← LinearEquiv.map_smul]
    have h0 : r • ((fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)) :
        (κ → AF F) × (κ → AF F)) = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact GlobalTheory.LatVac.at_liftV v (p.1 k) r hr
      · exact GlobalTheory.LatVac.at_liftV v (p.2 k) r hr
    rw [h0, map_zero]
  · show ((fun k => evFin F v ((co.e _).1 k)), fun k => evFin F v ((co.e _).2 k)) = p
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (funext fun k => GlobalTheory.LatVac.evFin_liftV v _) (funext fun k => GlobalTheory.LatVac.evFin_liftV v _)

end GlobalTheory.InductLagr

namespace GlobalTheory.InductLagr

theorem rel_of_vac : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ →
    ∀ {ι : Type} (P : Finset ι) (pl : ι → HeightOneSpectrum (𝓞 F)), Set.InjOn pl P →
    ∀ (Z : ι → Type) [∀ w, TopologicalSpace (Z w)] [∀ w, Add (Z w)]
      (A A' : ι → Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
      (co : ∀ w, Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z w)
      (I : ∀ w, ((Fin n × Fin d → Fv F (pl w)) → ℂ) →ₗ[ℂ] (Z w → ℂ))
      (H : AddSubgroup (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
      (R : Submodule ℂ ((Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ) × ((Fin n × Fin d → AF F) → ℂ)))
      (f : SInf F (Fin n × Fin d)),
    (∀ w ∈ P, IsLagrModel M ψ (pl w) (A w) (A' w) (co w) (I w)) →
    (∀ w ∈ P, ∀ u ∈ A w, At (evFin F (pl w)) u ∧ u ∈ H) → (∀ w ∈ P, ∀ u ∈ A' w, At (evFin F (pl w)) u) →
    (∀ w ∈ P, ∀ u, At (evFin F (pl w)) u → ∃ x ∈ A w, ∃ y ∈ A' w, u = x + y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ u, co w (u + x) = co w u + co w x) →
    (∀ w ∈ P, ∀ w' ∈ P, w' ≠ w → ∀ x ∈ A w, ∀ u, co w' (u + x) = co w' u) →
    (∀ w ∈ P, ∀ u, ∃ x ∈ A w, co w x = co w u ∧ ∀ y ∈ A' w,
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y =
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ p ∈ R, (fun u => p.1 (u + x), M.co.rho ψ x p.2) ∈ R) →
    (∀ w ∈ P, ∀ y ∈ A' w, ∀ p ∈ R, (fun u => ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y) * p.1 u, M.co.rho ψ y p.2) ∈ R) →
    (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (M.vac (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) ∈ R →
    ∀ φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ v, (∀ w ∈ P, pl w ≠ v) → φ v = M.vac v) →
      (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (φ (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ R := by
  intro F E _ _ _ _ _ σ n d X Y M ψ hstd hM ι P pl hpl Z _ _ A A' co I H R f hL hA hA' hdec hadd hloc hrep hRA hRA' hvac
  classical
  suffices key : ∀ S : Finset ι, S ⊆ P → ∀ φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, (∀ w ∈ S, pl w ≠ v) → φ v = M.vac v) →
      (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (φ (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ R by
    intro φ h1 h2
    exact key P subset_rfl φ h1 h2
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ φ _ h2
    have e : φ = M.vac := funext fun v => h2 v (by simp)
    subst e
    exact hvac
  | insert w S hwS ih =>
    intro hsub φ hφ1 hφ2
    have hwP : w ∈ P := hsub (Finset.mem_insert_self _ _)
    have hSP : S ⊆ P := (Finset.subset_insert _ _).trans hsub
    have hfam : GlobalTheory.BigNZ.Fam M φ := by
      refine ⟨hφ1, Filter.eventually_cofinite.2 (((insert w S).image pl).finite_toSet.subset fun v hv => ?_)⟩
      by_contra hc
      exact hv (hφ2 v fun w' hw' e => hc (Finset.mem_coe.2 (Finset.mem_image.2 ⟨w', hw', e⟩)))
    obtain ⟨r, -, er⟩ := GlobalTheory.PureFactor.exists_rest_factor (pl w) f φ (hfam.std hM)

    let C : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ := fun u => ∏ w' ∈ P.erase w, I w' (φ (pl w')) (co w' u)
    have hne : ∀ w' ∈ P.erase w, pl w' ≠ pl w := fun w' hw' e =>
      (Finset.mem_erase.1 hw').1 (hpl (Finset.mem_erase.1 hw').2 hwP e)
    have hprod : ∀ (χ : (Fin n × Fin d → Fv F (pl w)) → ℂ) u,
        ∏ w' ∈ P, I w' (Function.update φ (pl w) χ (pl w')) (co w' u) = I w χ (co w u) * C u := by
      intro χ u
      rw [← Finset.mul_prod_erase P _ hwP, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (hne w' hw')]

    let L : ((Fin n × Fin d → Fv F (pl w)) → ℂ) →ₗ[ℂ]
        ((Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ) × ((Fin n × Fin d → AF F) → ℂ)) :=
      { toFun := fun χ => (Set.indicator (H : Set _) fun u => I w χ (co w u) * C u,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) χ r)
        map_add' := fun a b => Prod.ext (funext fun u => by
            by_cases hu : u ∈ (H : Set _)
            · simp only [Set.indicator_of_mem hu, map_add (f := _), Pi.add_apply, Prod.fst_add, add_mul]
            · simp only [Set.indicator_of_notMem hu, Prod.fst_add, Pi.add_apply, add_zero])
          (funext fun _ => add_mul _ _ _)
        map_smul' := fun c a => Prod.ext (funext fun u => by
            by_cases hu : u ∈ (H : Set _)
            · simp only [Set.indicator_of_mem hu, map_smul, Pi.smul_apply, Prod.smul_fst, smul_eq_mul,
                RingHom.id_apply, mul_assoc]
            · simp only [Set.indicator_of_notMem hu, Prod.smul_fst, Pi.smul_apply, smul_zero, RingHom.id_apply])
          (funext fun _ => mul_assoc _ _ _) }
    have hLe : ∀ χ, (Set.indicator (H : Set _) fun u => ∏ w' ∈ P, I w' (Function.update φ (pl w) χ (pl w')) (co w' u),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ (pl w) χ)) = L χ := fun χ =>
      Prod.ext (by simp only [hprod]; rfl) (er χ).symm
    let N : Submodule ℂ ((Fin n × Fin d → Fv F (pl w)) → ℂ) := GlobalTheory.WeilM.SB _ ⊓ R.comap L

    have hvacN : M.vac (pl w) ∈ N := by
      refine ⟨(hM.vac _).1, ?_⟩
      show L _ ∈ R
      rw [← hLe]
      refine ih hSP _ (fun v => ?_) (fun v hv => ?_)
      · by_cases e : v = pl w
        · subst e; rw [Function.update_self]; exact (hM.vac _).1
        · rw [Function.update_of_ne e]; exact hφ1 v
      · by_cases e : v = pl w
        · subst e; rw [Function.update_self]
        · rw [Function.update_of_ne e]
          refine hφ2 v fun w' hw' => ?_
          rcases Finset.mem_insert.1 hw' with h | h
          · subst h; exact fun e' => e e'.symm
          · exact hv w' h

    have hstA : ∀ x ∈ A w, ∀ χ ∈ N,
        GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ (pl w)) (GlobalTheory.LatVac.locCo M.co (pl w) x) χ ∈ N := by
      intro x hx χ hχ
      obtain ⟨hxat, hxH⟩ := hA w hwP x hx
      have hsb := GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 (pl w) (GlobalTheory.LatVac.locCo M.co (pl w) x) χ hχ.1
      have hact := GlobalTheory.VacBridge.rho_acts_locCo M.co ψ (pl w) x hxat χ
      refine ⟨hsb, ?_⟩
      show L _ ∈ R
      have hR := hRA w hwP x hx (L χ) hχ.2
      convert hR using 1
      refine Prod.ext (funext fun u => ?_) ?_
      · show Set.indicator (H : Set _) (fun u => I w _ (co w u) * C u) u =
          Set.indicator (H : Set _) (fun u => I w χ (co w u) * C u) (u + x)
        have hC : C (u + x) = C u := Finset.prod_congr rfl fun w' hw' => by
          rw [hloc w hwP w' (Finset.mem_of_mem_erase hw') (Finset.ne_of_mem_erase hw') x hx u]
        by_cases hu : u ∈ (H : Set _)
        · have hu' : u + x ∈ (H : Set _) := H.add_mem hu hxH
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu', hC, hadd w hwP x hx u,
            (hL w hwP).2.1 x hx χ hχ.1 _ hsb hact (co w u)]
        · have hu' : u + x ∉ (H : Set _) := fun h => hu (by simpa using H.sub_mem h hxH)
          rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']
      · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) _ r = M.co.rho ψ x (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) χ r)
        rw [er, er, GlobalTheory.BigNZ.Fam.acts hM hfam f hχ.1 hact]

    have hstA' : ∀ y ∈ A' w, ∀ χ ∈ N,
        GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ (pl w)) (GlobalTheory.LatVac.locCo M.co (pl w) y) χ ∈ N := by
      intro y hy χ hχ
      have hyat := hA' w hwP y hy
      have hsb := GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 (pl w) (GlobalTheory.LatVac.locCo M.co (pl w) y) χ hχ.1
      have hact := GlobalTheory.VacBridge.rho_acts_locCo M.co ψ (pl w) y hyat χ
      refine ⟨hsb, ?_⟩
      show L _ ∈ R
      have hR := hRA' w hwP y hy (L χ) hχ.2
      convert hR using 1
      refine Prod.ext (funext fun u => ?_) ?_
      · show Set.indicator (H : Set _) (fun u => I w _ (co w u) * C u) u =
          ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y) *
            Set.indicator (H : Set _) (fun u => I w χ (co w u) * C u) u
        by_cases hu : u ∈ (H : Set _)
        · obtain ⟨x, hx, hcx, hsx⟩ := hrep w hwP u
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← hcx,
            (hL w hwP).2.2 y hy χ hχ.1 _ hsb hact x hx, hsx y hy, mul_assoc]
        · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
      · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) _ r = M.co.rho ψ y (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) χ r)
        rw [er, er, GlobalTheory.BigNZ.Fam.acts hM hfam f hχ.1 hact]

    have hst : ∀ p, ∀ χ ∈ N, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ (pl w)) p χ ∈ N := by
      intro p χ hχ
      obtain ⟨u, hu, rfl⟩ := exists_at_locCo M.co (pl w) p
      obtain ⟨x, hx, y, hy, rfl⟩ := hdec w hwP u hu
      rw [map_add (f := _)]
      exact schr_add_mem _ N _ _ (hstA x hx) (hstA' y hy) χ hχ
    have hN : N = GlobalTheory.WeilM.SB _ :=
      _root_.GlobalTheory.SchrIrred.schr_irreducible (pl w) (GlobalTheory.LatVac.psiAt ψ (pl w)) (GlobalTheory.SchrSB.continuous_psiAt ψ hstd.1 _)
        (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hstd _) N inf_le_left hst (M.vac (pl w)) hvacN (hM.vac _).2.1
    have hmem : φ (pl w) ∈ N := hN ▸ hφ1 (pl w)
    have h2 : L (φ (pl w)) ∈ R := hmem.2
    rw [← hLe, Function.update_eq_self] at h2
    exact h2

end GlobalTheory.InductLagr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralAbsNormPowMulOnId
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.TameHeckeIntegral

open Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_onId (E : Type) [Field E] [NumberField E] (ψ : HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ)
    (n : I → ℤ) (hinf : ψ.HasInf φs n) (ht : ∀ v, ψ.TameAt v) (b : ℕ) (hb : b ≠ 0)
    (hu : ∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) (cc : Ideal (𝓞 E)) (hcc : cc ≠ ⊥)
    (hcop : cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤) :
    UnitOff (Ideal.absNorm cc) ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ) := by
  classical
  have hb0 : (b : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hb
  have hfin : {w | ¬ ψ.UnrAt w}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(b : 𝓞 E)}) (by simpa using hb0)).subset fun w hw => ?_
    have hbw : (b : 𝓞 E) ∈ w.asIdeal := by
      by_contra h
      exact hw (hu w h)
    show w.asIdeal ∣ Ideal.span {(b : 𝓞 E)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hbw
  have hcc0 : cc ≠ 0 := hcc
  unfold HChar.onId
  refine finprod_induction (fun u : ℂˣ => UnitOff (Ideal.absNorm cc) (u : ℂ)) (by simpa using unitOff_one _)
    (fun x y hx hy => by simpa [Units.val_mul] using unitOff_mul hx hy) fun v => ?_
  show UnitOff _ (((ψ.val v ^ FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ)) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]
  by_cases hdv : v.asIdeal ∣ cc
  · have hle : cc ≤ v.asIdeal := Ideal.le_of_dvd hdv
    have hbv : (b : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top (by
      rw [eq_top_iff, ← hcop]
      exact sup_le hle (by rw [Ideal.span_singleton_le_iff_mem]; exact h))
    have hq : ((Ideal.absNorm cc : ℕ) : 𝓞 E) ∈ v.asIdeal := hle (Ideal.absNorm_mem cc)
    exact unitOff_zpow (GlobalTheory.ValUnit.unitOff_val E ψ I φs n v _ hinf hfin ht (hu v hbv) hq) _
  · have h0 : FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0 := by
      rw [FractionalIdeal.count_coe E v hcc0, Nat.cast_eq_zero]
      by_contra h
      exact hdv ((Associates.count_ne_zero_iff_dvd hcc0 (HeightOneSpectrum.prime v).irreducible).1 h)
    rw [h0, zpow_zero]
    exact unitOff_one _

theorem isIntegral_absNorm_pow_mul_onId : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  intro E _ _ ψ I _ φs n hinf ht b hb hu cc hcc hcop
  obtain ⟨_, K, hK, _⟩ := unitOff_onId E ψ I φs n hinf ht b hb hu cc hcc hcop
  exact ⟨K, hK⟩

end GlobalTheory.TameHeckeIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftLowerBoundOffBasePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLift_lowerBound_off_basePlace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ), AdelC R F → (∀ i, GalOut R i 1) → GlobalTheory.Hk3.Core R F → A.fam.Ok s → (∀ i σ, ∃ v : (R.MW i σ).Vec, IsExtVec (R.MW i σ) v) → R.LUnif → GlobalTheory.BigOn.BaseLinks R F → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowForm R F b := by
  first | exact @GlobalTheory.LowForm.lowForm_six | exact GlobalTheory.LowForm.lowForm_six | (intros; apply GlobalTheory.LowForm.lowForm_six <;> assumption)
end

