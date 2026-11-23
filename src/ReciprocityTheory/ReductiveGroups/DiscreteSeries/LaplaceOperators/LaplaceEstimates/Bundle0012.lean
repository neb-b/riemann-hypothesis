module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirValueSubSingle
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K2Vd
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CapIdx
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PsiDatum
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Transport

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotM
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS TransportMapLinear

theorem quotM : QuotMStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp _ _ _ π μW μN
    P hP hB x₀ w ξ s x hx₀ hHC' hGap' hx hper
  classical
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hsg
  have hmin : 1 ≤ min (pOf ε) (qOf ε) := hq0
  have hp1 : 1 ≤ pOf ε := le_trans hmin (min_le_left _ _)
  have hq1 : 1 ≤ qOf ε := le_trans hmin (min_le_right _ _)
  have hGL : GapLap ε lam h := ⟨hHC.1, hGap, hNeed⟩
  have hstd : StdGap ε (lam - Pi.single s 1) :=
    ⟨hHC'.1, h, hGap', by linarith [LemK.three_add_le_gapBound_dual ε]⟩
  have hE := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hR := rreg_isURepOn ε
  have hDR := isDerivedOn_smE hR
  have hUR : IsInfUnitary ε (smE ε (rreg ε)) := Base.smInfUnitary _ ε (L2 ε) (rreg ε) hR
  set G : Submodule ℂ (Fin (2 * r + k + 1) → D) := Submodule.pi Set.univ (fun _ => genSub E V) with hGdef
  set X : Submodule ℂ (Fin (2 * r + k + 1) → D) := LemK.Xs (LemK.eeVd E) (genSub E V) (LemK.thVd lam s)
    with hXdef
  set L := tMapDL (D := D) σ (xJ P z) x₀ ((w : D) : H) with hLdef
  have hmemG : ∀ f, f ∈ G ↔ ∀ c, f c ∈ genSub E V := fun f => LemK.mem_pi_submodule_iff
  have hXG : X ≤ G := fun f hf => (hmemG f).2 (LemK.mem_euler_eigenspace_iff.1 hf).1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => LemK.generated_submodule_stable_under_action V a b hv
  have hGA : ∀ a b, ∀ f ∈ G, LemK.tensVd E a b f ∈ G := fun a b f hf =>
    (hmemG _).2 (LemK.dualTensorAction_mem hGs a b ((hmemG f).1 hf))
  have hXA : ∀ a b, ∀ f ∈ X, LemK.tensVd E a b f ∈ X := fun a b f hf => LemK.euler_eigenspace_stable_under_action hE hGs a b hf
  have hspec := fun (f : Fin (2 * r + k + 1) → D) (hf : f ∈ G) =>
    tMapD_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap (xJ P z) x₀ w hx₀ f
      ((hmemG f).1 hf)
  have hsm : ∀ f ∈ G, IsSmoothL2 ε (L f) := fun f hf => (hspec f hf).1
  have hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (LemK.tensVd E a b f) g :=
    fun f hf a b g hg => (hspec f hf).2.1 a b g hg
  obtain ⟨Tl, hTl, hTint⟩ := exists_lin ε (LemK.tensVd E) G L hsm hGA hder
  have hbd : ∀ f ∈ G, ∃ C : ℝ, ∀ g ∈ UJset ε, ‖L f g‖ ≤ C * frob g ^ (1 - aExp ε h) := fun f hf => by
    obtain ⟨C, hC⟩ := (hspec f hf).2.2 []
    exact ⟨C, hC⟩
  have hcont : ∀ f ∈ G, ContinuousOn (L f) (UJset ε) := fun f hf => QuotA.contOn_of_smooth (hsm f hf).1
  set ψ := Formalism.MainNotions.S.psiGen k r z c with hψdef
  let Z : Submodule ℂ (Fin (2 * r + k + 1) → D) :=
    { carrier := {y | y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0}
      add_mem' := by
        rintro y₁ y₂ ⟨h1X, h1⟩ ⟨h2X, h2⟩
        refine ⟨X.add_mem h1X h2X, fun g hg => ?_⟩
        rw [L.map_add, QuotA.per_add hP hB hp hq hsg (hcont _ (hXG h1X)) (hbd _ (hXG h1X)) (hcont _ (hXG h2X))
          (hbd _ (hXG h2X)) ξ hg, h1 g hg, h2 g hg, add_zero]
      zero_mem' := by
        refine ⟨X.zero_mem, fun g hg => ?_⟩
        have := QuotA.per_smul P μW μN ψ π 0 0 ξ g
        rw [zero_smul, zero_smul] at this
        rw [L.map_zero, this]
      smul_mem' := by
        rintro a y ⟨hyX, hy⟩
        refine ⟨X.smul_mem a hyX, fun g hg => ?_⟩
        rw [L.map_smul, QuotA.per_smul, hy g hg, smul_zero] }
  have hmemZ : ∀ y, y ∈ Z ↔ y ∈ X ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN ψ π (L y) ξ g = 0 :=
    fun y => Iff.rfl
  have hZX : Z ≤ X := fun y hy => ((hmemZ y).1 hy).1
  have hZA : ∀ a b, ∀ y ∈ Z, LemK.tensVd E a b y ∈ Z := by
    intro a b y hy
    obtain ⟨hyX, hy0⟩ := (hmemZ y).1 hy
    refine (hmemZ _).2 ⟨hXA a b y hyX, fun g hg => ?_⟩
    rw [← QuotA.per_congr hP hB ψ (fun g' hg' => hder y (hXG hyX) a b g' hg') ξ hg,
      (per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hsg).2 (L y) (hsm y (hXG hyX)).1
        (fun wd => (hspec y (hXG hyX)).2.2 wd) a b g hg ξ]
    exact QuotA.eabB_zero hP (fun y' hy' => hy0 y' hy') a b hg
  have hZφ : ∀ y ∈ X, ∀ y' ∈ Z, Tl y = Tl y' → y ∈ Z := by
    intro y hy y' hy' he
    have e := congrArg Subtype.val he
    rw [hTl y (hXG hy), hTl y' (hXG (hZX hy'))] at e
    have hEq := QuotA.eqOn_unitary_of_toL2_eq (hsm y (hXG hy)) (hsm y' (hXG (hZX hy'))) e
    refine (hmemZ y).2 ⟨hy, fun g hg => ?_⟩
    rw [QuotA.per_congr hP hB ψ hEq ξ hg]
    exact ((hmemZ y').1 hy').2 g hg
  have hxZ : x ∉ Z := by
    intro hxZ
    obtain ⟨g, hg, hne⟩ := hper
    exact hne (((hmemZ x).1 hxZ).2 g hg)
  have hkfin : ∀ x' ∈ X, ∃ S : Submodule ℂ (Fin (2 * r + k + 1) → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensVd E) S ∧ x' ∈ S := fun x' hx' => LemK.eigenspace_K_finite hE hV.1 hV.2.1 hx'
  have hK2 := (LemK.k2Vd _ ε lam h H σ D E V s hσ hD hV hc hVK hHC.2 hHC.1 hGL hp1 hq1).2
  have hK3 : ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensVd E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ x' ∈ X, ψ' x' ≠ 0 → ∃ W : Submodule ℂ (smD ε (rreg ε)), W ≤ X.map ψ' ∧
        IsKIrrHW ε (smE ε (rreg ε)) (lowK ε (lam - Pi.single s 1)) W ∧
        ∀ v ∈ W, casimir (smE ε (rreg ε)) v = (casVal (lam - Pi.single s 1) : ℂ) • v := by
    intro ψ' hψ' x' hx' hψx'
    exact LemK.k3Vd _ ε lam h H σ D E V s (smD ε (rreg ε)) (smE ε (rreg ε)) ψ' x' hσ hD hV hc hVK hHC.2
      hHC.1 hGL hp1 hq1 hHC'.1 hDR.glRep hUR (fun a b f hf => hψ' a b f ((hmemG f).2 hf)) hx' hψx'
  have hline : ∃ ys ∈ X, ∀ ψ' : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b, ∀ y ∈ G, ψ' (LemK.tensVd E a b y) = smE ε (rreg ε) a b (ψ' y)) →
      ∀ w' ∈ X.map ψ', IsKHWVec ε (smE ε (rreg ε)) (lowK ε (lam - Pi.single s 1)) w' →
        ∃ c : ℂ, w' = c • ψ' ys := by
    obtain ⟨ys, hys, hl⟩ := line (isKUnitary_of_isInfUnitary hU) X (lowK ε (lam - Pi.single s 1)) hkfin hK2
    exact ⟨ys, hys, fun ψ' hψ' w' hw' hwK =>
      hl _ (smE ε (rreg ε)) ψ' (fun a b _ x' hx' => hψ' a b x' (hXG hx')) w' hw' hwK⟩
  obtain ⟨Y', W, hY'X, hW, hY'Z, hirr, hcas, hK⟩ :=
    QuotA.quot_generic (LemK.tensVd E) G X Z (lam - Pi.single s 1) hstd Tl hXG hTint hK3 hline hkfin hZX hZA
      hZφ hx hxZ
  refine ⟨Y'.map L, W, ?_, ?_, hirr, hcas, hK, ?_⟩
  · rintro F hF
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    exact ⟨y, hY'X hy, rfl⟩
  · intro v
    rw [hW]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨L y, Submodule.mem_map_of_mem hy, hTl y (hXG (hY'X hy))⟩
    · rintro ⟨F, hF, hv⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
      exact ⟨y, hy, Subtype.ext (hv.trans (hTl y (hXG (hY'X hy))).symm)⟩
  · rintro F hF hF0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hF
    have hyZ : y ∈ Z := (hmemZ y).2 ⟨hY'X hy, hF0⟩
    rw [hY'Z y hy hyZ, L.map_zero]
    intro g _
    rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepUp
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem stepUp : StepUpStatement := by
  intro hIS k r ε u h hgap hp hq lam s hlam hgl hlam' hgl' hu hB
  classical
  obtain ⟨T, μ, P, z, c, Vp, _, _, _, π, μW, μN, hμ, hP, hBD, v₁, v₂, ξ, x₀, x, hx₀, hx, hne⟩ := hB
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hgap
  have hdatum := LemK.psiDatum (2 * r + k + 1) ε lam h T μ hlam hgl hNeed hq0 hμ
  obtain ⟨H, _, _, _, σ, D, E, V, ι, hσ, hD, hV, hc, hVK, hcoef⟩ := hdatum
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hX₀ : P * x₀ * P⁻¹ ∈ UJset ε := cayley_conj_mem_unitary_group hP hx₀
  have hper : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
      (coefX σ (P * x₀ * P⁻¹) (((ι.symm v₂ : V) : D) : H) (((ι.symm v₁ : V) : D) : H)) ξ x =
      aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x := by
    have hHW := hBD.2.2.2.2.1
    have hHN := hBD.2.2.2.2.2
    have : SigmaFinite μW := hHW.1
    have : SigmaFinite μN := hHN.1
    unfold per aaFun sInt
    apply integral_congr_ae
    filter_upwards [ae_mem_unitary_nilpotent_product z μW μN hHW hHN] with p hp'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      unitary_hermitian_form_mul_mem hp'.1.1 hp'.2.1
    have hg := unitary_hermitian_form_mul_mem hs hx
    have hinv : x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := (Transport.uh_facts hP hx₀).2.1
    have hG : P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹ ∈ UJset ε :=
      cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem hinv hg)
    have hX : P⁻¹ * (P * x₀ * P⁻¹) * P = x₀ := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
        Matrix.mul_one]
    have heq : (P * x₀ * P⁻¹)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) =
        P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹ := by
      have h1 := conj_inv_mul_conj P (P * x₀ * P⁻¹) (Matrix.of p.1 * Matrix.of p.2 * x) hd
      rw [hX] at h1
      exact h1.symm
    show coefX σ (P * x₀ * P⁻¹) _ _ (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • _ =
      psiCoef T μ P v₁ v₂ (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) • _
    unfold coefX psiCoef
    rw [heq, hcoef _ hG (ι.symm v₁) (ι.symm v₂)]
    simp only [LinearEquiv.apply_symm_apply]
  have hne' : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
      (coefX σ (P * x₀ * P⁻¹) (((ι.symm v₂ : V) : D) : H) (((ι.symm v₁ : V) : D) : H)) ξ x ≠ 0 := by
    rw [hper]; exact hne
  obtain ⟨y, hy⟩ := evalP k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hgap hlam hgl z c Vp π
    μW μN P hP hBD (P * x₀ * P⁻¹) (ι.symm v₂) (ι.symm v₁) ξ s x hX₀ hx hu hne'
  have hstab : ∀ a b, ∀ m ∈ genSub E V, E a b m ∈ genSub E V := fun a b _ hm =>
    LemK.generated_submodule_stable_under_action V a b hm
  have hkill : ∀ m ∈ genSub E V, Capelli.capelliC E (((-(LemK.thV lam s)) : ℝ) : ℂ) m = 0 := by
    intro m hm
    rw [capVal (2 * r + k + 1) ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hlam hgl hNeed hq0 _ m hm,
      Finset.prod_eq_zero (Finset.mem_univ s) (by push_cast; ring), zero_smul]
  have hvS : (((ι.symm v₁ : V) : D)) ∈ genSub E V :=
    LemK.le_generatedSubmodule_dual V (ι.symm v₁).2
  have hXs := (eig D (2 * r + k) E (genSub E V) (-(LemK.thV lam s)) y y ((ι.symm v₁ : V) : D)
    hD.glRep hstab hkill hvS).1
  rw [neg_neg] at hXs
  obtain ⟨Wf, W', hWf, hW', hirr, hcas, hK, hinj⟩ := quotP k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ
    hcoef hp hq hgap hlam hgl z c Vp π μW μN P hP hBD (P * x₀ * P⁻¹) (ι.symm v₂) ξ s
    (Capelli.nnPlus E y (((-(LemK.thV lam s)) : ℝ) : ℂ) ((ι.symm v₁ : V) : D)) hX₀ hlam' hgl' hXs ⟨x, hx, hy⟩
  refine finStep hIS k r ε u (lam + Pi.single s 1) h z c Vp π μW μN P hP hBD hp hq hgap hlam' hgl' ξ Wf W'
    ?_ hW' hirr hcas hK hinj
  intro F hF
  obtain ⟨y', hy', rfl⟩ := hWf F hF
  have hyS : ∀ c', y' c' ∈ genSub E V := (LemK.mem_eigenTensorSpace_gen_iff.1 hy').1
  obtain ⟨hsm, -, hbd⟩ := tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hgap hlam hgl
    (xJ P z) (P * x₀ * P⁻¹) (ι.symm v₂) hX₀ y' hyS
  obtain ⟨C, hC⟩ := hbd []
  exact ⟨CapelliMinorRestriction.cont_of_smoothOnG hsm.1, C, hC⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

