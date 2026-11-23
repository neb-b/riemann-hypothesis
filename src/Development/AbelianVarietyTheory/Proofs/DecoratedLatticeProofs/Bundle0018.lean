module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearIsQuotIntTInt
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app app_coe)
open scoped Topology

noncomputable section
namespace GlobalTheory.PosOne.RrLin

theorem exists_open_translations {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {Φ : M → ℂ} (hΦ : Φ ∈ SB M) :
    ∃ Λ : AddSubgroup M, IsOpen (Λ : Set M) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  let Λ : AddSubgroup M :=
    { carrier := {y | ∀ x, Φ (x + y) = Φ x}
      zero_mem' := fun x => by simp
      add_mem' := fun {y z} hy hz x => by rw [← add_assoc, hz, hy]
      neg_mem' := fun {y} hy x => by rw [← hy (x + -y)]; simp }
  refine ⟨Λ, Λ.isOpen_of_mem_nhds (g := 0) ?_, fun x y hy => hy x⟩
  have h1 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + y) = Φ x := by
    refine IsCompact.eventually_forall_of_forall_eventually hΦ.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : M × M => (Φ (q.2 + q.1), Φ q.2) :=
      (hΦ.1.comp_continuous (continuous_snd.add continuous_fst)).prodMk
        (hΦ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ y in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + -y) = Φ x := by
    have ht : Filter.Tendsto (fun y : M => -y) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := M)).tendsto 0
    exact ht.eventually h1
  filter_upwards [h1, h2] with y hs hs' x
  by_cases hx : x ∈ tsupport Φ
  · exact hs x hx
  by_cases hx' : x + y ∈ tsupport Φ
  · rw [← hs' _ hx']; simp
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem exists_isQuotInt_tInt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (hp : 1 ≤ p) (hpc : p ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] {μ : kˣ →* ℂˣ} (hμ : IsOpen (μ.ker : Set kˣ))
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} (hσ : IsSmoothRep σ)
    {B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hB : BilPos ψ μ p σ B) (F : A)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ z, IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) z := by
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1
  let E : GL (n ⊕ Fin c) k → SB (Matrix n n' k) := fun h =>
    ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩
  set f := tInt ψ ν μ p σ B F Φ.1 with hf
  have hfE : ∀ h, f h = B (E h) (σ h F) := fun h => by
    rw [hf, tInt]
    exact congrArg (fun l : A →ₗ[ℂ] ℂ => l (σ h F)) (app_coe B (E h))
  have hmul : ∀ (g h : GL (n ⊕ Fin c) k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ),
      om μ 1 (g * h) Ψ = om μ 1 g (om μ 1 h Ψ) := fun g h Ψ => by
    rw [← om_mul, one_mul]
  refine (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG f).2 ?_ ?_ ?_
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have hU : IsOpen ({u : GL (n ⊕ Fin c) k | om μ 1 u Φ.1 = Φ.1} ∩ {u | σ u F = F}) :=
      ((isOpen_stabilizer_om hμ Φ.2).preimage (Continuous.prodMk_right 1)).inter (hσ F)
    have ht : Filter.Tendsto (fun y : GL (n ⊕ Fin c) k => h⁻¹ * y) (𝓝 h) (𝓝 1) := by
      simpa using (continuous_const_mul h⁻¹).tendsto h
    filter_upwards [ht.eventually (hU.mem_nhds ⟨om_one μ _, by simp⟩)] with y hy
    obtain ⟨u, rfl⟩ : ∃ u, y = h * u := ⟨h⁻¹ * y, by simp⟩
    rw [inv_mul_cancel_left] at hy
    have h1 : om μ 1 u Φ.1 = Φ.1 := hy.1
    have h2 : σ u F = F := hy.2
    have h3 : E (h * u) = E h := Subtype.ext (by
      show opE ψ ν p (om μ 1 (h * u) Φ.1) = opE ψ ν p (om μ 1 h Φ.1)
      rw [hmul, h1])
    rw [hfE h, hfE (h * u), h3, map_mul, Module.End.mul_apply, h2]
  · obtain ⟨Λ, hΛ, hΛ'⟩ := exists_open_translations Φ.2
    obtain ⟨Ω, hΩ, H⟩ := opE_support_compact_mod_R k n n' c p hp hpc ψ hψ hψ1 ν (tsupport Φ.1)
      Φ.2.2 Λ hΛ
    refine ⟨Ω, hΩ, fun h hh => ?_⟩
    have hne : E h ≠ 0 := fun h0 => hh (by rw [hfE, h0]; simp)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν p (om μ 1 h Φ.1) x₀ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (Subtype.ext (funext hc))
    exact H μ Φ.1 (subset_tsupport _) hΛ' (fun _ => 1) (IsLocallyConstant.const 1) h x₀
      (by simpa using hx₀)
  · intro x u hu h
    set a : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) with ha
    let Ψ : SB (Matrix n n' k) := ⟨om μ 1 x (E h).1, om_mem_SB μ 1 x (E h).2⟩
    have h1 : E (embX c x * u * h) = (a * (ψ (-simpleSum u) : ℂ)) • Ψ := by
      apply Subtype.ext
      show opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) =
        (a * (ψ (-simpleSum u) : ℂ)) • om μ 1 x (opE ψ ν p (om μ 1 h Φ.1))
      rw [mul_assoc, hmul, (opE_om_embX k n n' c p hp hpc ψ ν μ _).1, hmul,
        opE_om_target_unipotent k n n' c p hp hpc ψ ν μ _ u hu]
      funext y
      simp only [om, Pi.smul_apply, smul_eq_mul, ha]
      ring
    have h3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; simp
    have h4 : a * a =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) := by
      rw [ha, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos _ _)]
      congr 2
      ring
    have h5 := hB.1 (E h) u hu (σ h F)
    have h6 := hB.2 x (E h) Ψ (σ u (σ h F)) rfl
    rw [hfE, hfE, h1, map_smul, LinearMap.smul_apply, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply, h6, h5, ← h4, ← ha, smul_eq_mul]
    linear_combination (a * a * B (E h) (σ h F)) * h3

end GlobalTheory.PosOne.RrLin

namespace GlobalTheory.PosOne.RrLin
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem exists_linear_isQuotInt_tInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ'), ∃ Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) ∧ IsNEquiv ψ p ρ' Rr := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ hψ1 ν _ μ hμ μX _ μG _ A _ _ σ hσ B hB F ρ' hρ'
  have uniq := (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG · |>.1)
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1

  have hfE : ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) h,
      tInt ψ ν μ p σ B F Φ.1 h =
        B ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩ (σ h F) := fun Φ h => by
    rw [tInt]
    exact congrArg (fun l : A →ₗ[ℂ] ℂ => l (σ h F)) (app_coe B ⟨_, hE _ (om_mem_SB μ 1 h Φ.2)⟩)

  have hlinf : ∀ (a : ℂ) (Φ Ψ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      tInt ψ ν μ p σ B F (a • Φ + Ψ).1 = fun h => a * tInt ψ ν μ p σ B F Φ.1 h + tInt ψ ν μ p σ B F Ψ.1 h := by
    intro a Φ Ψ
    funext h
    rw [hfE, hfE, hfE, ← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.add_apply, ← map_smul, ← map_add (f := _)]
    congr 2
    apply Subtype.ext
    show opE ψ ν p (om μ 1 h (a • Φ.1 + Ψ.1)) =
      a • opE ψ ν p (om μ 1 h Φ.1) + opE ψ ν p (om μ 1 h Ψ.1)
    have e : om μ 1 h (a • Φ.1 + Ψ.1) = a • om μ 1 h Φ.1 + om μ 1 h Ψ.1 := by
      funext y; simp only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact (opE_SB_and_linear k n n' c p ψ hψ ν).2 a _ (om_mem_SB μ 1 h Φ.2) _ (om_mem_SB μ 1 h Ψ.2)
  have hex := fun Φ => exists_isQuotInt_tInt hp hpc hψ hψ1 ν hμ μX μG hσ hB F Φ
  choose Rr hRr using hex
  have hlin : ∀ (a : ℂ) Φ Ψ, Rr (a • Φ + Ψ) = a * Rr Φ + Rr Ψ := fun a Φ Ψ => by
    refine uniq _ _ _ (hRr _) ?_
    rw [hlinf]
    exact GlobalTheory.RootEx.QuotLinear.isQuotInt_linear k n c p hp hpc ν μX μG _ _ a _ _ (hRr Φ) (hRr Ψ)
  have h0 : Rr 0 = 0 := by simpa using hlin 1 0 0
  let RL : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ :=
    { toFun := Rr
      map_add' := fun Φ Ψ => by simpa using hlin 1 Φ Ψ
      map_smul' := fun a Φ => by simpa [h0] using hlin a Φ 0 }
  refine ⟨RL, hRr, fun g hg Φ => ?_⟩
  show Rr (ρ' g Φ) = (ψ (simpleSum g) : ℂ) * Rr Φ
  have e : tInt ψ ν μ p σ B F (ρ' g Φ).1 = tInt ψ ν μ p σ B F ((ψ (simpleSum g) : ℂ) • Φ + 0).1 := by
    funext h
    rw [hfE, hfE]
    congr 2
    apply Subtype.ext
    show opE ψ ν p (om μ 1 h (ρ' g Φ).1) = opE ψ ν p (om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1 + 0))
    have e1 : om μ 1 h (om μ g 1 Φ.1) = om μ g 1 (om μ 1 h Φ.1) := by
      rw [← om_mul, ← om_mul, one_mul, mul_one, mul_one, one_mul]
    rw [hρ', e1, GlobalTheory.RootExSource.opE_om_source k n n' c p hp hpc ψ ν μ _ g hg, add_zero]
    have e2 : om μ 1 h ((ψ (simpleSum g) : ℂ) • Φ.1) = (ψ (simpleSum g) : ℂ) • om μ 1 h Φ.1 := by
      funext y; simp only [om, Pi.smul_apply, smul_eq_mul]; ring
    rw [e2]
    funext x
    simp only [opE, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  have e3 : Rr (ρ' g Φ) = Rr ((ψ (simpleSum g) : ℂ) • Φ + 0) := uniq _ _ _ (hRr _) (e ▸ hRr _)
  rw [e3, hlin, h0, add_zero]

end GlobalTheory.PosOne.RrLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotIntCells
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.CellQuotInt

theorem isQuotInt_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsCO J) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h, ∀ j ∈ J, f (h * j) = f h) (_ : ∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers p J T f), (∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤) ∧ ∀ z, IsQuotInt ν μX μG p f z ↔ z = ∑ h ∈ T, (((μG J).toReal / (volCell ν μX p J h).toReal : ℝ) : ℂ) * f h := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ν _ μX _ μG _ J hJ f hfJ hfR T hT
  classical
  obtain ⟨bX, lX, sX, -, -, -, hXH, hXR⟩ := GlobalTheory.SplitWeil.volGL_haar k n ν
  obtain ⟨bG, lG, sG, -, -, -⟩ := GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  obtain ⟨hN, -, hH, hRi, hconj⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c p hp hpc ν
  haveI : LocallyCompactSpace (N k n c p) := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite (volN ν n c p) := Measure.IsHaarMeasure.sigmaFinite _
  haveI : μX.IsMulRightInvariant := by
    rw [Measure.isMulLeftInvariant_eq_smul μX (volGL ν n)]
    infer_instance
  have hRm : ∀ (g : GL n k) (u : N k n c p), embX c g * (u : GL (n ⊕ Fin c) k) ∈ R k n c p :=
    fun g u => mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right u.2)
  have hm : Continuous (fun z : GL n k × N k n c p => embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) :=
    (GlobalTheory.QuotInt.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  let S : GL (n ⊕ Fin c) k → Set (GL n k × N k n c p) :=
    fun h => {z | h⁻¹ * (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) * h ∈ J}
  have hSo : ∀ h, IsOpen (S h) := fun h =>
    hJ.1.preimage ((continuous_const.mul hm).mul continuous_const)
  have hScomp : ∀ h, ∃ D, IsCompact D ∧ S h ⊆ D := by
    intro h
    have hK : IsCompact ((fun x => h * x * h⁻¹) '' (J : Set (GL (n ⊕ Fin c) k))) :=
      hJ.2.image (by fun_prop)
    obtain ⟨D, hD, hDm⟩ := GlobalTheory.QuotInt.compact_preimage hN hK
    exact ⟨D, hD, fun z hz => hDm z ⟨_, hz, by group⟩⟩
  have hvol : ∀ h, volCell ν μX p J h = (μX.prod (volN ν n c p)) (S h) := by
    intro h
    rw [Measure.prod_apply (hSo h).measurableSet]
    rfl
  have hvol0 : ∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤ := by
    intro h
    obtain ⟨D, hD, hSD⟩ := hScomp h
    rw [hvol]
    exact ⟨(hSo h).measure_ne_zero _ ⟨(1, 1), by simp [S, J.one_mem]⟩,
      ((measure_mono hSD).trans_lt hD.measure_lt_top).ne⟩

  have hcell : ∀ h, ∫ g, (∫ u : N k n c p, (if h⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k)) * h ∈ J then (1 : ℂ) else 0)
      ∂(volN ν n c p)) ∂μX = (((volCell ν μX p J h).toReal : ℝ) : ℂ) := by
    intro h
    have e : (fun z : GL n k × N k n c p =>
        if h⁻¹ * (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) * h ∈ J then (1 : ℂ) else 0) =
        (S h).indicator (fun _ => (1 : ℂ)) := by
      funext z
      simp [S, Set.indicator_apply]
    have hint : Integrable ((S h).indicator (fun _ => (1 : ℂ))) (μX.prod (volN ν n c p)) := by
      rw [integrable_indicator_iff (hSo h).measurableSet]
      exact integrableOn_const (by rw [← hvol]; exact (hvol0 h).2)
    rw [← e] at hint
    have h2 := integral_prod _ hint
    simp only at h2
    rw [← h2, e, integral_indicator_const _ (hSo h).measurableSet, Measure.real, ← hvol]
    simp
  have hmod : ∀ (φ : GL (n ⊕ Fin c) k → ℂ) (g₀ : GL n k) (u₁ : GL (n ⊕ Fin c) k), u₁ ∈ N k n c p →
      ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) ∂(volN ν n c p)) ∂μX
        = ((nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) *
          ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) ∂μX := by
    intro φ g₀ u₁ hu₁
    have hpos : ∀ y : kˣ, 0 < nabs k y := fun y => (nabs_properties k).2.1 y
    have e3 : nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) ^ (-((c : ℝ) + 1 - 2 * p)) =
        nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p) := by
      have h3 : nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) =
          (nabs k (Matrix.GeneralLinearGroup.det g₀))⁻¹ := by
        simp [nabs]
      rw [h3, Real.inv_rpow (hpos _).le, ← Real.rpow_neg (hpos _).le, neg_neg]
    have step : ∀ g : GL n k,
        ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) ∂(volN ν n c p) =
          (nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p)) •
            ∫ u : N k n c p, φ (embX c (g * g₀) * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p) := by
      intro g
      have e1 := hconj g₀⁻¹ (fun y => φ (embX c (g * g₀) * y * u₁))
      have e2 := integral_mul_right_eq_self (μ := volN ν n c p)
        (fun u : N k n c p => φ (embX c (g * g₀) * (u : GL (n ⊕ Fin c) k))) ⟨u₁, hu₁⟩
      simp only [Subgroup.coe_mul, ← mul_assoc] at e2
      rw [e3, e2] at e1
      rw [← e1]
      congr 1
      funext u
      congr 1
      simp only [map_mul, map_inv]
      group
    simp only [step]
    rw [integral_smul, Complex.real_smul]
    congr 1
    have := integral_mul_right_eq_self (μ := μX)
      (fun g => ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) g₀
    simpa using this

  have hv0 : ∀ h, (volCell ν μX p J h).toReal ≠ 0 := fun h =>
    ENNReal.toReal_ne_zero.2 (hvol0 h)
  let F : GL (n ⊕ Fin c) k → ℂ := fun x =>
    ∑ t ∈ T, if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0
  have hFsb : F ∈ SB (GL (n ⊕ Fin c) k) := by
    have := GlobalTheory.QuotInt.sb_of_quot J hJ.1 hJ.2 (T.image (QuotientGroup.mk : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k ⧸ J))
      (fun q => ∑ t ∈ T, if (t : GL (n ⊕ Fin c) k ⧸ J) = q then
        f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0)
      (fun q hq => Finset.sum_eq_zero fun t ht => if_neg fun e => hq (Finset.mem_image.2 ⟨t, ht, e⟩))
    have hFeq : F = fun x : GL (n ⊕ Fin c) k => ∑ t ∈ T, if (t : GL (n ⊕ Fin c) k ⧸ J) = (x : GL (n ⊕ Fin c) k ⧸ J) then
        f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0 := by
      funext x
      simp only [F, QuotientGroup.eq]
    rw [hFeq]
    exact this
  have hFint : ∫ x, F x ∂μG =
      ∑ t ∈ T, ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t := by
    have hind : ∀ t : GL (n ⊕ Fin c) k,
        Integrable (fun x => if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) μG ∧
        ∫ x, (if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) ∂μG =
          ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t := by
      intro t
      have e : (fun x => if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) =
          fun x => (J : Set (GL (n ⊕ Fin c) k)).indicator
            (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ)) (t⁻¹ * x) := by
        funext x
        simp [Set.indicator_apply]
      have hi : Integrable ((J : Set (GL (n ⊕ Fin c) k)).indicator
          (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ))) μG := by
        rw [integrable_indicator_iff hJ.1.measurableSet]
        exact integrableOn_const hJ.2.measure_lt_top.ne
      rw [e]
      refine ⟨hi.comp_mul_left t⁻¹, ?_⟩
      rw [integral_mul_left_eq_self (fun x => (J : Set (GL (n ⊕ Fin c) k)).indicator
          (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ)) x) t⁻¹,
        integral_indicator_const _ hJ.1.measurableSet]
      simp only [Measure.real, Complex.real_smul]
      have := hv0 t
      push_cast
      field_simp
    show ∫ x, (∑ t ∈ T, _) ∂μG = _
    rw [MeasureTheory.integral_finsetSum _ (fun t _ => (hind t).1)]
    exact Finset.sum_congr rfl fun t _ => (hind t).2

  have hRinv : ∀ (y t : GL (n ⊕ Fin c) k), t⁻¹ * y ∈ J →
      DoubleCoset.mk (R k n c p) J y = DoubleCoset.mk (R k n c p) J t := by
    intro y t hy
    rw [DoubleCoset.eq]
    exact ⟨1, one_mem _, (t⁻¹ * y)⁻¹, J.inv_mem hy, by group⟩
  have hmkR : ∀ r ∈ R k n c p, ∀ y,
      DoubleCoset.mk (R k n c p) J (r * y) = DoubleCoset.mk (R k n c p) J y := by
    intro r hr y
    rw [DoubleCoset.eq]
    exact ⟨r⁻¹, inv_mem hr, 1, one_mem _, by group⟩
  have hFcell : ∀ t₀ ∈ T, ∀ y, DoubleCoset.mk (R k n c p) J y = DoubleCoset.mk (R k n c p) J t₀ →
      F y = if t₀⁻¹ * y ∈ J then f t₀ / (((volCell ν μX p J t₀).toReal : ℝ) : ℂ) else 0 := by
    intro t₀ ht₀ y hy
    show (∑ t ∈ T, _) = _
    rw [Finset.sum_eq_single t₀]
    · intro t ht hne
      rw [if_neg]
      intro hmem
      exact hne (hT.1 (Finset.mem_coe.2 ht) (Finset.mem_coe.2 ht₀) ((hRinv y t hmem).symm.trans hy))
    · intro h
      exact absurd ht₀ h
  have hFoff : ∀ y, (∀ t ∈ T, DoubleCoset.mk (R k n c p) J y ≠ DoubleCoset.mk (R k n c p) J t) → F y = 0 := by
    intro y hy
    exact Finset.sum_eq_zero fun t ht => if_neg fun hmem => hy t ht (hRinv y t hmem)
  have havg : ∀ x, f x = ∫ g, (∫ u : N k n c p, F (embX c g * (u : GL (n ⊕ Fin c) k) * x)
      ∂(volN ν n c p)) ∂μX := by
    intro x
    by_cases hx : ∃ t ∈ T, DoubleCoset.mk (R k n c p) J x = DoubleCoset.mk (R k n c p) J t
    · obtain ⟨t₀, ht₀, hxt⟩ := hx
      obtain ⟨r, hr, j, hj, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hxt.symm
      obtain ⟨g₀, u₁, hu₁, rfl⟩ := Radical.exists_of_mem_R hr
      set φ : GL (n ⊕ Fin c) k → ℂ := fun y => f t₀ / (((volCell ν μX p J t₀).toReal : ℝ) : ℂ) *
              (if t₀⁻¹ * y * t₀ ∈ J then (1 : ℂ) else 0) with hφ
      have key : ∀ (g : GL n k) (u : N k n c p),
          F (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁ * t₀ * j)) =
            φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) := by
        intro g u
        have hw : embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁) ∈ R k n c p :=
          mul_mem (hRm g u) hr
        have e : embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁ * t₀ * j) =
            (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j := by
          group
        have hmk : DoubleCoset.mk (R k n c p) J
            ((embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j) =
            DoubleCoset.mk (R k n c p) J t₀ := by
          rw [DoubleCoset.eq]
          exact ⟨_, inv_mem hw, j⁻¹, J.inv_mem hj, by group⟩
        rw [e, hFcell t₀ ht₀ _ hmk]
        have e2 : t₀⁻¹ * ((embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j) =
            t₀⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j := by
          group
        simp only [hφ, e2, J.mul_mem_cancel_right hj]
        split_ifs <;> simp
      simp only [key]
      rw [hmod φ g₀ u₁ hu₁]
      simp only [hφ, integral_const_mul]
      rw [hcell t₀, hfJ _ j hj, hfR g₀ u₁ hu₁ t₀]
      rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 (hv0 t₀))]
    · have hf0 : f x = 0 := by
        by_contra h0
        exact hx (hT.2 x h0)
      rw [hf0]
      have : ∀ (g : GL n k) (u : N k n c p), F (embX c g * (u : GL (n ⊕ Fin c) k) * x) = 0 := by
        intro g u
        apply hFoff
        intro t ht e
        exact hx ⟨t, ht, (hmkR _ (hRm g u) x).symm.trans e⟩
      simp [this]
  have hz₀ : IsQuotInt ν μX μG p f
      (∑ t ∈ T, ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t) :=
    ⟨F, hFsb, havg, hFint.symm⟩
  have huniq := (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG f).1
  exact ⟨hvol0, fun z => ⟨fun hz => huniq _ _ hz hz₀, fun e => by rw [e]; exact hz₀⟩⟩

end GlobalTheory.CellQuotInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalZetaIntegralOpenSubgroup
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOne

theorem covers_opE_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (J : Set (GL (n ⊕ Fin c) k))) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), ∃ T, Covers p J T fun h => opE ψ ν p (om μ 1 h Φ.1) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψc hψ ν _ μ _ J hJ Φ
  classical
  obtain ⟨Λ, hΛ, hper⟩ := exists_isOpen_addSubgroup_add_eq Φ.2.1 Φ.2.2
  obtain ⟨Ω, hΩ, hcov⟩ := opE_support_compact_mod_R k n n' c p hp1 hpc ψ hψc hψ ν (tsupport Φ.1) Φ.2.2 Λ hΛ
  obtain ⟨F, hF⟩ := hΩ.elim_finite_subcover (fun w : GL (n ⊕ Fin c) k => (fun g => w⁻¹ * g) ⁻¹' (J : Set _))
    (fun w => hJ.preimage (continuous_const.mul continuous_id))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [J.one_mem]⟩)
  let rep : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k := fun w => Quotient.out (DoubleCoset.mk (R k n c p) J w)
  have hrep : ∀ w, DoubleCoset.mk (R k n c p) J (rep w) = DoubleCoset.mk (R k n c p) J w :=
    fun w => DoubleCoset.out_eq' _
  refine ⟨F.image rep, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image] at ha hb
    obtain ⟨w₁, -, rfl⟩ := ha
    obtain ⟨w₂, -, rfl⟩ := hb
    rw [hrep, hrep] at hab
    simp only [rep, hab]
  · intro h hh
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hh
    obtain ⟨r, hr, w, hw, rfl⟩ := hcov μ Φ.1 (subset_tsupport _) (fun x y hy => hper x y hy) (fun _ => 1)
      (IsLocallyConstant.const 1) h x₀ (by simpa using hx₀)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hF hw)
    obtain ⟨hiF, hiw⟩ := Set.mem_iUnion.1 hi
    refine ⟨rep i, Finset.mem_image_of_mem _ hiF, ?_⟩
    rw [hrep, eq_comm, DoubleCoset.eq]
    exact ⟨r, hr, i⁻¹ * w, hiw, by group⟩

end GlobalTheory.PosOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiEqSumCoupIdx
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.Couple

theorem psi_eq_sum_coupIdx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z] (T : Chain k s X Z) (A : RepFam k s X) (c₁ c₂ : kˣ) (_ : T.Adapted A (box _ c₁) (box _ c₂)) (ψ : AddChar k Circle) (_ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (ε : k) (S : Finset ((X (s + 1) → k) ⧸ box (X (s + 1)) c₂)) (_ : T.coupIdx A (box _ c₁) (box _ c₂) ⊆ S), ∀ g ∈ A s 0 rfl, ∀ x₀, (∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y) ∧ ∀ η, GlobalTheory.StepData.hat ψ ν ε (T.Psi g x₀) η = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * GlobalTheory.StepData.hat ψ ν ε (cosetInd (box _ c₂) yb) η := by
  intro k _ _ _ _ _ _ s X _ _ Z _ _ T A c₁ c₂ hA ψ hψ ν _ ε S hS g hg x₀
  classical
  have key : ∀ y, T.Psi g x₀ y = ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := by
    intro y
    have hc : ∀ yb, cosetInd (box _ c₂) yb y = if Submodule.Quotient.mk y = yb then 1 else 0 := by
      intro yb; simp [cosetInd, Set.indicator_apply]
    simp_rw [hc, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · exact (T.xiPen_mk hA hg y x₀).symm
    · by_contra hne
      exact hm (Finset.mem_coe.1 (hS ⟨y, (hA g hg x₀ y).1 hne, rfl, g, hg, x₀, hne⟩))
  refine ⟨key, fun η => ?_⟩
  have hfun : T.Psi g x₀ = fun y => ∑ yb ∈ S, T.xiPen (box _ c₂) g yb x₀ * cosetInd (box _ c₂) yb y := funext key
  rw [hfun]
  simp only [GlobalTheory.StepData.hat, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun yb _ => ?_
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  · intro yb _
    simp_rw [mul_assoc]
    exact (integrable_hat ψ ν ε hψ (cosetInd_mem_SB c₂ yb) η).const_mul _

end GlobalTheory.Couple
end
end

