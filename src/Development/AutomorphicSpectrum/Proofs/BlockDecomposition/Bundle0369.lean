module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterFormulaOfDiscreteSeriesDatum
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPow
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.CentralExp

theorem continuous_scalarGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ →* GL (Fin n) k) := by
  have hs : Continuous (fun a : k => Matrix.scalar (Fin n) a) := by
    have : (fun a : k => Matrix.scalar (Fin n) a) = fun a => Matrix.diagonal (fun _ => a) := by
      funext a; rfl
    rw [this]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hs.comp Units.continuous_val
  · exact hs.comp (Units.continuous_val.comp continuous_inv)

theorem norm_scalarBy_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), 0 < x.1 → ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy x t c → ‖c‖ = nabs k t ^ ((x.1 : ℝ) * s) := by
  intro k _ _ _ _ x hx
  have hirr := x.2.rep.irr
  obtain ⟨v, hv⟩ : ∃ v : x.2.rep.V, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton x.2.rep.V := ⟨fun a b => by rw [hcon a, hcon b]⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Subrepresentation x.rep)
    exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have huniq : ∀ (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c' := by
    intro t c c' h h'
    exact smul_left_injective ℂ hv ((h v).symm.trans (h' v))
  choose f hf using GlobalTheory.T.central_character_exists k x
  have hmul : ∀ a b : kˣ, f (a * b) = f a * f b := by
    intro a b
    refine huniq (a * b) _ _ (hf _) fun w => ?_
    rw [map_mul, map_mul, Module.End.mul_apply, hf b w, map_smul, hf a w, smul_smul, mul_comm]
  have hone : f 1 = 1 := by
    refine huniq 1 _ _ (hf _) fun w => ?_
    simp
  let χ₀ : kˣ →* ℂ := { toFun := f, map_one' := hone, map_mul' := hmul }
  let χ : kˣ →* ℂˣ := χ₀.toHomUnits
  have hχ : ∀ t, ((χ t : ℂˣ) : ℂ) = f t := fun t => rfl
  have hsm : IsSmoothChar χ := by
    have hset : (χ.ker : Set kˣ) = (Matrix.GeneralLinearGroup.scalar (Fin x.1) : kˣ →* GL (Fin x.1) k) ⁻¹'
        {g | x.rep g v = v} := by
      ext t
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq]
      rw [hf t v]
      constructor
      · intro h
        have : f t = 1 := by rw [← hχ, h]; rfl
        rw [this, one_smul]
      · intro h
        have : f t = 1 := smul_left_injective ℂ hv (by simpa using h)
        exact Units.ext (by rw [hχ, this]; rfl)
    show IsOpen (χ.ker : Set kˣ)
    rw [hset]
    exact (x.2.rep.smooth v).preimage (continuous_scalarGL k x.1)
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k χ hsm
  have hn : (x.1 : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  refine ⟨s / x.1, fun t c hc => ?_⟩
  rw [huniq t c (f t) hc (hf t), ← hχ, hs t, mul_div_cancel₀ _ hn]

end GlobalTheory.CompanionTheory.CentralExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterFormulaOfDiscreteSeriesDatumStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_formula_of_discrete_series_datum : PositivityTheory.RgDs.Hilb.StepDatum → PositivityTheory.RgDs.Hilb.StepFormulaF := by
  first | exact @GlobalTheory.CompanionTheory.Hilb.stepFormulaF | exact GlobalTheory.CompanionTheory.Hilb.stepFormulaF | (intros; apply GlobalTheory.CompanionTheory.Hilb.stepFormulaF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordVectorSpinWeight
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem spinM_vacuum_lowest : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, (∀ a b, a < b → c b a *ᵥ q = 0) →
    (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) ∧ ∀ a b, a < b → spinM c b a *ᵥ q = 0 := by
  intro n ι _ _ c hc q hq
  obtain ⟨h1, _⟩ := hc
  have two : (2 : Matrix ι ι ℂ) *ᵥ q = (2 : ℂ) • q := by
    have : (2 : Matrix ι ι ℂ) = (2 : ℂ) • (1 : Matrix ι ι ℂ) := by
      rw [two_smul]; exact one_add_one_eq_two.symm
    rw [this, Matrix.smul_mulVec, Matrix.one_mulVec]
  have anti : ∀ a b d e, c a b *ᵥ (c d e *ᵥ q) =
      (if a = e ∧ b = d then (2 : ℂ) • q else 0) - c d e *ᵥ (c a b *ᵥ q) := by
    intro a b d e
    have h := congrArg (fun M => M *ᵥ q) (h1 a b d e)
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec] at h
    simp only [Matrix.mulVec_mulVec]
    rw [eq_sub_iff_add_eq, h]
    split_ifs
    · exact two
    · simp
  have sumv : ∀ (a b : Fin n), (∑ e, c a e * c e b) *ᵥ q = ∑ e, c a e *ᵥ (c e b *ᵥ q) := by
    intro a b
    simp only [Matrix.mulVec_mulVec]
    exact map_sum (Matrix.mulVec.addMonoidHomLeft q) _ _
  have hT : ∀ a e : Fin n, c a e *ᵥ (c e a *ᵥ q) =
      (if e < a then (2 : ℂ) else if e = a then 1 else 0) • q := by
    intro a e
    rcases lt_trichotomy e a with h | h | h
    · rw [if_pos h, anti a e e a, hq e a h]
      simp
    · subst h
      have h2 := anti e e e e
      simp only [and_self, if_true] at h2
      have h3 : (2 : ℂ) • (c e e *ᵥ (c e e *ᵥ q)) = (2 : ℂ) • q := by
        rw [two_smul]
        nth_rewrite 1 [h2]
        rw [two_smul]
        abel
      have h4 := smul_right_injective (ι → ℂ) (two_ne_zero : (2 : ℂ) ≠ 0) h3
      simpa using h4
    · rw [if_neg (not_lt.mpr h.le), if_neg h.ne', hq a e h]
      simp
  have hs : ∀ a : Fin n, ∑ e : Fin n, (if e < a then (2 : ℂ) else if e = a then 1 else 0) =
      2 * ((a : ℕ) : ℂ) + 1 := by
    intro a
    have h0 : ∀ e : Fin n, (if e < a then (2 : ℂ) else if e = a then 1 else 0) =
        (if e < a then 2 else 0) + (if e = a then 1 else 0) := by
      intro e
      rcases lt_trichotomy e a with h | h | h
      · simp [h, h.ne]
      · simp [h]
      · simp [not_lt.mpr h.le, h.ne']
    simp only [h0]
    rw [sum_add_distrib, ← Finset.sum_filter]
    have h5 : univ.filter (fun e : Fin n => e < a) = Finset.Iio a := by ext; simp
    rw [h5]
    simp [Fin.card_Iio, mul_comm]
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · unfold spinM
    rw [if_pos rfl, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sumv]
    simp only [hT]
    rw [← Finset.sum_smul, hs, smul_smul, ← sub_smul]
    congr 1
    simp only [rhoV]
    push_cast
    ring
  · unfold spinM
    rw [if_neg hab.ne', sub_zero, Matrix.smul_mulVec, sumv]
    have : ∀ e : Fin n, c b e *ᵥ (c e a *ᵥ q) = 0 := by
      intro e
      rcases lt_trichotomy e a with h | h | h
      · rw [anti b e e a, if_neg (fun hh => hab.ne' hh.1), hq e b (h.trans hab)]
        simp
      · subst h
        rw [anti b e e e, if_neg (fun hh => hab.ne' hh.1), hq e b hab]
        simp
      · rw [hq a e h]
        simp
    simp [this]

end GlobalTheory.CompanionTheory.RealCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetRepsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_group_finite_coset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J H A : Subgroup G), IsCompact (J : Set G) → IsOpen (H : Set G) → H ≤ J → A ≤ J → (∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ H) → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ A) ∧ ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H := by
  first | exact @GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps | exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps | (intros; apply GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstEqOne
section
noncomputable section

open GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.ExtCharU

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pw_add {n : ℕ} (ξ : Fin n → ℂˣ) (x y : Fin n → ℤ) :
    GlobalTheory.BCT.pw ξ (x + y) = GlobalTheory.BCT.pw ξ x * GlobalTheory.BCT.pw ξ y := by
  simp only [GlobalTheory.BCT.pw, Pi.add_apply, zpow_add, Units.val_mul, Finset.prod_mul_distrib]

theorem pw_ne_zero {n : ℕ} (ξ : Fin n → ℂˣ) (x : Fin n → ℤ) : GlobalTheory.BCT.pw ξ x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

def dg {n : ℕ} (ϖ : kˣ) (e : Fin n → ℤ) : Fin n → kˣ := fun i => ϖ ^ e i

theorem dg_add {n : ℕ} (ϖ : kˣ) (x y : Fin n → ℤ) : dg ϖ (x + y) = dg ϖ x * dg ϖ y := by
  funext i; simp [dg, zpow_add]

theorem ord_zpow (ϖ : kˣ) (m : ℤ) : ord k (ϖ ^ m) = m * ord k ϖ := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o ϖ m
  have h2 : ord k (ϖ ^ m) = m • ord k ϖ := by
    have := congrArg Multiplicative.toAdd h
    simpa [o] using this
  simpa using h2

def rr (n : ℕ) : Fin n → ℤ := fun i => (n : ℤ) - 1 - (i : ℕ)

theorem rr_anti (n : ℕ) : StrictAnti (rr n) := fun i j h => by
  have : (i : ℕ) < j := h
  simp only [rr]; omega

theorem rr_smul_anti (n : ℕ) {N : ℤ} (hN : 0 < N) : StrictAnti (N • rr n) := fun i j h => by
  have := rr_anti n h
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_lt_mul_of_pos_left this hN

theorem add_anti {n : ℕ} (e : Fin n → ℤ) :
    ∃ N : ℤ, 0 < N ∧ StrictAnti (e + N • rr n) := by
  refine ⟨1 + 2 * ∑ i, |e i|, by positivity, fun i j h => ?_⟩
  have hij : (i : ℕ) < j := h
  have hi : |e i| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hj : |e j| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h1 := abs_le.1 (le_refl |e i|)
  have h2 := abs_le.1 (le_refl |e j|)
  set S := ∑ l, |e l|
  have hd : (1 : ℤ) ≤ rr n i - rr n j := by simp only [rr]; omega
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem const_eq_one (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ} {c : ℂ}
    (hz : z ≠ 0)
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) :
    c = 1 := by
  have hr := hx (rr n) (rr_anti n)
  have h2 := hx (rr n + rr n) (by
    simpa [two_smul] using rr_smul_anti n (N := 2) (by norm_num))
  have hd : (fun i => ϖ ^ (rr n + rr n) i) = (fun i => ϖ ^ rr n i) * (fun i => ϖ ^ rr n i) :=
    dg_add ϖ (rr n) (rr n)
  rw [hd, map_mul, Module.End.mul_apply, hr, map_smul, hr, smul_smul, pw_add] at h2
  set p := GlobalTheory.BCT.pw ξ (rr n)
  have hp : p ≠ 0 := pw_ne_zero ξ _
  have h3 : c * p * (c * p) = c * (p * p) := smul_left_injective ℂ hz h2
  have hc : c ≠ 0 := by
    rintro rfl
    apply hz
    have h4 : R (fun i => ϖ ^ rr n i) z = 0 := by simpa using hr
    have h5 := congrArg (R (fun i => ϖ ^ rr n i)⁻¹) h4
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h5
    simpa using h5
  have hpp : p * p ≠ 0 := mul_ne_zero hp hp
  apply mul_left_cancel₀ (mul_ne_zero hc hpp)
  linear_combination h3

theorem eig_all (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ}
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = GlobalTheory.BCT.pw ξ x • z)
    (e : Fin n → ℤ) : R (dg ϖ e) z = GlobalTheory.BCT.pw ξ e • z := by
  obtain ⟨N, hN, ha⟩ := add_anti e
  have hy := hx _ (rr_smul_anti n hN)
  have hxy := hx _ ha
  have hd : (fun i => ϖ ^ (e + N • rr n) i) = dg ϖ e * (fun i => ϖ ^ (N • rr n) i) :=
    dg_add ϖ e _
  rw [hd, map_mul, Module.End.mul_apply, hy, map_smul, pw_add, mul_comm, mul_smul] at hxy
  exact smul_right_injective M (pw_ne_zero ξ (N • rr n)) hxy

theorem extChar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (R : Representation ℂ (Fin n → kˣ) M) (z : M) (ϖ : kˣ) (ξ : Fin n → ℂˣ) (c : ℂ),
    z ≠ 0 → ord k ϖ = 1 → (∀ t ∈ torusO k (Fin n), R t z = z) →
    (∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) →
    ∀ t : Fin n → kˣ,
      R t z = (((torusChar fun i => unrChar k (ξ i)) t : ℂˣ) : ℂ) • z := by
  intro k _ _ _ _ n M _ _ R z ϖ ξ c hz hϖ hO hx t
  have hc : c = 1 := const_eq_one R hz hx
  subst hc
  simp only [one_mul] at hx
  set e : Fin n → ℤ := fun i => ord k (t i) with he
  have hu : t * (dg ϖ e)⁻¹ ∈ torusO k (Fin n) := by
    intro i
    apply ord_eq_zero_iff.1
    have h1 : ord k (t i * (ϖ ^ e i)⁻¹) = 0 := by
      have h2 := ord_mul k (t i * (ϖ ^ e i)⁻¹) (ϖ ^ e i)
      rw [inv_mul_cancel_right, ord_zpow, hϖ, mul_one] at h2
      have h3 : e i = ord k (t i) := rfl
      omega
    simpa [dg] using h1
  have ht : t = dg ϖ e * (t * (dg ϖ e)⁻¹) := by simp
  have h1 : R t z = R (dg ϖ e) z := by
    conv_lhs => rw [ht]
    rw [map_mul, Module.End.mul_apply, hO _ hu]
  rw [h1, eig_all R hx e, torusChar_apply]
  congr 1
  simp [GlobalTheory.BCT.pw, he, unrChar_apply]

end GlobalTheory.CompanionTheory.ExtCharU
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion
section
noncomputable section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology

namespace GlobalTheory.CompanionTheory.CTFin.Central

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_unip_mul {r : ℕ} {φ : Sm E a} (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  set f₀ := JointCont.finPart g x₀
  have hc : Continuous (fun x : BlockIx a r → Ad E => f₀⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a (f₀⁻¹ * f₀) φ = φ := by rw [inv_mul_cancel]; simp
  have hev : ∀ᶠ x in 𝓝 x₀, chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val) = φ.1 (unip x * g) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.mem_nhds h1)] with x hx
    have hx' : finRep E a (f₀⁻¹ * JointCont.finPart g x) φ = φ := hx
    have e : unip x * g = finGL E a f₀ * infGL E a (JointCont.infPart g x) * finGL E a (f₀⁻¹ * JointCont.finPart g x) := by
      rw [JointCont.unip_mul_eq, mul_assoc, infGL_comm, ← mul_assoc, ← map_mul (finGL E a), mul_inv_cancel_left]
    rw [chart_val, e]
    exact (congrArg (fun ψ : Sm E a => ψ.1 (finGL E a f₀ * infGL E a (JointCont.infPart g x))) hx').symm
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E => chart φ.1 (finGL E a f₀) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a f₀))
      ((φ.2 _).continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  exact hA.congr hev

theorem exists_bound_unip_mul {r : ℕ} {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (continuous_unip_mul (r := r) hφ g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : x = (fun p => algebraMap E (Ad E) (q p)) + fun p => x p - algebraMap E (Ad E) (q p) := by
    funext p
    show x p = algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p))
    exact (add_sub_cancel _ _).symm
  have hper : φ.1 (unip x * g) = φ.1 (unip (fun p => x p - algebraMap E (Ad E) (q p)) * g) := by
    conv_lhs => rw [hx]
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  rw [hper]
  exact hC _ fun p _ => hq p

theorem integrable_unip_mul {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx a r → Ad E))
    (h𝓕 : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) {φ : Sm E a} (hl : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g)
    (hφ : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Integrable (fun x => φ.1 (unip x * g)) (μ.restrict 𝓕) := by
  have hfin := covol_lt_top μ 𝓕 h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) hl hφ g
  exact Integrable.of_bound (continuous_unip_mul hφ g).aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem ct_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ), ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → (∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ (X : Lie E a) (g : GA E a), (lie E a X F).1 g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ) → ∀ φ F : Sm E a, (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → ∀ z ∈ Zalg E a, ∀ g, (z F).1 g = ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 hμ h𝓕 hlie
  haveI := hμ
  let P : Sm E a → Prop := fun φ =>
    (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}
  have hadd : ∀ φ ψ : Sm E a, P φ → P ψ → P (φ + ψ) := fun φ ψ h1 h2 =>
    ⟨fun γ g => by
      change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
      rw [h1.1, h2.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).add_mem (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)
       (show ψ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h2.2)⟩
  have hsmul : ∀ (c : ℂ) (φ : Sm E a), P φ → P (c • φ) := fun c φ h1 =>
    ⟨fun γ g => by
      change c • φ.1 _ = c • φ.1 _
      rw [h1.1],
     (GlobalTheory.PRep.smoothPart (finRep E a)).smul_mem c (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from h1.2)⟩
  have hint : ∀ ψ : Sm E a, P ψ → ∀ g, Integrable (fun x => ψ.1 (unip x * g)) (μ.restrict 𝓕) :=
    fun ψ h g => integrable_unip_mul μ 𝓕 h𝓕 h.1 h.2 g
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {T | ∀ φ, P φ → P (T φ) ∧ ∀ F : Sm E a, (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) →
          ∀ g, (T F).1 g = ∫ x in 𝓕, (T φ).1 (unip x * g) ∂μ}
      mul_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₂ φ hφ
        obtain ⟨h2, e2⟩ := hT₁ _ h1
        exact ⟨h2, fun F hF g => e2 (T₂ F) (e1 F hF) g⟩
      add_mem' := fun {T₁ T₂} hT₁ hT₂ φ hφ => by
        obtain ⟨h1, e1⟩ := hT₁ φ hφ
        obtain ⟨h2, e2⟩ := hT₂ φ hφ
        refine ⟨hadd _ _ h1 h2, fun F hF g => ?_⟩
        change (T₁ F).1 g + (T₂ F).1 g = ∫ x in 𝓕, ((T₁ φ).1 (unip x * g) + (T₂ φ).1 (unip x * g)) ∂μ
        rw [integral_add (hint _ h1 g) (hint _ h2 g), e1 F hF g, e2 F hF g]
      algebraMap_mem' := fun c φ hφ => by
        refine ⟨by rw [Module.algebraMap_end_apply]; exact hsmul c φ hφ, fun F hF g => ?_⟩
        rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
        change c • F.1 g = ∫ x in 𝓕, c • φ.1 (unip x * g) ∂μ
        rw [integral_smul, hF g] }
  have hL : ∀ X, lie E a X ∈ S := fun X φ hφ =>
    ⟨⟨fun γ g => GlobalTheory.SpehInfChar.lie_leftInv (ratGL E a).range X
        (fun u hu g' => by obtain ⟨γ', rfl⟩ := MonoidHom.mem_range.1 hu; exact hφ.1 γ' g') _ ⟨γ, rfl⟩ g,
      GlobalTheory.SpehInfChar.lie_mem_smoothPart X (show φ ∈ GlobalTheory.PRep.smoothPart (finRep E a) from hφ.2)⟩,
     fun F hF g => hlie φ F hφ.1 hφ.2 hF X g⟩
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  intro φ F hl hlev hF z hz g
  have hzS : z ∈ S := by
    refine (Algebra.adjoin_le (S := S) ?_) hz
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hzS φ ⟨hl, hlev⟩).2 F hF g

end GlobalTheory.CompanionTheory.CTFin.Central
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffAdjugateEntry
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y i j) :=
  contDiff_apply_apply ℝ i j

theorem contDiff_det {n : ℕ} {M : Mat n → Mat n} (hM : ∀ i j, ContDiff ℝ ∞ (fun y => M y i j)) :
    ContDiff ℝ ∞ (fun y => (M y).det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => hM _ _

theorem contDiff_adjugate_entry {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ∞ (fun y : Mat n => y.adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det fun a b => ?_
  by_cases h : a = j
  · subst h
    simpa [Matrix.updateRow_self] using contDiff_const
  · simpa [Matrix.updateRow_ne h] using contDiff_entry a b

theorem contDiffOn_inv {n : ℕ} : ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹) (GLs n) := by
  have hd : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹) (GLs n) :=
    (contDiff_det (M := id) contDiff_entry).contDiffOn.inv (fun y hy => hy)
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine (hd.mul (contDiff_adjugate_entry i j).contDiffOn).congr fun y _ => ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Mol.HfSmooth
end
end

