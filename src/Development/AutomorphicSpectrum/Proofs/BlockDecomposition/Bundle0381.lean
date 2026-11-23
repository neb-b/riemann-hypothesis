module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0367
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpinGlRelationsAdjoint
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount.SpinRel

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def quadM (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b

theorem term_comm {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g e : Fin n) :
    c a e * c e b * c d g - c d g * (c a e * c e b) =
      (if b = d then (if e = g then (2 : ℂ) • c a g else 0) else 0) -
        (if a = g then (if e = d then (2 : ℂ) • c d b else 0) else 0) := by
  have h1 := hc.1 e b d g
  have h2 := hc.1 a e d g
  have h : c a e * c e b * c d g - c d g * (c a e * c e b) =
      c a e * (c e b * c d g + c d g * c e b) - (c a e * c d g + c d g * c a e) * c e b := by
    noncomm_ring
  rw [h, h1, h2]
  by_cases hbd : b = d <;> by_cases heg : e = g <;> by_cases hag : a = g <;> by_cases hed : e = d <;>
    simp only [hbd, heg, hag, hed, and_self, and_true, and_false, true_and, false_and, if_true, if_false,
      mul_zero, zero_mul, sub_zero, two_smul, mul_two, two_mul] <;> simp_all [two_smul, mul_two, two_mul]

theorem quad_c {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d g : Fin n) :
    quadM c a b * c d g - c d g * quadM c a b =
      (if b = d then c a g else 0) - (if a = g then c d b else 0) := by
  have h : quadM c a b * c d g - c d g * quadM c a b =
      (1 / 2 : ℂ) • ∑ e, (c a e * c e b * c d g - c d g * (c a e * c e b)) := by
    simp only [quadM, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h]
  simp only [term_comm hc, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hag : a = g <;>
    simp [hbd, hag, smul_sub, smul_smul]

theorem quad_quad {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b d e : Fin n) :
    quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (if b = d then quadM c a e else 0) - (if e = a then quadM c d b else 0) := by
  have h : ∀ f, quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b =
      ((if b = d then c a f else 0) - (if a = f then c d b else 0)) * c f e +
        c d f * ((if b = f then c a e else 0) - (if a = e then c f b else 0)) := by
    intro f
    rw [← quad_c hc a b d f, ← quad_c hc a b f e]
    noncomm_ring
  have h2 : quadM c a b * quadM c d e - quadM c d e * quadM c a b =
      (1 / 2 : ℂ) • ∑ f, (quadM c a b * (c d f * c f e) - (c d f * c f e) * quadM c a b) := by
    conv_lhs => rw [show quadM c d e = (1 / 2 : ℂ) • ∑ f, c d f * c f e from rfl]
    simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      Finset.sum_sub_distrib]
  rw [h2]
  simp only [h, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  by_cases hbd : b = d <;> by_cases hae : a = e
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : e = a := hae.symm
    simp [hbd, hae, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel
  · have hea : ¬ e = a := fun h => hae h.symm
    simp [hbd, hae, hea, quadM, ite_mul, mul_ite, smul_sub, smul_add, Finset.sum_ite_eq, Finset.sum_ite_eq']
    try abel

theorem spinM_eq (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    spinM c a b = quadM c a b - (if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0) := rfl

theorem spin_glRel {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) : Formalism.REAL.GlRel (spinM c) := by
  intro a b d e
  have h := quad_quad hc a b d e
  have hcomm : spinM c a b * spinM c d e - spinM c d e * spinM c a b =
      quadM c a b * quadM c d e - quadM c d e * quadM c a b := by
    simp only [spinM_eq]
    by_cases hab : a = b <;> by_cases hde : d = e <;>
      simp only [hab, hde, if_true, if_false, sub_zero, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
        one_mul, mul_one] <;> module
  rw [hcomm, h]
  by_cases hbd : b = d
  · by_cases hea : e = a
    · subst hbd
      subst hea
      simp [spinM_eq]
    · have hae : ¬ a = e := fun h => hea h.symm
      subst hbd
      simp [spinM_eq, hea, hae]
  · by_cases hea : e = a
    · have hdb : ¬ d = b := fun h => hbd h.symm
      simp [spinM_eq, hbd, hea, hdb]
    · simp [hbd, hea]

theorem spin_conjTranspose {c : Fin n → Fin n → Matrix ι ι ℂ} (hc : IsCliff c) (a b : Fin n) :
    (spinM c a b)ᴴ = spinM c b a := by
  simp only [spinM_eq, quadM]
  by_cases hab : a = b
  · subst hab
    simp [conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul, Complex.conj_ofNat]
  · simp [hab, Ne.symm hab, conjTranspose_sum, conjTranspose_mul, hc.2, conjTranspose_smul]

theorem spinRel : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    Formalism.REAL.GlRel (spinM c) ∧ ∀ a b, (spinM c a b)ᴴ = spinM c b a :=
  fun _ hc => ⟨spin_glRel hc, spin_conjTranspose hc⟩

end GlobalTheory.CompanionTheory.RealCount.SpinRel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableOfHeckeSpectral
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SqIntHecke

theorem lintegral_sq_lt_top_of_cover {X ι κ : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ) [Finite ι]
    [Countable κ] (A : ι → κ → Set X) (hcov : ∀ x, ∃ i j, x ∈ A i j) (b w : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (E : ENNReal) (hE : E < ⊤) (hF : ∀ i j, ∀ x ∈ A i j, ‖F x‖ ≤ b i j)
    (hμ : ∀ i j, μ (A i j) ≤ ENNReal.ofReal (w i j) * E)
    (hsum : ∀ i, Summable fun j => b i j ^ 2 * w i j) :
    ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have hu : (⋃ p : ι × κ, A p.1 p.2) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, j, h⟩ := hcov x
    exact ⟨(i, j), h⟩
  have h1 : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∑' p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ := by
    conv_lhs => rw [← setLIntegral_univ, ← hu]
    exact lintegral_iUnion_le _ _
  have h2 : ∀ p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤
      ENNReal.ofReal (b p.1 p.2 ^ 2 * w p.1 p.2) * E := by
    rintro ⟨i, j⟩
    have h3 : ∫⁻ x in A i j, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∫⁻ x in A i j, ENNReal.ofReal (b i j ^ 2) ∂μ := by
      refine setLIntegral_mono measurable_const fun x hx => ?_
      rw [ENNReal.rpow_two, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hF i j x hx) 2)
    refine h3.trans ?_
    rw [setLIntegral_const, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
    gcongr
    exact hμ i j
  refine (h1.trans (ENNReal.tsum_le_tsum h2)).trans_lt ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (b i j ^ 2 * w i j))]
  refine ENNReal.mul_lt_top ?_ hE
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _) (hw i j)) (hsum i)]
  exact ENNReal.ofReal_lt_top

theorem sq_mul_pow_eq {r : ℕ} (q : ℝ) (e g : Fin r → ℕ) (ρ : Fin r → ℝ) (C : ℝ) :
    (C * ∏ j, ρ j ^ g j) ^ 2 * q ^ (∑ j, g j * e j) = C ^ 2 * ∏ j, (q ^ e j * ρ j ^ 2) ^ g j := by
  have h1 : ∏ j, (q ^ e j) ^ g j = q ^ (∑ j, g j * e j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have h2 : ∏ j, (ρ j ^ 2) ^ g j = (∏ j, ρ j ^ g j) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [mul_pow _ _ (g _)]
  rw [Finset.prod_mul_distrib, h1, h2, mul_pow C, mul_assoc, mul_comm (q ^ _)]

theorem isSqIntCoeff_of_heckeSpectral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π →
    Zls.HeckeSpectral π → IsSqIntCoeff π := by
  intro k _ _ _ _ N V _ _ π hs hi ha hu hH
  unfold IsSqIntCoeff CoeffLp
  intro _ _ μ hμ v l hl
  have hcen : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ w, ‖l (π z w)‖ = ‖l w‖ := by
    intro z hz w
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨c, hc⟩ := _root_.GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar k N V π hs hi ha t
    rw [hc, map_smul, norm_smul, hu t c hc, one_mul]
  have hF : ∀ g : GL (Fin N) k, ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
    intro g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    rw [hz, Subgroup.mem_center_iff.1 z.2 g, map_mul, Module.End.mul_apply, hcen _ z.2]
  have hmeas : AEStronglyMeasurable (fun q : AdGL k N => ‖l (π q.out v)‖) μ := by
    refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k N => ‖l (π q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (π g v)‖ from funext hF]
    exact ((SqIntBridge.isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  refine ⟨fun q => ‖l (π q.out v)‖, hF, ?_⟩
  unfold MemLp
  rw [show ENNReal.ofReal 2 = 2 by simp, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hmeas]
  simp only [ENNReal.toReal_ofNat]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (GL (Fin 0) k) := inferInstance
    have h1 : Subsingleton (AdGL k 0) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [Subsingleton.elim a b]⟩
    have h2 : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
    refine lintegral_sq_lt_top_of_cover μ _ (fun _ _ : Unit => Set.univ) (fun _ => ⟨(), (), trivial⟩)
      (fun _ _ => ‖l (π (1 : AdGL k 0).out v)‖) (fun _ _ => 1) (fun _ _ => zero_le_one) _ h2 ?_ (by simp)
      (fun _ => (hasSum_fintype _).summable)
    intro _ _ x _
    rw [Subsingleton.elim x 1, norm_norm]
  obtain ⟨m1, hm1, hK1⟩ := _root_.GlobalTheory.CompanionTheory.CongruenceBasis.exists_Km_subset k N _ (hs v) (by simp)
  obtain ⟨m2, hm2, hK2⟩ := _root_.GlobalTheory.CompanionTheory.CongruenceBasis.exists_Km_subset k N _ hl (by simp [Module.End.one_eq_id])
  have hm : 1 ≤ max m1 m2 := hm1.trans (le_max_left _ _)
  obtain ⟨m, hmm⟩ : ∃ m, m = max m1 m2 := ⟨_, rfl⟩
  rw [← hmm] at hm
  have hv : v ∈ fixed π (Zls.Km k N m) := by
    rintro ⟨x, hx⟩
    have : π x v = v := hK1 (_root_.GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone k N m1 m (hmm ▸ le_max_left _ _) hx)
    simpa using this
  have hlK : ∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l := fun x hx =>
    hK2 (_root_.GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone k N m2 m (hmm ▸ le_max_right _ _) hx)
  obtain ⟨s, hsK, hcov⟩ := _root_.GlobalTheory.CompanionTheory.Dblock.CartanCover.cartan_cover k N m hm hN
  have key : ∀ p : s, ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧
      (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧
      ∀ g : Fin (N - 1) → ℕ, ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m,
        ‖l (π (p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
    rintro ⟨p, hp⟩
    obtain ⟨h1, h2⟩ := hsK p hp
    obtain ⟨hf, hli, heq⟩ := _root_.GlobalTheory.CompanionTheory.CongruenceCoef.coef_const_translated_double_coset k N V π m v hv l hlK p.1 p.2 h1 h2
    obtain ⟨C, ρ, hρ0, hρ1, hb⟩ := _root_.GlobalTheory.CompanionTheory.CoeffBound.coeff_bound k N V π hs ha hH m hm (π p.2 v) hf (l ∘ₗ π p.1) hli
    refine ⟨C, ρ, hρ0, hρ1, fun g x hx y hy => ?_⟩
    rw [heq _ x hx y hy]
    exact hb g
  choose C ρ hρ0 hρ1 hbound using key
  refine lintegral_sq_lt_top_of_cover μ _
    (fun (p : s) (g : Fin (N - 1) → ℕ) => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2})
    ?_ (fun p g => C p * ∏ j, ρ p j ^ g j)
    (fun _ g => (Nat.card 𝓀[k] : ℝ) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))))
    (fun _ _ => by positivity)
    (μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))))
    (_root_.GlobalTheory.CompanionTheory.KmVol.measure_image_Km_lt_top k N μ hμ m) ?_ ?_ ?_
  · intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨p, hp, g, a, ha', b, hb, z, hz, rfl⟩ := hcov h
    exact ⟨⟨p, hp⟩, g, _, ⟨a, ha', b, hb, rfl⟩, (QuotientGroup.mk_mul_of_mem _ hz).symm⟩
  · rintro p g _ ⟨h, ⟨a, ha', b, hb, rfl⟩, rfl⟩
    show ‖‖l (π (QuotientGroup.mk _ : AdGL k N).out v)‖‖ ≤ _
    rw [norm_norm, hF]
    exact hbound p g a ha' b hb
  · intro p g
    obtain ⟨h1, h2⟩ := hsK p.1 p.2
    refine (_root_.GlobalTheory.CompanionTheory.KmVolume.measure_translated_doubleCoset_le k N μ hμ m hm p.1.1 p.1.2 h1 h2 g).trans_eq ?_
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro p
    have h := GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex (N - 1)
      (fun j => (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ p j ^ 2)
      (fun j => by positivity) (hρ1 p)
    exact (h.mul_left (C p ^ 2)).congr fun g => (sq_mul_pow_eq _ _ g _ _).symm

end GlobalTheory.CompanionTheory.SqIntHecke
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfSupEq
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepSecondIso

theorem subQuot_equiv_of_sup : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), E ≤ A → E ⊔ B = A →
    Nonempty ((subQuot E B).Equiv (subQuot A B)) := by
  intro G V _ _ _ ρ A B E hEA hsup
  have hEA' : E.toSubmodule ≤ A.toSubmodule := fun x hx => hEA hx
  let PE := Submodule.comap E.toSubmodule.subtype B.toSubmodule
  let PA := Submodule.comap A.toSubmodule.subtype B.toSubmodule
  let f : E.toSubmodule →ₗ[ℂ] A.toSubmodule ⧸ PA := PA.mkQ ∘ₗ Submodule.inclusion hEA'
  have hf : PE ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (p := PA) (Submodule.inclusion hEA' x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  let φ := PE.liftQ f hf
  have hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.inclusion hEA' x) :=
    fun _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective PE q
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hq
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective PA q
    have ha : (a : V) ∈ E.toSubmodule ⊔ B.toSubmodule := by
      rw [← Subrepresentation.toSubmodule_sup, hsup]
      exact a.2
    obtain ⟨e, he, b, hb, hab⟩ := Submodule.mem_sup.mp ha
    refine ⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩
    rw [hφ, Submodule.Quotient.eq]
    show e - (a : V) ∈ B.toSubmodule
    have hdiff : e - (a : V) = -b := by
      rw [← hab]
      abel
    rw [hdiff]
    exact B.toSubmodule.neg_mem hb
  let ψ := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨Representation.Equiv.mk' ⟨φ, fun g => ?_⟩ ψ.symm (fun x => ψ.symm_apply_apply x)
    (fun y => ψ.apply_symm_apply y)⟩
  exact Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)

end GlobalTheory.CompanionTheory.RepSecondIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientRealisedBySubreps
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SubquotPres

theorem exists_equiv_subQuot : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (π : Representation ℂ G W),
    IsSubquotient π ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ Nonempty (π.Equiv (subQuot A B)) := by
  intro G V W _ _ _ _ _ ρ π h
  obtain ⟨S, f, hf⟩ := h
  have hint : ∀ (g : G) (x : S.toSubmodule),
      f.toLinearMap (S.toRepresentation g x) = π g (f.toLinearMap x) := fun g x => by
    simpa only [Representation.IntertwiningMap.toLinearMap_apply] using
      Representation.IntertwiningMap.isIntertwining _ _ f g x
  let K : Submodule ℂ S.toSubmodule := LinearMap.ker f.toLinearMap
  let B : Subrepresentation ρ := ⟨K.map S.toSubmodule.subtype, by
    intro g v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨S.toRepresentation g x, ?_, rfl⟩
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hint, hx, map_zero]⟩
  have hBS : B ≤ S := by
    show K.map S.toSubmodule.subtype ≤ S.toSubmodule
    exact Submodule.map_subtype_le _ _
  have hQ : Submodule.comap S.toSubmodule.subtype B.toSubmodule = K :=
    Submodule.comap_map_eq_of_injective Subtype.val_injective K
  let φ := Submodule.liftQ (Submodule.comap S.toSubmodule.subtype B.toSubmodule) f.toLinearMap hQ.le
  have hφ : ∀ x : S.toSubmodule, φ (Submodule.Quotient.mk x) = f.toLinearMap x := fun x => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hQ.ge
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk x, by rw [hφ, Representation.IntertwiningMap.toLinearMap_apply]⟩
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hφint : ∀ (g : G) q, φ (GlobalTheory.SmGL.subQuot S B g q) = π g (φ q) := by
    intro g q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact hint g x
  have hT : ∀ g : G, e.symm.toLinearMap ∘ₗ π g =
      GlobalTheory.SmGL.subQuot S B g ∘ₗ e.symm.toLinearMap := by
    intro g
    ext w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    obtain ⟨q, rfl⟩ := e.surjective w
    rw [LinearEquiv.symm_apply_apply]
    exact (hφint g q).symm
  let T : Representation.IntertwiningMap π (GlobalTheory.SmGL.subQuot S B) :=
    ⟨e.symm.toLinearMap, hT⟩
  exact ⟨S, B, hBS, ⟨Representation.Equiv.mk' T e (fun w => e.apply_symm_apply w)
    (fun q => e.symm_apply_apply q)⟩⟩

end GlobalTheory.CompanionTheory.SubquotPres
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumTwOrbitEqZero
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.FiniteFourier

open GlobalTheory.CompanionTheory.TwistedAverage

theorem sum_twOrbit_eq_zero {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G)
    (hL : IsCompact (L : Set G)) (L₁ : Subgroup L) (hL₁ : IsOpen (L₁ : Set L)) (v : V)
    (hv : ∀ x ∈ L₁, ρ (x : G) v = v) (θ : L →* ℂˣ) (hθ : ∀ x ∈ L₁, θ x = 1)
    (hk : v ∈ twKer ρ L θ) [L₁.Normal] [Fintype (L ⧸ L₁)] :
    ∑ q : L ⧸ L₁, twOrbit ρ L θ v q.out = 0 := by
  classical
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hle : L₁ ≤ θ.ker := fun x hx => hθ x hx
  have hopen : IsOpen (θ.ker : Set L) := Subgroup.isOpen_mono hle hL₁
  obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL θ hopen hk
  have : L₁.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set C : Subgroup L := (M ⊓ L₁).normalCore with hC
  have : C.Normal := Subgroup.normalCore_normal _
  have : C.FiniteIndex := inferInstance
  have : Fintype (L ⧸ C) := Fintype.ofFinite _
  have hCM : C ≤ M ⊓ L₁ := Subgroup.normalCore_le _
  have : Finite (L₁ ⧸ C.subgroupOf L₁) := inferInstance
  have : Fintype (L₁ ⧸ C.subgroupOf L₁) := Fintype.ofFinite _
  have h0 := hsum C (hCM.trans inf_le_left)
  rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L θ v)
    (fun x k hk => twOrbit_mul_right ρ L θ v x k ⟨hv k hk, hθ k hk⟩)] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact h0

theorem eq_zero_of_twKer :
    ∀ {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ (L₁ : Subgroup L), IsOpen (L₁ : Set L) → ∀ (v : V), (∀ x ∈ L₁, ρ (x : G) v = v) → ∀ {ι : Type} (R : Finset ι), R.Nonempty → ∀ (χ : ι → (L →* ℂˣ)), (∀ a ∈ R, ∀ x ∈ L₁, χ a x = 1) → (∀ a ∈ R, v ∈ twKer ρ L (χ a)) → (∀ x : L, x ∉ L₁ → ∑ a ∈ R, (((χ a x)⁻¹ : ℂˣ) : ℂ) = 0) → v = 0 := by
  intro G V _ _ _ _ _ ρ hρ L hL L₁ hL₁ v hv ι R hR χ hχ hker hsum
  classical
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have : Finite (L ⧸ L₁) := Subgroup.quotient_finite_of_isOpen _ hL₁
  have : L₁.Normal := inferInstance
  have : Fintype (L ⧸ L₁) := Fintype.ofFinite _
  have key : ∀ a ∈ R, ∑ q : L ⧸ L₁, twOrbit ρ L (χ a) v q.out = 0 := fun a ha =>
    sum_twOrbit_eq_zero ρ hρ L hL L₁ hL₁ v hv (χ a) (hχ a ha) (hker a ha)
  have h0 : ∑ q : L ⧸ L₁, ∑ a ∈ R, twOrbit ρ L (χ a) v q.out = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero key
  have hoff : ∀ q : L ⧸ L₁, q ≠ 1 → ∑ a ∈ R, twOrbit ρ L (χ a) v q.out = 0 := by
    intro q hq
    have hnot : q.out ∉ L₁ := by
      intro hmem
      apply hq
      rw [← QuotientGroup.out_eq' q]
      exact (QuotientGroup.eq_one_iff _).2 hmem
    simp only [twOrbit]
    rw [← Finset.sum_smul, hsum _ hnot, zero_smul]
  have hone : ((1 : L ⧸ L₁).out : L) ∈ L₁ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
  have hmain : ∑ a ∈ R, twOrbit ρ L (χ a) v (1 : L ⧸ L₁).out = R.card • v := by
    rw [Finset.card_eq_sum_ones, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [twOrbit]
    rw [hχ a ha _ hone, hv _ hone]
    simp
  rw [Finset.sum_eq_single (1 : L ⧸ L₁) (fun q _ hq => hoff q hq)
    (fun h => absurd (Finset.mem_univ _) h), hmain] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 hR.card_pos.ne')
  · exact h0

end GlobalTheory.CompanionTheory.FiniteFourier
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittCoordQuotientPullBijectiveStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_coord_quotient_pull_bijective : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (cW : Coord q W d) (j : ℕ), Function.Bijective (((mqS q ρ hn {W}).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).pull j) := by
  first | exact @GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij | exact GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij | (intros; apply GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal.local_bij <;> assumption)
end

