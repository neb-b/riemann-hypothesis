module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.EisHalfPlaneW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.SiegelWeilStdLt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchwartzDecayUniform
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKF0.Grow
open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
open GlobalTheory.LFun GlobalTheory.ThK in
theorem schwartz_decay_uniform (hA : HtBd) (hF : FinInv) (hS : Sob) (hT : TrBd) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  obtain ⟨C, -, hC⟩ := hA F E σ n d X W M
  obtain ⟨C', k, -, h⟩ := weighted hF hS hT hP.base.std hΦ N
  refine ⟨C' * C ^ k, k, fun g g' x => ?_⟩
  obtain ⟨m, h1, h2, h3⟩ := hC g g'
  rw [mul_assoc, ← mul_pow]
  exact h _ _ m _ h1 h2 (impl_sOf hP.weil g g') h3 x
end PositivityTheory.ThKF0.Grow
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelMultOfKAlt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelFrame
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem siegelMult_of_k : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    _root_.SiegelEisensteinSeries.BRoad.SiegelMult_k := by
  intro hSec hWL hD hDI hCM hGT hBd _ hPar hSg
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY χ hχ c hres b K a hb hK ha s₁ f hf
  obtain ⟨⟨ε, hε⟩, t₀, ht₀⟩ := hb
  have hb' : IsFrame2 σ Y b := ⟨⟨ε, hε⟩, t₀, ht₀⟩
  have hcm := hB.cm
  have hunr := hB.unram
  have hgood : (adCM σ χ).Good := hCM F E σ χ c hcm hunr hχ hres
  obtain ⟨-, -, -, ht2', hlc', hsc', hKc⟩ := hGT E (AE F E) (adCM σ χ) hgood (Fin n) ε
  let Φ := frameEquiv (Y := Y) χ ε b hε
  have hΓ : ∀ x, x ∈ rat2 σ Y ↔ Φ x ∈ (adCM σ χ).uΓ ε (Fin n) := rat_iff χ ε b hε
  have hKK : ∀ x, x ∈ K ↔ Φ x ∈ (adCM σ χ).uK ε (Fin n) := fun x => GlobalTheory.T.standard_compact_frame_equiv F E σ n Y hD hDI hcm χ ε b hε B K hK x
  have hIP : ∀ x, (∃ t, IsPar x t) ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := _root_.GlobalTheory.CompanionTheory.SiegelFrame.ParStab.exists_isPar_iff_mem_uQ F E σ n Y χ ε b hε t₀ ht₀
  have hPP : ∀ x, x ∈ par2 σ Y ↔ Φ x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
    intro x
    constructor
    · intro hx
      have : par2 σ Y ≤ ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))).comap Φ.toMonoidHom :=
        (Subgroup.closure_le _).2 fun p hp => (hIP p).1 hp
      exact this hx
    · intro hx
      exact Subgroup.subset_closure ((hIP x).2 hx)
  have hH := fun x => uH_eq hD hBd χ hgood ε b hε t₀ ht₀ K hKK a ha x
  have hiwa : Iwa ((adCM σ χ).uQ ε (Set.univ : Set (Fin n))) ((adCM σ χ).uK ε (Fin n)) := by
    intro y
    obtain ⟨p, t, hp, k, hk, e⟩ := ha.iwa (Φ.symm y)
    refine ⟨Φ p, (hIP p).1 ⟨t, hp⟩, Φ k, (hKK k).1 hk, ?_⟩
    rw [← map_mul, ← e, MulEquiv.apply_symm_apply]
  obtain ⟨-, hparU⟩ := hPar E (AE F E) (adCM σ χ) hgood (Fin n) ε (Set.univ : Set (Fin n))
  obtain ⟨hIP', hIH, -⟩ := hparU (by rwa [inf_idem])
  rw [inf_idem] at hIP'
  haveI := ht2'
  haveI := hlc'
  have hW := hSg F E σ χ c hcm hunr hχ hres ε (Fin n) (by simpa using hn) hiwa
  obtain ⟨σ₀, hσ₀⟩ := _root_.GlobalTheory.CompanionTheory.GodementH.godement_sum_k F E σ B n Y r s hB hn hY b K a hb' hK ha
  refine eis_from_U hSec hWL Φ (continuous_frameEquiv χ ε b hε) _ _ _ ((adCM σ χ).uC ε (Fin n))
    ((adCM σ χ).uH ε (Set.univ : Set (Fin n))) hKc hIP' hIH ?_ K a χ s₁ f hf hΓ hKK hPP hIP hH
    (continuous_frameEquiv_symm χ ε b hε) ?_ ⟨σ₀, fun σ' h => ?_⟩
  · simpa using hW
  · intro p t hp
    refine ⟨?_, ?_⟩
    · show (((adCM σ χ).χ (bdet (Sum.inl '' (Set.univ : Set (Fin n))) (frameEquiv χ ε b hε p).1) : Circle) : ℂ) = _
      rw [GlobalTheory.T.block_det_parabolic_frame F E σ n Y χ ε b hε t₀ ht₀ p t hp]
      rfl
    · have := ha.val p t hp 1 (one_mem _)
      rwa [mul_one] at this
  · obtain ⟨C, N, h⟩ := hσ₀ σ' h
    exact ⟨C, N, fun x => (h x).2⟩
end GlobalTheory.CompanionTheory.SiegelFrame
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisHalf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.SiegelEis GlobalTheory.CompanionTheory.EisHalf
namespace PositivityTheory.SiegelWeilFormula.Aeis
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem eis_half_plane_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (hH : IsHgt K a) (χ : Chr F E) (s₁ : ℂ)
    (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
      ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  have hKc : IsCompact (K : Set (G2 σ Y)) := _root_.PositivityTheory.SiegelWeilFormula.Aeis.isCompact_K_w_k hB hK
  obtain ⟨-, hpos⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.height_pos_w_k hB hK hH
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a hKc hH hpos χ s₁ f hf
  obtain ⟨σ₀, hσ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.godement_sum_w_k hB hb hK hH
  have hsum : ∀ σ' : ℝ, σ₀ < σ' → ∀ x : G2 σ Y,
      Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') := by
    intro σ' h x
    obtain ⟨_, _, h'⟩ := hσ σ' h
    exact (h' x).1
  have hterm : ∀ (z : ℂ) (x : G2 σ Y) (q : Cos σ Y),
      ‖eisTerm (flat a f s₁ z) x q‖ ≤ C * a ((Quotient.out q).1 * x) ^ (z.re + (n : ℝ) / 2) :=
    fun z x q => hC z _
  refine ⟨fun z x => ∑' q, eisTerm (flat a f s₁ z) x q, σ₀ - (n : ℝ) / 2, ?_, ?_⟩
  · intro z hz x
    have h1 : σ₀ < z.re + (n : ℝ) / 2 := by linarith
    exact (Summable.of_norm_bounded ((hsum _ h1 x).mul_left C) (hterm z x)).hasSum
  · intro x z hz
    have hz' : σ₀ - (n : ℝ) / 2 < z.re := hz
    obtain ⟨c, hc1, hc2⟩ := exists_between hz'
    set d : ℝ := z.re + 1 with hd
    have hopen : IsOpen {w : ℂ | c < w.re ∧ w.re < d} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hc3 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have hd3 : σ₀ < d + (n : ℝ) / 2 := by linarith
    have hu : Summable (fun q : Cos σ Y => |C| * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
        a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2))) :=
      ((hsum _ hc3 x).add (hsum _ hd3 x)).mul_left _
    have hdiff : ∀ q : Cos σ Y,
        DifferentiableOn ℂ (fun w : ℂ => eisTerm (flat a f s₁ w) x q) {w : ℂ | c < w.re ∧ w.re < d} :=
      fun q => (differentiable_cpow_term (hpos _) s₁ _).differentiableOn
    have hle : ∀ (q : Cos σ Y) (w : ℂ), w ∈ {w : ℂ | c < w.re ∧ w.re < d} →
        ‖eisTerm (flat a f s₁ w) x q‖ ≤ |C| * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
          a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2)) := by
      intro q w hw
      have hA := hpos ((Quotient.out q).1 * x)
      have h2 := rpow_le_add_rpow (u := w.re + (n : ℝ) / 2) (c := c + (n : ℝ) / 2)
        (d := d + (n : ℝ) / 2) hA (by linarith [hw.1]) (by linarith [hw.2])
      have h3 := Real.rpow_nonneg hA.le (w.re + (n : ℝ) / 2)
      calc _ ≤ C * a ((Quotient.out q).1 * x) ^ (w.re + (n : ℝ) / 2) := hterm w x q
        _ ≤ |C| * a ((Quotient.out q).1 * x) ^ (w.re + (n : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) h3
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    have hD := Complex.differentiableOn_tsum_of_summable_norm hu hdiff hopen hle
    have hmem : {w : ℂ | c < w.re ∧ w.re < d} ∈ 𝓝 z :=
      hopen.mem_nhds ⟨hc2, by rw [hd]; linarith⟩
    exact (hD.differentiableAt hmem).differentiableWithinAt
theorem eis_half_mod_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) (χ : Chr F E) (s₁ : ℂ)
    (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) →
      (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧
      ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨ac, a0⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.height_pos_w_k hB hK ha
  have kc := _root_.PositivityTheory.SiegelWeilFormula.Aeis.isCompact_K_w_k hB hK
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a kc ha a0 χ s₁ f hf
  obtain ⟨σ₀, hG⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.godement_sum_w_k hB hb hK ha
  obtain ⟨W, hW, h1W, hWa⟩ := exists_nhd_one kc ac ha a0
  refine ⟨σ₀ - n / 2, fun t Ê ht hE => ?_⟩
  have tb : ∀ (z : ℂ) (c c' : ℝ), c ≤ z.re → z.re ≤ c' → ∀ g,
      ‖flat a f s₁ z g‖ ≤ |C| * (a g ^ (c + (n : ℝ) / 2) + a g ^ (c' + (n : ℝ) / 2)) := fun z c c' h1 h2 g =>
    (hC z g).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_pos_of_pos (a0 g) _).le).trans
      (mul_le_mul_of_nonneg_left (rpow_le_add (a0 g) (by linarith) (by linarith)) (abs_nonneg C)))
  have gr : ∀ c c' : ℝ, t < c → ∃ (D : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ D * (ht2 x : ℝ) ^ N := by
    intro c c' hc
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < max c c' + (n : ℝ) / 2 := by linarith [le_max_left c c']
    obtain ⟨C₁, N₁, H₁⟩ := hG _ h1
    obtain ⟨C₂, N₂, H₂⟩ := hG _ h2
    refine ⟨|C| * (|C₁| + |C₂|), max N₁ N₂, fun z h1z h2z x => ?_⟩
    have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
    have S := (H₁ x).1.add (H₂ x).1
    have hs := (hE z (by linarith) x).norm_le_of_bounded (S.mul_left |C|).hasSum
      (fun q => tb z c (max c c') h1z (h2z.trans (le_max_right c c')) _)
    refine hs.trans ?_
    rw [tsum_mul_left, (H₁ x).1.tsum_add (H₂ x).1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    have p1 : (ht2 x : ℝ) ^ N₁ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_left _ _)
    have p2 : (ht2 x : ℝ) ^ N₂ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_right _ _)
    have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₁ := pow_nonneg (by linarith) _
    have q1 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₂ := pow_nonneg (by linarith) _
    rw [add_mul]
    exact add_le_add ((H₁ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q0).trans
        (mul_le_mul_of_nonneg_left p1 (abs_nonneg _))))
      ((H₂ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q1).trans (mul_le_mul_of_nonneg_left p2 (abs_nonneg _))))
  have ct : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) := by
    rintro ⟨z₀, x₀⟩ ⟨hz₀, -⟩
    have hz₁ : t < z₀.re := hz₀
    obtain ⟨c, hc1, hc2⟩ := exists_between hz₁
    obtain ⟨c', hc'⟩ := exists_gt z₀.re
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < c' + (n : ℝ) / 2 := by linarith
    obtain ⟨_, _, H₁⟩ := hG _ h1
    obtain ⟨_, _, H₂⟩ := hG _ h2
    let V : Set (G2 σ Y) := (fun x => x₀⁻¹ * x) ⁻¹' W
    have hV : IsOpen V := hW.preimage (continuous_const.mul continuous_id)
    let S : Set (ℂ × G2 σ Y) := {z : ℂ | c < z.re ∧ z.re < c'} ×ˢ V
    have hS : IsOpen S :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)).prod hV
    have mS : (z₀, x₀) ∈ S := ⟨⟨hc2, hc'⟩, by simpa [V] using h1W⟩
    have sumU : Summable fun q : Cos σ Y => |C| *
        (2 ^ |c + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c + (n : ℝ) / 2) +
          2 ^ |c' + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c' + (n : ℝ) / 2)) :=
      (((H₁ x₀).1.mul_left _).add ((H₂ x₀).1.mul_left _)).mul_left _
    have cts : ContinuousOn (fun y : ℂ × G2 σ Y => ∑' q : Cos σ Y, eisTerm (flat a f s₁ y.1) y.2 q) S := by
      refine continuousOn_tsum (fun q => Continuous.continuousOn ?_) sumU ?_
      · have cg : Continuous fun y : ℂ × G2 σ Y => (Quotient.out q).1 * y.2 := continuous_const.mul continuous_snd
        exact ((Complex.continuous_ofReal.comp (ac.comp cg)).cpow (continuous_fst.sub continuous_const)
          fun y => Complex.ofReal_mem_slitPlane.2 (a0 _)).mul (hf.cont.comp cg)
      · rintro q ⟨z, x⟩ ⟨⟨hz1, hz2⟩, hx⟩
        have hu := hWa ((Quotient.out q).1 * x₀) (x₀⁻¹ * x) hx
        rw [show (Quotient.out q).1 * x₀ * (x₀⁻¹ * x) = (Quotient.out q).1 * x by group] at hu
        exact (tb z c c' hz1.le hz2.le _).trans (mul_le_mul_of_nonneg_left (add_le_add
          (rpow_le_of_near (a0 _) hu.1 hu.2 _) (rpow_le_of_near (a0 _) hu.1 hu.2 _)) (abs_nonneg C))
    have ctE : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) S :=
      cts.congr fun y hy => (hE y.1 (hc1.trans hy.1.1) y.2).tsum_eq.symm
    exact (ctE.continuousAt (hS.mem_nhds mS)).continuousWithinAt
  refine ⟨fun z hz => ?_, ct, gr⟩
  obtain ⟨D, N, hD⟩ := gr z.re z.re hz
  have cz : Continuous fun x => Ê z x :=
    ct.comp_continuous (Continuous.prodMk_right z) fun x => ⟨hz, trivial⟩
  have M1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have M0 : (0 : ℝ) < max D 1 := by linarith
  have Mc : ((max D 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 M0.ne'
  have e : (fun x => Ê z x) = ((max D 1 : ℝ) : ℂ) • ((((max D 1 : ℝ) : ℂ))⁻¹ • fun x => Ê z x) := by
    rw [smul_smul, mul_inv_cancel₀ Mc, one_smul]
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨cz.const_smul _, N, fun x => ?_⟩)
  have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
  have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N := pow_nonneg (by linarith) _
  rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg M0.le, inv_mul_le_iff₀ M0]
  exact (hD z le_rfl le_rfl x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) q0)
theorem eisHalf_w_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) (χ : Chr F E) (s₁ : ℂ)
    (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ (t : ℝ) (v : ℂ → modFun σ Y), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) ((v s).1 x)) ∧
      WHolo (growForms σ Y) v {s | t < s.re} := by
  obtain ⟨Ê, t, hsum, hhol⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eis_half_plane_w_k hB hb hK ha χ s₁ f hf
  obtain ⟨t₀, hmod⟩ := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eis_half_mod_w_k hB hb hK ha χ s₁ f hf
  obtain ⟨t', ht, ht₀⟩ : ∃ t' : ℝ, t ≤ t' ∧ t₀ ≤ t' := ⟨max t t₀, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ s : ℂ, t' < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x) :=
    fun s hs => hsum s (lt_of_le_of_lt ht hs)
  obtain ⟨hmem, hcont, hbd⟩ := hmod t' Ê ht₀ hsum'
  classical
  let v : ℂ → modFun σ Y := fun s => if h : t' < s.re then ⟨fun x => Ê s x, hmem s h⟩ else 0
  have hv : ∀ s : ℂ, t' < s.re → ∀ x, (v s).1 x = Ê s x := by
    intro s h x
    simp only [v, dif_pos h]
  refine ⟨t', v, fun s h x => by rw [hv s h x]; exact hsum' s h x, ?_⟩
  have hS : IsOpen {s : ℂ | t' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS ?_ ?_ ?_
  · intro x
    exact ((hhol x).mono fun s hs => lt_of_le_of_lt ht hs).congr fun s hs => hv s hs x
  · refine hcont.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    exact hv s hs x
  · intro Q hQ hQc
    rcases Q.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 0, by simp⟩
    obtain ⟨z₁, hz₁, hmin⟩ := hQc.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨z₂, -, hmax⟩ := hQc.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨C, N, h⟩ := hbd z₁.re z₂.re (hQ hz₁)
    refine ⟨C, N, fun s hs x => ?_⟩
    rw [hv s (hQ hs) x]
    exact h s (hmin hs) (hmax hs) x
end PositivityTheory.SiegelWeilFormula.Aeis
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadLt
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.Khead
theorem siegelWeilStd_lt_k (h : _root_.PositivityTheory.SiegelWeilFormula.SWStdLt_k) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n) r s r' s', n < m → _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n →
    min r s = 0 → (A.IsHerm σ B r s ∧ Y.IsSkew σ B r' s' ∨ A.IsSkew σ B r s ∧ Y.IsHerm σ B r' s') →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
    ∀ (κ : Type) [Fintype κ] dd om S l, IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) B.ψ dd χ om S l →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a →
    ∀ (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ A.J) D μ →
    ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => om k.1 Φ)) →
      EisValueAt (flat a (fun x => l (om x Φ)) (((m : ℂ) - n) / 2)) (((m : ℂ) - n) / 2)
        fun x => (if n < m then 1 else 2) * ⨍ g in D, thetaSum F (om x (S g Φ)) ∂μ := by
  intro F E _ _ _ _ _ σ B m n A Y r s r' s' hlt h1 h2 h3 h4 h5 χ h6 h7 κ _ dd om S l h8 b K a h9 h10 h11 μ D h12 h13 Φ h14 h15
  simp only [if_pos hlt, one_mul]
  exact h F E σ B m n A Y r s r' s' χ κ dd om S l b K a μ D Φ
    ⟨h1, h2, h3, hlt, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
end PositivityTheory.SiegelWeilFormula.Khead
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexaEv
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
set_option linter.unusedSectionVars false
theorem sEv_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.SEv_k := by
  intro F E _ _ _ _ _ σ B bs m n A Y b ε r s hB hm hn hsg hb hε dd hd
  refine ⟨adelicCoordinatesEvalZeroForm_mem_admissible _, fun z Φ _ => evaluation_zero_unipotent_kill bs A Y b hb dd hd B.ψ z Φ, fun Φ hΦ => ?_⟩
  have hψ : ∀ x : F, B.ψ (algebraMap F (AF F) x) = 1 := hB.std.2.1
  have hs := (summable_of_mem_schA F hΦ).hasSum
  have h := (Equiv.hasSum_iff (xiEquiv (m := m) bs b hb)).mpr hs
  have e1 : thetaSum F Φ = ∑' ξ : Fin m × Fin n × Fin 2 → F, Φ fun i => algebraMap F (AF F) (ξ i) := rfl
  rw [e1]
  convert h using 1
  funext y
  exact evaluation_zero_antisymmetric bs A Y b hb dd hd B.ψ hψ Φ y
end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilLdexbUnit
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_skewUnit_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) :
    ∃ r : (AE F E)ˣ, cA σ (r : AE F E) = -(r : AE F E) ∧
      (∀ v, compFin F E v (r : AE F E) ∈ intLoc F E v ∧ compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) ∈ intLoc F E v) ∧
      ∀ w, ‖piInf (B.emb w) (r : AE F E)‖ = 1 := by
  classical
  have hc := hB.cm
  obtain ⟨ξ, hξ, hσξ⟩ := UnitA.exists_xi hc
  obtain ⟨S, hS⟩ := UnitA.exists_S (F := F) ξ
  choose u hu1 hu2 hu3 using _root_.UpperTheory.TP.K.exists_locUnit hB hξ hσξ
  let xv : ∀ v : Pl F, (Fv F v ⊗[F] E)ˣ := fun v =>
    ⟨inclR (F := F) (Fv F v) ξ, inclR (F := F) (Fv F v) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let b : ∀ v : Pl F, GL (Fin 1) (Fv F v ⊗[F] E) := fun v => if v ∈ S then sc1 (u v * (xv v)⁻¹) else 1
  have hb : ∀ v ∉ S, b v = 1 := fun v hv => if_neg hv
  let e : ∀ w : InfinitePlace F, w.Completion ⊗[F] E ≃+* ℂ := fun w =>
    RingEquiv.ofBijective (infEmb (B.emb w)) (infEmb_bijective hc (B.emb w))
  have hτ : ∀ w : InfinitePlace F, (B.emb w).1 ξ ≠ 0 := fun w => (map_ne_zero _).2 hξ
  let c : ∀ w : InfinitePlace F, GL (Fin 1) (w.Completion ⊗[F] E) := fun w =>
    sc1 (Units.map (e w).symm.toMonoidHom (Units.mk0 (Complex.I / (B.emb w).1 ξ) (div_ne_zero Complex.I_ne_zero (hτ w))))
  obtain ⟨γ, hγf, hγi⟩ := Frames.exists_GL_of_components S b hb c
  let X : (AE F E)ˣ := ⟨inclR (F := F) (AF F) ξ, inclR (F := F) (AF F) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let r : (AE F E)ˣ := Matrix.GeneralLinearGroup.det γ * X
  have hf : ∀ v, Units.map (compFin F E v).toMonoidHom r = if v ∈ S then u v else xv v := by
    intro v
    have hX : Units.map (compFin F E v).toMonoidHom X = xv v := Units.ext (UnitA.compFin_inclR v ξ)
    rw [map_mul, map_det_bc, hγf v, hX]
    by_cases hv : v ∈ S
    · simp only [b, if_pos hv, det_sc1, inv_mul_cancel_right]
    · simp only [b, if_neg hv, map_one, one_mul]
  have hfv : ∀ v, compFin F E v (r : AE F E) = ((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v]; rfl
  have hfi : ∀ v, compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) =
      (((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v, ← map_inv]; rfl
  have hi : ∀ w, infEmb (B.emb w) (compInf F E w (r : AE F E)) = Complex.I := by
    intro w
    have hX : Units.map (compInf F E w).toMonoidHom X = Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) :=
      Units.ext (UnitA.compInf_inclR w ξ)
    have h1 : Units.map (compInf F E w).toMonoidHom r = Matrix.GeneralLinearGroup.det (c w) *
        Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) := by
      rw [map_mul, map_det_bc, hγi w, hX]
    have h2 : compInf F E w (r : AE F E) = (e w).symm (Complex.I / (B.emb w).1 ξ) * inclR (F := F) w.Completion ξ := by
      have := congrArg Units.val h1
      simpa [c, det_sc1] using this
    rw [h2, map_mul]
    have h3 : infEmb (B.emb w) ((e w).symm (Complex.I / (B.emb w).1 ξ)) = Complex.I / (B.emb w).1 ξ :=
      (e w).apply_symm_apply _
    have h4 : infEmb (B.emb w) (inclR (F := F) w.Completion ξ) = (B.emb w).1 ξ := by
      change infEmb (B.emb w) ((1 : w.Completion) ⊗ₜ[F] ξ) = _
      rw [infEmb_tmul, map_one, one_mul]
    rw [h3, h4, div_mul_cancel₀ _ (hτ w)]
  refine ⟨r, ?_, fun v => ?_, fun w => ?_⟩
  ·
    have key : -(cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E)) = 1 := by
      refine GlobalTheory.AdelicU.Supp.adTens_eq_one' (fun w => ?_) (fun v => ?_)
      · have hz : sigR w.Completion σ (compInf F E w (r : AE F E)) = -compInf F E w (r : AE F E) := by
          apply (e w).injective
          change infEmb (B.emb w) _ = infEmb (B.emb w) _
          rw [← infEmb_sigR hc, hi w, map_neg, hi w, Complex.conj_I]
        have hu : compInf F E w (r : AE F E) * compInf F E w ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compInf_cA, hz, neg_mul, neg_neg, hu]
      · have hz : sigR (Fv F v) σ (compFin F E v (r : AE F E)) = -compFin F E v (r : AE F E) := by
          rw [hfv v]
          by_cases hv : v ∈ S
          · simp only [if_pos hv]; exact hu3 v
          · simp only [if_neg hv, xv]
            rw [UnitA.sigR_inclR, hσξ, map_neg]
        have hu : compFin F E v (r : AE F E) * compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compFin_cA, hz, neg_mul, neg_neg, hu]
    have : cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) = -1 := by
      rw [← neg_neg (cA σ (r : AE F E) * _), key]
    calc cA σ (r : AE F E) = cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) * (r : AE F E) := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = -(r : AE F E) := by rw [this, neg_one_mul]
  · rw [hfv v, hfi v]
    by_cases hv : v ∈ S
    · simp only [if_pos hv]; exact ⟨hu1 v, hu2 v⟩
    · simp only [if_neg hv]; exact hS v hv
  · change ‖infEmb (B.emb w) (compInf F E w (r : AE F E))‖ = 1
    rw [hi w, Complex.norm_I]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.StandardAdditiveCharacterSign
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_additive_character_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  first | exact @_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k | exact _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k | (intros; apply _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k <;> assumption)
end
end

