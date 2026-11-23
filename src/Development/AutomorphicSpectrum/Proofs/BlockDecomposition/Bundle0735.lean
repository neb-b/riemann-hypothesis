module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0733
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0726
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0713
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0729
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0730
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCosetsParamRational
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0731
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0732
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBlockInvertibleCriterion
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeSchurOrthogonality
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

private theorem avg_conj_coef_ge_lemma {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(ρ g : B →ₗ[ℂ] B), hρ.norm g⟩ : B →ₗᵢ[ℂ] B).inner_map_map x y

private theorem avg_conj_coef_ge_lemma_2 {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g h : Γ) (x : B) : ρ g (ρ h x) = ρ (g * h) x := by
  rw [hρ.mul]; rfl

private theorem avg_conj_coef_ge_lemma_3 {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g : Γ) (x y : B) : ⟪ρ g x, y⟫_ℂ = ⟪x, ρ g⁻¹ y⟫_ℂ := by
  have e : y = ρ g (ρ g⁻¹ y) := by
    rw [avg_conj_coef_ge_lemma_2 hρ, mul_inv_cancel, hρ.one]; rfl
  conv_lhs => rw [e]
  exact avg_conj_coef_ge_lemma hρ g x _

theorem avg_conj_coef_ge : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ) (hρ : IsU ρ), IsFd ν σ d →
    ∀ w₀ : A, ‖w₀‖ = 1 → ∀ (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (i : A →L[ℂ] B), IsIsoMap σ ρ i → ∀ z : B,
    ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc z⟫_ℂ).re := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hFd w₀ hw₀ hc i hi z
  obtain ⟨hd, hFd'⟩ := hFd
  have hmap : ∀ g x, i (σ g x) = ρ g (i x) := hi.1
  have hiso : ∀ x, ‖i x‖ = ‖x‖ := hi.2
  set f : Γ → ℂ := fun g => star ⟪w₀, σ g w₀⟫_ℂ with hf
  set T := coefOp ν ρ hρ f hc with hT
  have hw1 : ⟪w₀, w₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw₀]; simp
  set a := ContinuousLinearMap.adjoint i z with ha
  have hA : ⟪i w₀, T z⟫_ℂ = ⟪i w₀, z⟫_ℂ / (d : ℂ) := by
    rw [hT, inner_coefOp]
    have hpt : ∀ g, f g * ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ := by
      intro g
      have e1 : ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ := by
        calc ⟪i w₀, ρ g z⟫_ℂ = ⟪ρ g⁻¹ (i w₀), z⟫_ℂ := by
              rw [avg_conj_coef_ge_lemma_3 hρ, inv_inv]
          _ = ⟪i (σ g⁻¹ w₀), z⟫_ℂ := by rw [hmap]
          _ = ⟪σ g⁻¹ w₀, a⟫_ℂ := by rw [ha, ContinuousLinearMap.adjoint_inner_right]
          _ = ⟪w₀, σ g a⟫_ℂ := by rw [avg_conj_coef_ge_lemma_3 hσ, inv_inv]
      rw [e1, hf, mul_comm]
    simp_rw [hpt]
    rw [(hFd' a w₀ w₀ w₀).2, hw1, mul_one, ha, ContinuousLinearMap.adjoint_inner_right]
  have hB1 : ∀ g, ⟪ρ g z, T z⟫_ℂ = ∫ k, f (g * k) * ⟪z, ρ k z⟫_ℂ ∂ν := by
    intro g
    rw [hT, inner_coefOp]
    have e : ∀ h, f h * ⟪ρ g z, ρ h z⟫_ℂ = f (g * (g⁻¹ * h)) * ⟪z, ρ (g⁻¹ * h) z⟫_ℂ := by
      intro h
      rw [mul_inv_cancel_left, avg_conj_coef_ge_lemma_3 hρ, avg_conj_coef_ge_lemma_2 hρ]
    simp_rw [e]
    exact integral_mul_left_eq_self (fun k => f (g * k) * ⟪z, ρ k z⟫_ℂ) g⁻¹
  set φ : Γ → ℂ := fun k => ⟪z, ρ k z⟫_ℂ with hφ
  have hfc : Continuous f := (continuous_const.inner (hσ.cont w₀)).star
  have hφc : Continuous φ := continuous_const.inner (hρ.cont z)
  have hφb : ∀ k, ‖φ k‖ ≤ ‖z‖ ^ 2 := by
    intro k
    calc ‖φ k‖ ≤ ‖z‖ * ‖ρ k z‖ := norm_inner_le_norm _ _
      _ = ‖z‖ ^ 2 := by rw [hρ.norm, sq]
  have hcs : Integrable (fun g => star (f g)) ν :=
    hc.mono (hfc.star.aestronglyMeasurable) (ae_of_all _ fun g => by rw [norm_star])
  have hG : Integrable (fun p : Γ × Γ => f p.1 * star (f (p.1 * p.2))) (ν.prod ν) := by
    have h0 : Integrable (fun p : Γ × Γ => f p.1 * star (f p.2)) (ν.prod ν) := hc.mul_prod hcs
    exact (measurePreserving_prod_mul ν ν).integrable_comp_of_integrable h0
  have hF : Integrable (Function.uncurry fun g k => f g * (star (f (g * k)) * star (φ k))) (ν.prod ν) := by
    refine Integrable.mono' (hG.norm.mul_const (‖z‖ ^ 2)) ?_ (ae_of_all _ fun p => ?_)
    · exact (show Continuous (fun p : Γ × Γ => f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))) from
        (hfc.comp continuous_fst).mul (((hfc.comp (continuous_fst.mul continuous_snd)).star).mul
          ((hφc.comp continuous_snd).star))).aestronglyMeasurable
    · show ‖f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))‖ ≤ ‖f p.1 * star (f (p.1 * p.2))‖ * ‖z‖ ^ 2
      simp only [norm_mul, norm_star]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hφb _) (norm_nonneg _)) (norm_nonneg _)
  have hinner : ∀ k, ∫ g, f g * star (f (g * k)) ∂ν = star (f k) / (d : ℂ) := by
    intro k
    have e : ∀ g, f g * star (f (g * k)) = ⟪w₀, σ g (σ k w₀)⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ := by
      intro g
      simp only [hf, star_star]
      rw [← avg_conj_coef_ge_lemma_2 hσ]
      ring
    simp_rw [e]
    rw [(hFd' (σ k w₀) w₀ w₀ w₀).2, hw1, mul_one]
    simp only [hf, star_star]
  have hB2 : ⟪T z, T z⟫_ℂ = star ⟪z, T z⟫_ℂ / (d : ℂ) := by
    have s1 : ⟪T z, T z⟫_ℂ = ∫ g, f g * ⟪T z, ρ g z⟫_ℂ ∂ν := inner_coefOp ν ρ hρ f hc (T z) z
    have s2 : ∀ g, f g * ⟪T z, ρ g z⟫_ℂ = ∫ k, f g * (star (f (g * k)) * star (φ k)) ∂ν := by
      intro g
      rw [← inner_conj_symm, hB1 g, ← integral_conj, ← integral_const_mul]
      simp only [map_mul, starRingEnd_apply, hφ]
    have s3 : ∀ k, ∫ g, f g * (star (f (g * k)) * star (φ k)) ∂ν = star (f k) / (d : ℂ) * star (φ k) := by
      intro k
      simp_rw [← mul_assoc]
      rw [integral_mul_const, hinner k]
    have s4 : ⟪z, T z⟫_ℂ = ∫ k, f k * φ k ∂ν := inner_coefOp ν ρ hρ f hc z z
    have s5 : ∀ k, star (f k) / (d : ℂ) * star (φ k) = (starRingEnd ℂ) (f k * φ k) / (d : ℂ) := by
      intro k
      rw [map_mul, starRingEnd_apply, starRingEnd_apply]
      ring
    rw [s1]
    simp_rw [s2]
    rw [integral_integral_swap hF]
    simp_rw [s3, s5]
    rw [integral_div, integral_conj, ← s4, starRingEnd_apply]
  have hTn : ⟪T z, T z⟫_ℂ = ((‖T z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hX : star ⟪z, T z⟫_ℂ = ((d * ‖T z‖ ^ 2 : ℝ) : ℂ) := by
    have h := hB2.symm.trans hTn
    rw [div_eq_iff hdC] at h
    rw [h]
    push_cast
    ring
  have hre : (⟪z, T z⟫_ℂ).re = d * ‖T z‖ ^ 2 := by
    have h := congrArg Complex.re hX
    rw [Complex.ofReal_re] at h
    rw [← h]
    exact (Complex.conj_re _).symm
  have hle : ‖⟪z, i w₀⟫_ℂ‖ ≤ d * ‖T z‖ := by
    have h1' : ‖⟪i w₀, T z⟫_ℂ‖ ≤ ‖T z‖ := by
      calc ‖⟪i w₀, T z⟫_ℂ‖ ≤ ‖i w₀‖ * ‖T z‖ := norm_inner_le_norm _ _
        _ = ‖T z‖ := by rw [hiso, hw₀, one_mul]
    have h2' : ‖⟪z, i w₀⟫_ℂ‖ = d * ‖⟪i w₀, T z⟫_ℂ‖ := by
      rw [hA, norm_div, norm_inner_symm, Complex.norm_real, Real.norm_of_nonneg hd.le]
      field_simp
    rw [h2']
    exact mul_le_mul_of_nonneg_left h1' hd.le
  rw [hre, div_le_iff₀ hd]
  have hsq : ‖⟪z, i w₀⟫_ℂ‖ ^ 2 ≤ (d * ‖T z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  nlinarith [hsq]

end GlobalTheory.CompanionTheory.RgHeA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf
open GlobalTheory.Eis

variable {D : D7} {n ρ p : ℕ}

theorem chz_add (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    chz ψ b₀ (a + b) = chz ψ b₀ a * chz ψ b₀ b := by
  simp only [chz, AddSubgroup.coe_add]
  rw [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.HermPoisson.halfTr_add', AddChar.map_add_eq_mul]

theorem chz_norm {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (a : hermA D ρ) :
    ‖chz ψ b₀ a‖ = 1 := hψ.2.1 _

theorem chz_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) : Continuous (chz ψ b₀) :=
  GlobalTheory.CompanionTheory.HermPoisson.continuous_chi hψ (b₀.1.map (incA D) : Mx D ρ ρ)

theorem chz_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (l : ratHerm D ρ) :
    chz ψ b₀ l.1 = 1 :=
  GlobalTheory.CompanionTheory.HermPoisson.chi_rat hψ (m := (b₀.1.map (incA D) : Mx D ρ ρ)) ⟨b₀.1, rfl⟩ l

theorem continuous_jacobi_map_zero {hn : ρ + p = n} (M : Maps D hn) : Continuous fun z : hermA D ρ => M.nzx z 0 :=
  M.nzx_cont.comp (continuous_id.prodMk continuous_const)


set_option maxHeartbeats 1600000 in
theorem unfold_on {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {b₀ : HermE D ρ} (hb₀ : b₀.1.det ≠ 0) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {s : ℂ} {f : G D n → ℂ}
    (hf : Continuous f) (hl : IsLaw χ s f) (hs : (n : ℝ) / 2 < s.re) (C : Set (G D n)) (hC : IsCompact C) :
    ∃ Um : Cosets (P D n) (GF D n) → ℝ, Summable Um ∧
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧ ∀ g ∈ C,
      (∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ ∑' l : ratHerm D ρ, Um (e (l, u))) ∧
      HasSum (fun u : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E =>
        Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)) (zc M m ψ b₀ (eisS f) g) := by
  obtain ⟨hinv, hdet, hmaj⟩ := _root_.GlobalTheory.CompanionTheory.ZUnf.law_facts hχ hf hl hs
  obtain ⟨hHaar, hFD, hvol⟩ := m.hz
  obtain ⟨hadd, hcsh, hcem, hrat⟩ := _root_.GlobalTheory.CompanionTheory.ZUnf.centre_nzx M
  have hcolat := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := ρ)
  haveI : Countable (ratHerm D ρ) := countable_ratHerm
  haveI : Countable (Cosets (P D n) (GF D n)) := countable_cosets
  haveI : Countable (Cosets (P D p) (GF D p)) := countable_cosets
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) := countable_mat ρ p
  obtain ⟨e, he, hfib, hτe, hterm⟩ := _root_.GlobalTheory.CompanionTheory.ZUnf.CellGlue.cell hn M
  obtain ⟨K0, hK0, hKc⟩ := hcolat.2
  have hcn := continuous_jacobi_map_zero M
  obtain ⟨Um, hUm, hub⟩ := hmaj ((fun d : hermA D ρ × G D n => M.nzx d.1 0 * d.2) '' (K0 ×ˢ C))
    ((hK0.prod hC).image ((hcn.comp continuous_fst).mul continuous_snd))
  refine ⟨Um, hUm, e, he, fun g hg => ?_⟩
  let F : Cosets (P D n) (GF D n) → hermA D ρ → ℂ := fun q b => term (P D n) (GF D n) f (M.nzx b 0 * g) q
  let F0 : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → hermA D ρ → ℂ := fun u z =>
    f (M.w * M.nzx z 0 * (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g))
  let ch : hermA D ρ → ℂ := fun b => conj (chz ψ b₀ b)
  let τ : ratHerm D ρ → Cosets (P D n) (GF D n) ≃ Cosets (P D n) (GF D n) := fun l =>
    rmulEquiv _ _ ⟨M.nzx l.1 0, (hrat l).1⟩
  have hτ : ∀ (l : ratHerm D ρ) q b, F q ((l : hermA D ρ) + b) = F (τ l q) b := fun l q b => by
    simp only [F]
    rw [hadd, mul_assoc]
    exact term_mul_left hinv ⟨M.nzx l.1 0, (hrat l).1⟩ _ q
  have hchc : Continuous ch := Complex.continuous_conj.comp (chz_cont hψ b₀)
  have hF : ∀ q, Continuous (F q) := fun q =>
    hf.comp (continuous_const.mul (hcn.mul continuous_const))
  have hF0 : ∀ (l : ratHerm D ρ) u b, F (e (l, u)) b = F0 u ((l : hermA D ρ) + b) := fun l u b => by
    simp only [F, F0]
    rw [hterm f hinv, hadd]
    congr 1
    have h1 : M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * (M.nzx b 0 * g) =
        M.nzx b 0 * (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g) := by
      rw [← mul_assoc, mul_assoc (M.sh _), ← hcem, ← mul_assoc, ← hcsh]
      simp only [mul_assoc]
    simp only [mul_assoc] at h1 ⊢
    rw [h1]
  have key := _root_.GlobalTheory.CompanionTheory.UnfoldFam.unfold_fam m.lz (ratHerm D ρ) m.𝓖 hFD hvol
    (fun q : Cosets (P D n) (GF D n) => zKer hn (ratOf q.out)) (⊥ : Submodule D.host.E (Fin ρ → D.host.E)) F F0 ch
    (fun q => (hF q).aestronglyMeasurable) hchc.aestronglyMeasurable
    (fun b => by simp only [ch, RCLike.norm_conj]; exact chz_norm hψ b₀ b)
    (fun a b => by simp only [ch]; rw [chz_add, map_mul])
    (fun l => by simp only [ch]; rw [chz_rat hψ b₀ l, map_one])
    Um hUm τ hτ
    (fun l q => by
      obtain ⟨ζ, -, hζ⟩ := (hrat l).2
      have := GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv (D := D) (n := n) q ⟨M.nzx l.1 0, (hrat l).1⟩ (bl hn ζ 0 0 0) hζ
      change (cosetCell (τ l q)).comap (zinc hn) = (cosetCell q).comap (zinc hn)
      rw [show cosetCell (τ l q) = cosetCell q from this])
    (fun b => by
      obtain ⟨γ, hγ, hb⟩ := hKc b
      refine ⟨-⟨γ, hγ⟩, fun q => ?_⟩
      have h1 := hτ (-⟨γ, hγ⟩) q (γ + b)
      have h2 : (((-⟨γ, hγ⟩ : ratHerm D ρ) : hermA D ρ) + (γ + b)) = b := by simp
      rw [h2] at h1
      rw [h1]
      exact hub _ _ ⟨(γ + b, g), ⟨hb, hg⟩, rfl⟩)
    e he hfib (fun l l' u => hτe l l' u (hrat l').1) hF0
    (fun y hy => by
      obtain ⟨ν, hν1, hν⟩ := _root_.GlobalTheory.CompanionTheory.ZUnf.SmallZ.small hn hψ b₀ hb₀ y hy
      refine ⟨ν, ?_, fun q hq b => ?_⟩
      · intro h
        apply hν1
        have := congrArg (starRingEnd ℂ) h
        simpa [ch] using this
      · obtain ⟨x, hxP, a, ha, hd, hpe⟩ : ∃ x ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat x) = a.1 ∧
            Matrix.GeneralLinearGroup.det a = 1 ∧ (q.out : G D n) * M.nzx ν 0 = x * (q.out : G D n) := by
          obtain ⟨x, hx, a, ha, hd, hpe⟩ := hν (q.out : GF D n) (M.nzx ν 0) (q.out : GF D n).2 (ratOf q.out) (mat_ratOf _) hq
            (by rw [M.nzx_mat, adj_zero])
          exact ⟨x, hx, a, ha, hd, hpe⟩
        simp only [F, term]
        rw [hadd, mul_assoc (M.nzx ν 0), ← mul_assoc _ (M.nzx ν 0), hpe, mul_assoc, hdet x hxP a ha hd])
  refine ⟨fun u => ?_, ?_⟩
  · obtain ⟨hi, hle⟩ := key.1 u
    refine le_trans ?_ hle
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [F0, norm_mul, RCLike.norm_conj, chz_norm hψ b₀, mul_one]
  · exact key.2

theorem zUnfold : ZUnfold := by
  intro D n ρ p hn M m ψ hψ b₀ hb₀ χ hχ s f hf hl hs g
  refine ⟨?_, fun C hC => ?_⟩
  · obtain ⟨Um, -, e, -, h⟩ := unfold_on M m hψ hb₀ hχ hf hl hs {g} isCompact_singleton
    exact (h g rfl).2
  · obtain ⟨Um, hUm, e, he, h⟩ := unfold_on M m hψ hb₀ hχ hf hl hs C hC
    refine ⟨fun u => ∑' l : ratHerm D ρ, Um (e (l, u)), ?_, fun g hg u => (h g hg).1 u⟩
    have h1 : Summable (fun x : (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) × ratHerm D ρ => Um (e (x.2, x.1))) :=
      hUm.comp_injective (he.comp Prod.swap_injective)
    exact h1.prod

end GlobalTheory.CompanionTheory.ZUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientOrthogonalityRelation
section
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeA

theorem isInvInvariant_of_right_haar {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  haveI : IsFiniteMeasureOnCompacts μ.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.inv = c • μ := ⟨_, Measure.isMulLeftInvariant_eq_smul μ.inv μ⟩
  have hsq : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by rw [Measure.inv_def, Measure.inv_def, Measure.map_smul c measurable_inv.aemeasurable]
      _ = (c * c) • μ := by rw [hc, smul_smul]
  let K := Classical.arbitrary (TopologicalSpace.PositiveCompacts G)
  have hpos : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hK : μ K = ((c * c) • μ) K := by rw [← hsq]
  rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at hK
  have h1 : ((c * c : NNReal) : ENNReal) = 1 :=
    ((ENNReal.mul_left_inj hpos hfin).1 (by rw [one_mul]; exact hK.symm))
  have hcc : (c : ℝ) * c = 1 := by exact_mod_cast ENNReal.coe_eq_one.1 h1
  have hc1 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
    exact_mod_cast this
  exact ⟨by rw [hc, hc1, one_smul]⟩

theorem isSelfAdjoint_coefOp : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ), IsU ρ → ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    IsSelfAdjoint (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ hσ hρ v hm
  haveI := GlobalTheory.CompanionTheory.RgHeA.isInvInvariant_of_right_haar ν
  obtain ⟨_, hadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hσ
  obtain ⟨_, hρadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hρ
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro a b
  try simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, ← integral_conj]
  calc ∫ g, (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) ∂ν
      = ∫ g, star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        have e1 : star ⟪v, ρ g⁻¹ v⟫_ℂ = ⟪v, ρ g v⟫_ℂ := by
          rw [← hρadj]
          exact inner_conj_symm _ _
        have e2 : (starRingEnd ℂ) ⟪b, σ g a⟫_ℂ = ⟪a, σ g⁻¹ b⟫_ℂ := by
          rw [inner_conj_symm, hadj]
        show (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) = star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ
        rw [map_mul, e1, e2, starRingEnd_apply, star_star]
    _ = ∫ g, star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ ∂ν :=
        integral_inv_eq_self (fun g => star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ) ν

end GlobalTheory.CompanionTheory.RgHeA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfAllOfModels
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.SpreadingModels

theorem perfAll_of_models
    (hBase : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {Y₀ Y : Scheme.{0}}
      (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (f : Y ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Y₀),
      IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ)) → ∀ (M₀ : LB Y₀), M₀.IsLB → Perf f₀ M₀ →
        Nonempty (Perf f (M₀.pull π)))
    (hIso : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M M' : LB Y},
      M.IsLB → M'.IsLB → ∀ (w : LB.Iso M M'), w.IsGen → Perf f M' → Nonempty (Perf f M))
    (hModel : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → HasModel f M) : PerfAll := by
  intro R _ Y f hs hp M hM
  obtain ⟨R₀, _, _, φ, Y₀, f₀, π, hp₀, hf₀, hsq, M₀, hM₀, w, hw⟩ := hModel R Y f hs hp M hM
  haveI := hp₀
  haveI := hf₀
  obtain ⟨P₀⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f₀ hM₀
  obtain ⟨P⟩ := hBase φ f₀ f π hsq M₀ hM₀ P₀
  exact hIso f hM (Geo.Tor.pull_isLB hM₀ π) w hw P

end GlobalTheory.CompanionTheory.SpreadingModels
end

