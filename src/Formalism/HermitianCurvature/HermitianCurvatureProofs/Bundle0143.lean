module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0139
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactZetaLe

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermStep
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem germ_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (P' : ℝ) (hP' : GSup S ε b (n - 1) P')
    (hP'0 : 0 ≤ P') (w' : S.W) (hw' : w' ∈ S.base.Wall) (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop)
    (La : Submodule ℤ (crystallineComparison.V S.f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (hsm : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) :
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ (z₀ : crystallineComparison.V S.f) (Ss : Finset (crystallineComparison.V S.f)), (∀ z ∈ Ss, z - z₀ ∈ La) → (∀ z ∈ Ss, Good z) →
          ZLattice.covolume La * ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re ≤
            (∏ _v : Fin S.f, KB.dlB S b n) *
              ((∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) * P') *
              ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ := by
  have hk : n * C.Kst = (n - 1) * C.Kst + C.Kst := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [add_mul, one_mul]
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  set L : Fin S.f → ℝ := fun v => Λ b (n - 1) v with hLdef
  have hL0 : ∀ v, 0 ≤ L v := fun v => hΛ0 b (n - 1) hb (by omega) (by omega) v

  obtain ⟨θL, hθL, hLV⟩ := Formalism.FourierDecayAlt.P.lift_bound_below_top_all_places E Wp Wq S Λ hpos hLL ε hε (b + n - 2) (n - 1) (by omega)
    (by omega) (by omega) w' hw' (by omega)
  have hΛi : b + n - 2 - (n - 1) + 1 = b := by omega
  rw [hΛi] at hLV

  choose! θ'' hθ'' using hP'
  set Wd := S.base.Wb (S.base.cnt w' + n * C.Kst) with hWd
  set pairs := S.base.Wb (S.base.cnt w' + C.Kst) ×ˢ S.base.Wb (S.base.cnt w' + C.Kst) with hpairs
  have hpw : ∀ x ∈ pairs, (x.1 ∈ S.base.Wall ∧ S.base.cnt x.1 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.1 + (n - 1) * C.Kst) ⊆ Wd) ∧
      (x.2 ∈ S.base.Wall ∧ S.base.cnt x.2 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.2 + (n - 1) * C.Kst) ⊆ Wd) := by
    intro x hx
    rw [hpairs, Finset.mem_product, mem_Wb_iff, mem_Wb_iff] at hx
    exact ⟨⟨hx.1.1, by omega, Wb_mono S (by omega)⟩, ⟨hx.2.1, by omega, Wb_mono S (by omega)⟩⟩
  have hpr : ∀ u, u ∈ S.base.Wall → S.base.cnt u + (n - 1) * C.Kst ≤ S.Ntop →
      TB.IsProb (S.base.Wb (S.base.cnt u + (n - 1) * C.Kst)) (θ'' u) := fun u h1 h2 => (hθ'' u h1 h2).1
  let q : crystallineComparison.V S.f → S.W → ℝ := fun σ u =>
    ∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)
  have hq : ∀ σ, TB.IsProb Wd (q σ) := by
    intro σ
    set A := crystallineComparison.pat L ((S.g : ℝ) • σ)
    refine ⟨fun u => Finset.sum_nonneg fun x hx => mul_nonneg ((hθL A).1 x) (div_nonneg (add_nonneg
      ((hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).1 u) ((hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).1 u)) (by norm_num)),
      fun u hu => Finset.sum_eq_zero fun x hx => ?_, ?_⟩
    · have h1 : θ'' x.1 u = 0 := (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).2.1 u fun h => hu ((hpw x hx).1.2.2 h)
      have h2 : θ'' x.2 u = 0 := (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).2.1 u fun h => hu ((hpw x hx).2.2.2 h)
      simp [h1, h2]
    · show ∑ u ∈ Wd, ∑ x ∈ pairs, θL A x * ((θ'' x.1 u + θ'' x.2 u) / 2) = 1
      rw [Finset.sum_comm, ← (hθL A).2.2]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
        prob_sum_sub (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1) (hpw x hx).1.2.2,
        prob_sum_sub (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1) (hpw x hx).2.2.2]
      norm_num
  obtain ⟨θn, hθn, hmix⟩ := tsum_mix Wd (fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst L ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm
    (by linarith [one_le_tsum_mL La C.Kst L hL0 (S.g : ℝ) hsm]) (fun σ => q σ) (fun σ => hq σ)
  refine ⟨θn, hθn, fun Y hY κ hκ z₀ Ss hS hgood => ?_⟩
  obtain ⟨Pq, Qq, hreg, hGD⟩ := germ_global S hpos hI hg Λ hLL hGL hΛ0 ε hε n hn b hb hbn w' hcnt Y hY
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem La (S.g : ℝ) hg'.ne'
  have := j1; have := j2
  set N' : S.W → ℝ := fun u => P' * S.base.N0 ε (b - 1) u Y κ with hN'
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, c)]) (C.loc (S.σ v) h' ++ [(n, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(n, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  let U : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ := fun v p q =>
    KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)]) (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])
  have hsub : ∀ x' ∈ pairs, ∀ (t : crystallineComparison.V S.f), Good t →
      (KB.NstV S ε (b + n - 2) (n - 1) x'.1 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.1 u * N' u ∧
      (KB.NstV S ε (b + n - 2) (n - 1) x'.2 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.2 u * N' u := by
    intro x' hx' t ht
    have e : b + (n - 1) - 1 = b + n - 2 := by omega
    have h1 := (hθ'' x'.1 (hpw x' hx').1.1 (hpw x' hx').1.2.1).2 Y hY κ hκ t ht
    have h2 := (hθ'' x'.2 (hpw x' hx').2.1 (hpw x' hx').2.2.1).2 Y hY κ hκ t ht
    rw [e] at h1 h2
    have s1 : ∑ u ∈ Wd, θ'' x'.1 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.1 + (n - 1) * C.Kst), θ'' x'.1 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').1.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').1.1 (hpw x' hx').1.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    have s2 : ∑ u ∈ Wd, θ'' x'.2 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.2 + (n - 1) * C.Kst), θ'' x'.2 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').2.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').2.1 (hpw x' hx').2.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    exact ⟨s1 ▸ h1, s2 ▸ h2⟩
  have hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V S.f, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi Y κ U x (x + (S.g : ℝ) • σ)‖ ≤
        crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u := by
    intro σ _ x hx hx'
    set t : crystallineComparison.V S.f := fun v => (x v)⁻¹ with ht_def
    set t' : crystallineComparison.V S.f := fun v => ((x + (S.g : ℝ) • σ) v)⁻¹ with ht'_def
    have ht : Good t := fun v => inv_ne_zero (hx v)
    have ht' : Good t' := fun v => inv_ne_zero (hx' v)
    have ephi : phi Y κ U x (x + (S.g : ℝ) • σ) = KB.NstV S ε (b + n - 2) (n - 1) w' Y κ t t' := by
      rw [nstV_eq]; rfl
    have hlv := hLV Y κ κ κ (fun h hh => by rw [hY h hh]; omega) (blockPSD_same Y κ hκ) t t' ht ht'
      (crystallineComparison.pat L ((S.g : ℝ) • σ))
    have ediff : ∀ v, (t v)⁻¹ - (t' v)⁻¹ = -(((S.g : ℝ) • σ) v) := by
      intro v; simp only [t, t', inv_inv, Pi.add_apply]; ring
    simp only [ediff, norm_neg] at hlv
    rw [ephi]
    refine bound_mL C.Kst L hL0 _ _ _ (hlv.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hL0 v) _)
    show _ ≤ ∑ u ∈ Wd, (∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)) * N' u
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun x' hx' => ?_
    have hs := hsub x' hx'
    have e2 : ∑ u ∈ Wd, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((θ'' x'.1 u + θ'' x'.2 u) / 2) * N' u =
        θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((∑ u ∈ Wd, θ'' x'.1 u * N' u + ∑ u ∈ Wd, θ'' x'.2 u * N' u) / 2) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [e2]
    refine mul_le_mul_of_nonneg_left ?_ ((hθL _).1 x')
    linarith [(hs t ht).1, (hs t' ht').2]
  have hH := herglotz_germ (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b n)
    (fun _ => dlB_pos S hg b n) U Pq Qq
    (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) hGD
    (fun _ _ _ _ => rfl) La Lm hLm
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u) (hmix N').1 hF z₀ Ss hS
  rw [(hmix N').2] at hH
  have hN : ∑ z ∈ Ss, Nz Y κ D z = ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re :=
    Finset.sum_congr rfl fun z hz => by
      simp only [Nz, if_pos (hgood z hz)]
      rw [nstV_eq]
      rfl
  rw [hN] at hH
  refine hH.trans (le_of_eq ?_)
  have e3 : ∑ u ∈ Wd, θn u * N' u = P' * ∑ u ∈ Wd, θn u * S.base.N0 ε (b - 1) u Y κ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
  rw [e3]
  ring

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.QuadInner1
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem hphi_meas : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
    (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
  meas_hn measurable_id

theorem quad_inner {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μW μN μW' : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN] [SigmaFinite μW']
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    (hS2 : muSof μW' μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
      ∂(muSof μW' μN) ∂(muSof μW μN) = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hae2 : ∀ᵐ s ∂(muSof μW' μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS2
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t.1 * γ * (Matrix.of t.2)⁻¹ * Matrix.of zz')‖ₑ) := by
    have mγ : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of.symm γ : Formalism.QuantumDeterminants.Mt k r)) :=
      measurable_const
    exact measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz))
      measurable_fst) mγ) (meas_inv measurable_snd)) (meas_const_mt zz'))
  calc ∫⁻ s, ∫⁻ s', ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s * γ * (Matrix.of s')⁻¹) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ
        ∂(muSof μW' μN) ∂(muSof μW μN)
      = ∫⁻ s, ∫⁻ s', ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * γ * (Matrix.of s')⁻¹ * Matrix.of zz')‖ₑ
          ∂(muSof μW' μN) ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        apply lintegral_congr_ae
        filter_upwards [hae2] with s' hs'
        have hY : Matrix.of s * γ * (Matrix.of s')⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul hs hγ) (MatrixMultiplicationContinuity.uh_inv hs').1
        have hM : (Matrix.of zz)⁻¹ * (Matrix.of s * γ * (Matrix.of s')⁻¹) * Matrix.of zz' ∈
            Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hY) hz'
        rw [coef_eq hds hz hY hz', ← hee0 _ hM]
        simp only [Matrix.mul_assoc]
    _ = ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of zz)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ *
          (Matrix.of q.1 * Matrix.of q.2)⁻¹ * Matrix.of zz')‖ₑ ∂(μW'.prod μN) ∂(μW.prod μN) := by
        unfold muSof
        rw [lintegral_map (hJ.lintegral_prod_right' (ν := (μW'.prod μN).map
          (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r)))) hphi_meas]
        apply lintegral_congr
        intro p
        have hK : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r =>
            ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) *
              γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ) := by
          have mc : Measurable (fun _ : Formalism.QuantumDeterminants.Mt k r => (fun i j => ((Matrix.of zz)⁻¹ *
              Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r) * γ) i j :
                Formalism.QuantumDeterminants.Mt k r)) := measurable_const
          exact measurable_enorm_composition he0 (meas_matmul (meas_matmul mc (meas_inv measurable_id)) (meas_const_mt zz'))
        show ∫⁻ y, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j :
            Formalism.QuantumDeterminants.Mt k r) * γ * (Matrix.of y)⁻¹ * Matrix.of zz')‖ₑ ∂((μW'.prod μN).map
              (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
                (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r))) = _
        rw [lintegral_map hK hphi_meas]
        rfl
    _ = abelian₂ e0 γ (μW.prod μN) (μW'.prod μN) zz zz' := rfl

theorem quad_inner1 {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) {e0 : Mx k r → ℂ} (he0 : Continuous e0)
    (hee0 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e0 g = ⟪w0, σ g w0⟫_ℂ)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hS1 : muSof μW μN {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0)
    {zz zz' : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN) =
      Lam1 e0 (μW.prod μN) zz zz' := by
  have hae1 : ∀ᵐ s ∂(muSof μW μN), Matrix.of s ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rw [ae_iff]; simpa using hS1
  have hJ : Measurable (fun t : Formalism.QuantumDeterminants.Mt k r =>
      ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of t * Matrix.of zz')‖ₑ) :=
    measurable_enorm_composition he0 (meas_matmul (meas_matmul (meas_inv (meas_const_mt zz)) measurable_id) (meas_const_mt zz'))
  calc ∫⁻ s, ‖⟪σ (Matrix.of zz) w0, σ (Matrix.of s) (σ (Matrix.of zz') w0)⟫_ℂ‖ₑ ∂(muSof μW μN)
      = ∫⁻ s, ‖e0 ((Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz')‖ₑ ∂(muSof μW μN) := by
        apply lintegral_congr_ae
        filter_upwards [hae1] with s hs
        have hM : (Matrix.of zz)⁻¹ * Matrix.of s * Matrix.of zz' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
          DDSmoothness.uh_mul (DDSmoothness.uh_mul (MatrixMultiplicationContinuity.uh_inv hz).1 hs) hz'
        rw [coef_eq hds hz hs hz', ← hee0 _ hM]
    _ = Lam1 e0 (μW.prod μN) zz zz' := by
        unfold muSof Lam1
        rw [lintegral_map hJ hphi_meas]
        rfl

end Formalism.FourierDecayAlt.P.S3dx4
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SiteTransport
section
open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

section comp

variable {V V' V'' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V'']
  [Module ℂ V''] {T : V →ₗ[ℂ] V'} {T' : V' →ₗ[ℂ] V''}

theorem rel_comp {A : Pr V} {A' : Pr V'} {A'' : Pr V''} (h : Rel T A A') (h' : Rel T' A' A'') :
    Rel (T' ∘ₗ T) A A'' := by
  refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
  · have h1 := LinearMap.congr_fun h.1 v
    have h2 := LinearMap.congr_fun h'.1 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]
  · have h1 := LinearMap.congr_fun h.2 v
    have h2 := LinearMap.congr_fun h'.2 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]

theorem mrel_comp {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    {M'' : Matrix (Fin 2) (Fin 2) (Pr V'')} (h : MRel T M M') (h' : MRel T' M' M'') : MRel (T' ∘ₗ T) M M'' :=
  fun a b => rel_comp (h a b) (h' a b)

variable {S : Type} [Fintype S] [DecidableEq S]

end comp

section bT

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem mrel_Ts {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) (Y : ℂ) : MRel T (Wd.Ts σ Y) (Wd.Ts σ' Y) := by
  unfold Wd.Ts; exact mrel_Tm Y hp hc hci

theorem arel_bT {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) : ∀ w : List (Wd.Letter ℂ S), ARel T (Wd.bT σ w) (Wd.bT σ' w)
  | [] => by unfold Wd.bT; exact arel_one
  | l :: w => by
    unfold Wd.bT Wd.vlet
    refine arel_mul (arel_ins _ (brel_lift0 ?_)) (arel_bT hp hc hci w)
    split_ifs
    · exact mrel_Ts hp hc hci _
    · intro a b
      rw [Matrix.map_apply, Matrix.map_apply]
      exact rel_star (mrel_Ts hp hc hci _ a b)

end bT

section one

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem site_ops {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (l : Fin ρ) :
    Rel (trL ht z z' π π') (L.p (shS l)) (Ls.p l) ∧ Rel (trL ht z z' π π') (L.c (shS l)) (Ls.c l) ∧
      Rel (trL ht z z' π π') (L.ci (shS l)) (Ls.ci l) := by
  have hop := fun (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  refine ⟨?_, ?_, ?_⟩
  · rw [hL.1, hLs.1]
    exact rel_mk (fun v => hop 0 v) (fun v => by simp only [LinearMap.neg_apply, hop 3, map_neg])
  · rw [hL.2.2.1, hLs.2.2.1]
    exact rel_mk (fun v => hop 1 v) (fun v => hop 4 v)
  · rw [hL.2.2.2.1, hLs.2.2.2.1]
    exact rel_mk (fun v => hop 2 v) (fun v => hop 5 v)

theorem qqi_rel_n {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'))}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    {sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))))} {s : ℂ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (n : ℕ) (hn : n ≤ ρ) (Y : ℂ) :
    MRel (trL ht z z' π π') (P5.QQi L st ⟨n + 1, by omega⟩ Y) (P5.QQi Ls sts ⟨n, by omega⟩ Y) := by
  have hQ : MRel (trL ht z z' π π') (st.QQ Y) (sts.QQ Y) := by
    rw [hst, hsts]
    exact mrel_smul s fun a b => rel_mk (fun v => t_tr ht hz hz' X Xs Y a b v) (fun v => t_tr ht hz hz' X Xs _ b a v)
  unfold P5.QQi
  exact mrel_mul (mrel_mul (mrel_conjTranspose (tprod_rel ht hL hLs _ _ n rfl)) hQ) (tprod_rel ht hL hLs _ _ n rfl)

end one

end Formalism.FourierDecayAlt.P.PTieB

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntUv
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_add_left (A A' C : Wq →L[ℂ] Wp) : B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  have h : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_add_right]

theorem hs_add_right (A C C' : Wq →L[ℂ] Wp) : B.hsInner A (C + C') = B.hsInner A C + B.hsInner A C' := by
  have h : B.hsVec (C + C') = B.hsVec C + B.hsVec C' := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_add_left]

theorem hs_smul_left (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner (a • A) C = a * B.hsInner A C := by
  have h : B.hsVec (a • A) = a • B.hsVec A := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_smul_right]

theorem hs_smul_right (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  have h : B.hsVec (a • C) = a • B.hsVec C := by
    unfold B.hsVec; ext i; simp
  unfold B.hsInner
  rw [h, inner_smul_left]

end HS

section Lim

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end Lim

end Formalism.FourierDecayAlt.P5.HerB
end
end

