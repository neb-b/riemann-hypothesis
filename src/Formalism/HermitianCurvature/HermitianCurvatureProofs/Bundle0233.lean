module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0142
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0230
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSliceFamJF
section
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

theorem sliceFamJF_cpt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (j : ℕ)
    (Bs : B.RealPlaceData P.k (P.r - j) Wp Wq) (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt (JC.parLev P j) Bs.z Bs.z' F) : KB.CptCoef Bs F := by
  obtain ⟨⟨hCC, ε, hε, hεG⟩, hcpt⟩ := hF
  refine ⟨Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_of_all (fun m => (hCC 0 m).choose_spec.1), ?_, ε, hε, hεG⟩
  have hcont : Continuous (fun g : B.Mat P.k (P.r - j) => B.gN g) := by
    unfold B.gN
    fun_prop
  obtain ⟨R, hR⟩ := (hcpt.isCompact.image hcont).bddAbove
  refine ⟨R, fun g _ hg => hR ⟨g, subset_tsupport F hg, rfl⟩⟩

private theorem liftVec_injective_apply {k i r' : ℕ} {v w : Fin (2 * r' + k + 1) → ℂ}
    (h : liftVec k i r' v = liftVec k i r' w) : v = w := by
  funext q
  have hq := congrFun h ⟨q.1 + i, by omega⟩
  simp only [liftVec] at hq
  rw [dite_eq_left ⟨by simp, by simp; omega⟩, dite_eq_left ⟨by simp, by simp; omega⟩] at hq
  simpa using hq

private theorem castM_castM_eq_castM_trans {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (h3 : a = c) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM h3 g := by
  subst h1 h2
  rfl

theorem slice_family_orbital : SliceFamJF := by
  intro Wp Wq _ _ _ _ _ _ P T _ hN j hj _ _ F hF t ht γ hγ hΩ
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  have hC := sliceFamJF_cpt P j (T.bs j) F hF
  set c : ℂ := ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) with hc
  let f0 : B.Mat P.k (P.r - (j + 1)) → Wq →L[ℂ] Wp := (B.GV P.k (P.r - (j + 1))).indicator fun g =>
    ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
      (psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) *
          star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) •
        F ((rn1 e xx.1)⁻¹ * mc e t g * rn1 e xx.2)
      ∂(U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))
  have hsf : sliceFam T j hj F t = fun g => c • f0 g := by
    funext g
    simp only [sliceFam, f0, Set.indicator]
    split_ifs
    · rfl
    · rw [smul_zero]
  rw [hsf, JCx2.bc_JF_smul]
  congr 1
  obtain ⟨hW1, hW1', hN1⟩ := hN j (by omega)
  obtain ⟨hW0, hW0', hN0⟩ := hN (j + 1) hj
  refine jfStep P.k (P.r - (j + 1)) (P.r - j) e Wp Wq (T.bs j) (T.bs (j + 1)) ?_ ?_ ?_ ?_
    hW1 hW1' hW0 hW0' hN1 hN0 F f0 t ht hC ?_ γ hγ hΩ
  · apply liftVec_injective_apply (i := j)
    apply castV_inj (h := (by omega : j + (P.r - j) = P.r))
    rw [T.z_lev j (by omega), asm_castV_castV,
      lift_lift_V j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega), T.z_lev (j + 1) hj]
  · apply liftVec_injective_apply (i := j)
    apply castV_inj (h := (by omega : j + (P.r - j) = P.r))
    rw [T.z'_lev j (by omega), asm_castV_castV,
      lift_lift_V j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega), T.z'_lev (j + 1) hj]
  · intro y
    rw [T.π_lev (j + 1) hj, T.π_lev j (by omega)]
    congr 1
    simp only [lev1]
    rw [castM_castM_eq_castM_trans _ _ (by omega : 1 + (P.r - (j + 1)) = P.r - j),
      lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega)]
  · intro y
    rw [T.π'_lev (j + 1) hj, T.π'_lev j (by omega)]
    congr 1
    simp only [lev1]
    rw [castM_castM_eq_castM_trans _ _ (by omega : 1 + (P.r - (j + 1)) = P.r - j),
      lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega)]
  · intro g hg
    simp [f0, Set.indicator, hg]

end Formalism.FourierDecayAlt.P.CutSH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivCombCongr
section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section ShiftJ

variable {r : ℕ}

def shIdxJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) :
    {m : Fin (r - i) // jl.val ≤ m.val} ≃ {p : Fin r // j.val ≤ p.val} where
  toFun m := ⟨⟨m.1.val + i.val, by have := m.1.isLt; have := i.isLt; omega⟩, by
    have := m.2; show j.val ≤ m.1.val + i.val; omega⟩
  invFun p := ⟨⟨p.1.val - i.val, by have := p.1.isLt; have := p.2; omega⟩, by
    have := p.2; show jl.val ≤ p.1.val - i.val; omega⟩
  left_inv m := by
    apply Subtype.ext; apply Fin.ext
    show m.1.val + i.val - i.val = m.1.val
    omega
  right_inv p := by
    apply Subtype.ext; apply Fin.ext
    show p.1.val - i.val + i.val = p.1.val
    have := p.2; omega

def shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) : Cf (r - i) (jl) ≃ᵐ Cf r j :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (shIdxJ i j jl hjl)

theorem shEqJ_mp (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) : MeasurePreserving (shEqJ i j jl hjl) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ) (shIdxJ i j jl hjl)

theorem shEqJ_apply (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c' : Cf (r - i) (jl))
    (p : {p : Fin r // j.val ≤ p.val}) : shEqJ i j jl hjl c' p = c' ((shIdxJ i j jl hjl).symm p) := by
  unfold shEqJ
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

def shiftV (i : Fin (r + 1)) (c' : Fin r → ℂ) : Fin (r - i) → ℂ :=
  fun m => c' ⟨m.val + i.val, by have := m.isLt; have := i.isLt; omega⟩

theorem glue_shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) (c'' : Cf (r - i) (jl)) :
    glue j c' (shEqJ i j jl hjl c'') =
      glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i (glue (jl) (shiftV i c') c'')) := by
  funext p
  by_cases h1 : j.val ≤ p.val
  · have h2 : i.val ≤ p.val := by omega
    have h3 : (jl).val ≤ p.val - i.val := by omega
    simp only [glue, dif_pos h1, dif_pos h2, Formalism.FourierDecayAlt.P.PTie.shiftCf, dif_pos h3, shEqJ_apply]
    rfl
  · by_cases h2 : i.val ≤ p.val
    · have h3 : ¬ (jl).val ≤ p.val - i.val := by omega
      simp only [glue, dif_neg h1, dif_pos h2, Formalism.FourierDecayAlt.P.PTie.shiftCf, dif_neg h3, shiftV]
      congr 1
      apply Fin.ext
      show p.val = p.val - i.val + i.val
      omega
    · simp only [glue, dif_neg h1, dif_neg h2]
      exact hc p (by omega)

theorem wtI_shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c'' : Cf (r - i) (jl)) :
    wtI j (shEqJ i j jl hjl c'') = wtI (jl) c'' := by
  unfold wtI
  congr 1
  simp_rw [shEqJ_apply]
  exact Fintype.prod_equiv (shIdxJ i j jl hjl).symm _ _ fun l => rfl

end ShiftJ

section Tr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem integrand_tr (μ : Measure (Mt k r)) (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ}
    {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - i)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (u v : Ix S → RadSp k r z z' π π') (c'' : Cf (r - i) (jl)) :
    wtI j (shEqJ i j jl hjl c'') * ∑ a, pairAt μ (u a) (v a) (glue j c' (shEqJ i j jl hjl c'')) =
      (κ : ℂ)⁻¹ * (wtI (jl) c'' *
        ∑ a, pairAt μi (T (u a)) (T (v a)) (glue (jl) (shiftV i c') c'')) := by
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  rw [wtI_shEqJ, glue_shEqJ i j jl hjl c c' hc]
  simp_rw [hT]
  rw [← Finset.mul_sum]
  field_simp

theorem form_tr (μ : Measure (Mt k r)) (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ}
    {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - i)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (u v : Ix S → RadSp k r z z' π π') :
    form μ j u v c' = (κ : ℂ)⁻¹ * form μi (jl) (fun a => T (u a)) (fun a => T (v a)) (shiftV i c') := by
  unfold form
  rw [← (shEqJ_mp i j jl hjl).integral_comp', ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c'' => ?_)
  exact integrand_tr μ i j jl hjl c c' hc μi T κ hκ hT u v c''

end Tr

theorem arel_star {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {S : Type}
    [Fintype S] [DecidableEq S] {T : V →ₗ[ℂ] V'} {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')}
    (h : Formalism.FourierDecayAlt.P.PBH.ARel T M M') : Formalism.FourierDecayAlt.P.PBH.ARel T (star M) (star M') := fun a b => by
  rw [Matrix.star_apply, Matrix.star_apply]
  exact Formalism.FourierDecayAlt.P.PBH.rel_star (h b a)

end Formalism.FourierDecayAlt.P5.HerD
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GNPsdC
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section C1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem block0C (hA : P5.ThmPActualCpt) (hPSC : StandardPairingDecay.PStdC) (hVI : KB.VIsoCpt) (hFP : FormPosCpt)
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (Y : Finset C.LPt)
    (hY : ∀ h ∈ Y, D.ptSize h = j) :
    KB.BlockPSD Y Y (KB.gN (setC S p F) v ε j w) (KB.hatB (setC S p F) v ε (j + 1) 1 w l)
      (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  set Dv := CV ((p v).T.bs j) (S := Fin w.length) with hDv
  refine block_iso Dv ((p v).form j hj w) cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj w x₁ x₂ y c h₁ h₂ hy)
    (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj w x y₁ y₂ c hx h₁ h₂)
    (fun x hx => hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x hx)
    (KB.waveG ((p v).T.bs j) (sW S j l) w) (fun x hx => (hVI hA _ _ (D.parOf S v) (p v) j hj w hw' (sW S j l) x x hx hx).1)
    (fun x y hx hy => (hVI hA _ _ (D.parOf S v) (p v) j hj w hw' (sW S j l) x y hx hy).2)
    Y (uY S p F v ε j hj w Y) (fun h => uY_cv hB F hF v ε hε j hj w Y h)
    (1 / (ΓS S j * S.sizeAt v w)) ?_ _ _ ?_ ?_
  · have : 0 ≤ ΓS S j * S.sizeAt v w := by
      refine mul_nonneg ?_ (sizeAt_nonneg S v w)
      unfold ΓS
      have hgpos := g_pos_of_built hB
      have hrd := PBD.rd_pos' E
      exact (PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _).le
    positivity
  · intro h hh h' hh'
    rw [uY_mem S p F v ε j hj w Y h hh, uY_mem S p F v ε j hj w Y h' hh']
    exact gN_uB hB F hF v ε hε j hj w h h'
  · intro h hh h' hh'
    rw [uY_mem S p F v ε j hj w Y h hh, uY_mem S p F v ε j hj w Y h' hh']
    exact hatB_uB_C hPSC hB F hF v ε hε j hj w hw l h h' (hY h hh) (hY h' hh')

theorem gN_psdC (hA : P5.ThmPActualCpt) (hFP : FormPosCpt) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (Y : Finset C.LPt) :
    TB.PSDOn Y (KB.gN (setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  set c0 : ℝ := 1 / (ΓS S j * S.sizeAt v w) with hc0
  have hc0n : 0 ≤ c0 := by
    have := gam_pos hB j
    have := sizeAt_nonneg S v w
    positivity
  set Dv := CV ((p v).T.bs j) (S := Fin w.length) with hDv
  have hG := gram_psd Dv (fun x y => (c0 : ℂ) * (p v).form j hj w x y) cv_zero (fun x y hx hy => cv_add hx hy)
    (fun c x hx => cv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => by simp only [form_slC (p v) j hj w x₁ x₂ y c h₁ h₂ hy]; ring)
    (fun x y₁ y₂ c hx h₁ h₂ => by simp only [form_srC (p v) j hj w x y₁ y₂ c hx h₁ h₂]; ring)
    (fun x hx => mul_nonneg (by exact_mod_cast hc0n) (hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x hx))
    Y (uY S p F v ε j hj w Y) (fun h => uY_cv hB F hF v ε hε j hj w Y h)
  refine psd_congr (fun x hx y hy => ?_) hG
  show (c0 : ℂ) * (p v).form j hj w (uY S p F v ε j hj w Y x) (uY S p F v ε j hj w Y y) = _
  rw [uY_mem S p F v ε j hj w Y x hx, uY_mem S p F v ε j hj w Y y hy, gN_uB hB F hF v ε hε j hj w x y]

end C1

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GoodAlt
section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Act

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

theorem rad_zero (Φ : Q.RadSp k ρ z z' π π') {x : (Fin ρ → ℂ) × Q.Mx k ρ} (hx : x ∉ Q.DomR k ρ z z') :
    (Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := Φ.2.1 x hx

theorem one_mem_OmX : (fun _ => (1 : ℂ)) ∈ OmX ρ := fun _ => one_ne_zero

theorem good_fn (hT : 0 ≤ Tz k ρ z * Tz k ρ z') (X : Q.ActualOps k ρ z z' π π') (j : Fin 6) :
    Good z z' π π' (X.fn j) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  set Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp) := fun Z y =>
    if 0 < Q.GGl k ρ z z' (Matrix.of y) then Q.fnVal k ρ z z' j (Matrix.of y) • Ψf Z y else 0 with hΦf

  have key : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' (Matrix.of y) →
      (X.fn j Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) =
        Q.fnVal k ρ z z' j (Matrix.of y) • (Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) := by
    intro Φ c y hG hpos
    by_cases hD : ((c, Matrix.of y) : (Fin ρ → ℂ) × Q.Mx k ρ) ∈ Q.DomR k ρ z z'
    · exact X.fn_apply j Φ (c, Matrix.of y) hD
    · rw [rad_zero (X.fn j Φ) hD, rad_zero Φ hD, smul_zero]
  have key0 : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      ¬ 0 < Q.GGl k ρ z z' (Matrix.of y) → (X.fn j Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = 0 := by
    intro Φ c y hpos
    exact rad_zero (X.fn j Φ) (x := (c, Matrix.of y)) (fun hD => hpos hD.2.2)
  refine ⟨Φf, fun Z c y hG => ?_, ?_, fun K hK q hq hG hqK => ?_, ?_⟩
  · by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key (Ψ Z) c y hG hpos, hR Z c y hG, hΦf]
      simp only [if_pos hpos]
    · rw [key0 (Ψ Z) c y hpos, hΦf]
      simp only [if_neg hpos]
  · intro q₀ hq hG
    obtain ⟨U, F, hU, hqU, hFs, hfF⟩ := hF q₀ hq hG
    have hfn := Formalism.FourierDecayAlt.P.Qx5.fnVal_contDiffOn (z := z) (z' := z') (k := k) (r := ρ) hT j
    have hm : ContDiff ℝ ∞ fun q : Par × Mt k ρ =>
        (((fun _ => (1 : ℂ)), (Matrix.of q.2 : Q.Mx k ρ)) : (Fin ρ → ℂ) × Q.Mx k ρ) :=
      contDiff_const.prodMk contDiff_snd
    refine ⟨U ∩ U₀, fun q => Q.fnVal k ρ z z' j (Matrix.of q.2) • F q, hU.inter hU₀, ⟨hqU, hq⟩, ?_, ?_⟩
    · refine ContDiffOn.smul (hfn.comp hm.contDiffOn (fun q hq' => ?_)) (hFs.mono Set.inter_subset_left)
      exact ⟨one_mem_OmX, (hUpos hq'.2).2⟩
    · intro q hq' hG'
      have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq'.2).2
      show Φf q.1 q.2 = _
      rw [hΦf]
      simp only [if_pos hpos]
      rw [show Ψf q.1 q.2 = F q from hfF q hq'.1 hG']
  · have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
    rw [hΦf]
    simp only [if_pos hpos]
    rw [hK q hG (fun h => hqK (subset_closure h)), smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key Ψi c y hyG hpos, hi c y hyV hyG, ← integral_smul]
      refine integral_congr_ae (ae_of_all _ fun Z => ?_)
      rw [hΦf]
      simp only [if_pos hpos]
    · rw [key0 Ψi c y hpos]
      have : (fun Z => Φf Z y) = fun _ => 0 := by
        funext Z
        rw [hΦf]
        simp only [if_neg hpos]
      rw [this, integral_zero]

theorem good_alt_bis (hOm : ∀ c : Fin ρ → ℂ, c ∈ OmX ρ) (hS : ∀ c c' : Fin ρ → ℂ, c = c')
    (X : Q.ActualOps k ρ z z' π π') (Y : ℂ) (a b : Fin 2) : Good z z' π π' (X.t Y a b) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  set c₁ : Fin ρ → ℂ := fun _ => 1 with hc₁
  set f : Par → Q.Mx k ρ → (Wq →L[ℂ] Wp) := fun Z => (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ with hfdef
  have hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2)) :=
    parFam_congr hF (fun q _ hG => (hR q.1 c₁ q.2 hG).symm) hU₀
  obtain ⟨a1, b1, c1⟩ := parOK_tL (E := Wq →L[ℂ] Wp) z z' Y a b Par U₀ hU₀ f hf
  set Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp) := fun Z y =>
    if 0 < Q.GGl k ρ z z' (Matrix.of y) then tL k ρ z z' (Fin.last ρ) Y a b (f Z) (Matrix.of y) else 0 with hΦf
  have key : ∀ (Φ : Q.RadSp k ρ z z' π π') (y : Mt k ρ),
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' (Matrix.of y) →
      (X.t Y a b Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ (Matrix.of y) =
        tL k ρ z z' (Fin.last ρ) Y a b ((Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁) (Matrix.of y) := by
    intro Φ y hG hpos
    exact X.t_apply Y a b Φ (c₁, Matrix.of y) ⟨hOm c₁, hG, hpos⟩
  have key0 : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      ¬ 0 < Q.GGl k ρ z z' (Matrix.of y) → (X.t Y a b Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = 0 := by
    intro Φ c y hpos
    exact rad_zero (X.t Y a b Φ) (x := (c, Matrix.of y)) (fun hD => hpos hD.2.2)
  refine ⟨Φf, fun Z c y hG => ?_, ?_, fun K hK q hq hG hqK => ?_, ?_⟩
  · rw [hS c c₁]
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key (Ψ Z) y hG hpos, hΦf]
      simp only [if_pos hpos]
      rfl
    · rw [key0 (Ψ Z) c₁ y hpos, hΦf]
      simp only [if_neg hpos]
  · exact parFam_congr a1 (fun q hq _ => by
      have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
      show _ = Φf q.1 q.2
      rw [hΦf]
      simp only [if_pos hpos]) hU₀
  · have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
    rw [hΦf]
    simp only [if_pos hpos]
    refine b1 q hq hG (closure K)ᶜ isClosed_closure.isOpen_compl hqK (fun q' hq' hG' => ?_)
    show (Ψ q'.1 : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ (Matrix.of q'.2) = 0
    rw [hR q'.1 c₁ q'.2 hG']
    exact hK q' hG' (fun h => hq' (subset_closure h))
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    rw [hS c c₁]
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key Ψi y hyG hpos]
      rw [c1 ν Kp hKp hν ((Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁) y V hV hyV hyG hKV (fun y' hy' hG' => by
        rw [hi c₁ y' hy' hG']
        refine integral_congr_ae (ae_of_all _ fun Z => ?_)
        exact (hR Z c₁ y' hG').symm)]
      refine integral_congr_ae (ae_of_all _ fun Z => ?_)
      show _ = Φf Z y
      rw [hΦf]
      simp only [if_pos hpos]
    · rw [key0 Ψi c₁ y hpos]
      have : (fun Z => Φf Z y) = fun _ => 0 := by
        funext Z
        rw [hΦf]
        simp only [if_neg hpos]
      rw [this, integral_zero]

end Act

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

