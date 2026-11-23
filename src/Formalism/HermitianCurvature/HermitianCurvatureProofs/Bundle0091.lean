module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0085
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NotCdomRaiseOfLt
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrCap

theorem not_cdom_raise_of_lt {k : ℕ} {Λ : Fin k → ℝ} {a b : Fin k} (hab : a < b)
    (h : PI.UpqRep.CDom (PI.UpqRep.allPos k)
      (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) Λ) : False := by
  obtain ⟨c, hc, heq⟩ := h
  have hsing : ∀ p : Fin k, ∑ j : Fin k, ((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j = ((p : ℕ) : ℝ) := by
    intro p
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have e1 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (Λ - fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) j =
      ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have hj : ∀ j : Fin k,
        (Λ - fun c => Λ c + (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) j =
          (Pi.single b (1 : ℝ) : Fin k → ℝ) j - (Pi.single a (1 : ℝ) : Fin k → ℝ) j := by
      intro j
      simp only [Pi.sub_apply, Pi.single_apply]
      ring
    simp only [hj, mul_sub, Finset.sum_sub_distrib, hsing]
  have e2 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j ≤ 0 := by
    have hj : ∀ j : Fin k, ((j : ℕ) : ℝ) * (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j =
        ∑ p, ∑ q, (c p q : ℝ) * (((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j -
          ((j : ℕ) : ℝ) * (Pi.single q (1 : ℝ) : Fin k → ℝ) j) := by
      intro j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PI.UpqRep.root, Pi.sub_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    apply Finset.sum_nonpos
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_nonpos
    intro q _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsing, hsing]
    by_cases h0 : c p q = 0
    · simp [h0]
    · have hpq : ((p : ℕ) : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast (hc p q h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [heq] at e1
  linarith

theorem core {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} {g : Mx k r} {u : Fin k → ℝ}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : IsRepW k r z π) (hgU : g ∈ UH (Hpk k r))
    (hgfix : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (s : ℂ) (hgz : g *ᵥ (s • bvec (wI k r (Fin.last k))) = z)
    (hK : PI.UpqRep.IsKTypeOf (PI.UpqRep.allPos k) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
      (PI.UpqRep.lowK (PI.UpqRep.allPos k) u) ⊤) (w : ℂ) (v : W) :
    qdet (EB π (fr k r g)) w v =
      cpol (fun j : Fin k => ((PI.UpqRep.lowK (PI.UpqRep.allPos k) u j : ℝ) : ℂ) - ((j : ℕ) : ℂ)) w • v := by
  set Bs := fr k r g with hBs
  have hB : IsFrameOf k r [z] Bs := fr_frame hgU hgfix s hgz
  set Λ := PI.UpqRep.lowK (PI.UpqRep.allPos k) u with hΛ
  set E := EB π Bs with hE
  have hgl : GlRel E := (frame_general_linear W k r k z π Bs hR hB).1
  set Ec : Fin k → (W →L[ℂ] W) := fun c => ecOp π (unitB (Hpk k r) Bs c c) with hEc
  have hEE : ∀ c x, E c c x = Ec c x := fun c x => rfl
  have hσ : ∀ θ : Fin k → ℝ, π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) =
      NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • Ec c) := by
    intro θ
    rw [← torus hgU θ]
    exact op_torus hR hB θ
  obtain ⟨-, -, hirr, ⟨v₀, -, hv0, hwt⟩, hdom⟩ := hK

  have hdiag : ∀ c, E c c v₀ = (Λ c : ℂ) • v₀ := by
    intro c
    set A := hpart2 (Hpk k r) (unitB (Hpk k r) Bs c c) with hAdef
    have hA : InLieW k r z A := (QrD.frame_lie hB c c).2
    have hAe : A = (-Complex.I) • unitB (Hpk k r) Bs c c := hpart2_self Bs c
    have hf : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • A)) v₀) =
        fun t : ℝ => Complex.exp (((-t * Λ c : ℝ) : ℂ) * Complex.I) • v₀ := by
      funext t
      set θ : Fin k → ℝ := fun c' => if c' = c then -t else 0 with hθ
      have h1 : (t : ℂ) • A = ∑ c', ((θ c' : ℂ) * Complex.I) • unitB (Hpk k r) Bs c' c' := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        rw [hAe, smul_smul]
        congr 1
        simp only [hθ, if_pos rfl]
        push_cast
        ring
      have hsθ : ∑ a, Λ a * θ a = -t * Λ c := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        simp only [hθ, if_pos rfl]
        ring
      rw [h1, torus hgU θ]
      refine (hwt θ (Dg_mem θ)).trans ?_
      rw [hsθ]
    have hd : dOp π A v₀ = (-(Λ c : ℂ) * Complex.I) • v₀ := by
      rw [← QrD.dRep_eq hR.1 hR.2 hA v₀]
      unfold dRep
      rw [hf]
      exact (deriv_cexp (Λ c) v₀).deriv
    rw [hEE]
    show ecOp π (unitB (Hpk k r) Bs c c) v₀ = _
    unfold ecOp
    rw [hpart1_self, SkewHermitianParts.dOp_zero, zero_add, _root_.smul_apply, hd, smul_smul]
    congr 1
    linear_combination (-(Λ c : ℂ)) * Complex.I_sq

  have hup : ∀ a b, a < b → E a b v₀ = 0 := by
    intro a b hab
    by_contra hne
    set x := E a b v₀ with hx
    have hxw : ∀ c, Ec c x = (((fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) c : ℝ) : ℂ) • x := by
      intro c
      rw [← hEE, hx, CommonEigenvectors.diag_move hgl c a b v₀, hdiag c, map_smul]
      by_cases hca : c = a <;> by_cases hcb : c = b
      · exact absurd (hca.symm.trans hcb) hab.ne
      · rw [if_pos hca, if_neg (fun h => hcb h.symm)]
        simp only [if_pos hca, if_neg hcb]
        push_cast
        module
      · rw [if_neg hca, if_pos hcb.symm]
        simp only [if_neg hca, if_pos hcb]
        push_cast
        module
      · rw [if_neg hca, if_neg (fun h => hcb h.symm)]
        simp only [if_neg hca, if_neg hcb]
        push_cast
        module
    have hwx : PI.UpqRep.IsWtOn (PI.UpqRep.Kset (PI.UpqRep.allPos k)) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
        (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) x := by
      intro θ _
      show π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) x = _
      rw [hσ θ]
      exact exp_sum_eig Ec θ _ x hxw
    exact not_cdom_raise_of_lt hab (hdom _ x Submodule.mem_top hne hwx)

  have hHW : IsHW E (fun j => (Λ j : ℂ)) v₀ := ⟨hdiag, hup⟩
  set m : Fin k → ℂ := fun j => (Λ j : ℂ) - ((j : ℕ) : ℂ) with hm
  have hq0 : ∀ w', qdet E w' v₀ = cpol m w' • v₀ := by
    intro w'
    rw [quantumDetHighestWeight_holds W k E _ v₀ hgl hHW w']
    congr 1
    unfold cpol
    apply Finset.prod_congr rfl
    intro j _
    simp only [hm]
    ring
  have hmem : v₀ ∈ CapSp E m := mem_CapSp.2 hq0
  have hstab : Stab E (CapSp E m) := (capelli_stabilizer W k E m hgl).1
  have hirrE : ∀ S : Submodule ℂ W, Stab E S → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hU := lie_stabilizer W k r z π Bs hz hT hR hB S hS
    refine hirr S le_top ?_
    intro h hh y hy
    have hu : hᴴ * h = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.1 hh.1
      rwa [Matrix.star_eq_conjTranspose] at this
    exact hU _ (emb_uw hgU hgfix s hgz hu) y hy
  have htop : CapSp E m = ⊤ := by
    rcases hirrE _ hstab with h | h
    · exfalso
      rw [h] at hmem
      exact hv0 ((Submodule.mem_bot ℂ).1 hmem)
    · exact h
  have hv : v ∈ CapSp E m := by
    rw [htop]
    exact Submodule.mem_top
  exact mem_CapSp.1 hv w

end QrCap

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbJConvCpt
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx3
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem conv0 (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ)
    (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c₁ : ℕ)
    (hPP : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), C2.Std k r z z' → C2.PosPt k r z z' γ →
      C2.IsMonomial (Zhat k r z z' γ) → ∃ C : ℝ,
        (∀ σ ∈ C2.Sg k r z z' γ, ∀ s' ∈ Sset k r z',
          B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (c₁ * (r + 1) ^ 2)) ∧
        (∀ s ∈ Sset k r z, ∀ σ' ∈ C2.Sg' k r z z' γ,
          B.gN s + B.gN σ' ≤ C * B.gN (s⁻¹ * γ * σ') ^ (c₁ * (r + 1) ^ 2)))
    (hγ : γ ∈ B.GV k r) (hd : ∀ a, d a ≠ 0) (hZ : Zhat k r D.z D.z' γ = C2.monoP w d)
    (hpos : 0 < Gf k r D.z D.z' γ)
    (hA : 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A)
    (hFc : ContinuousOn F (B.GV k r)) (sharpFunctionalExponent : ℝ) (hb : ∀ g ∈ B.GV k r, B.gN g ^ A * ‖F g‖ ≤ sharpFunctionalExponent) :
    ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ (Formalism.FourierDecayAlt.D.muR D γ w) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := by
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  set bN : ℝ := 4 * ((r : ℝ) * nn + 1) with hbN
  set c : ℕ := (c₁ + 1) * (r + 1) ^ 2 with hc
  set M : ℝ := A / c - 2 * bN with hM
  have hmono : C2.IsMonomial (Zhat k r D.z D.z' γ) := ⟨w, d, hd, hZ⟩
  obtain ⟨CP, hCP, -⟩ := hPP k r D.z D.z' γ (P.Dx2.Rad.std D) ⟨hγ, hpos⟩ hmono

  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
  have hnn0 : 0 ≤ nn := by positivity
  have hrn : 0 ≤ (r : ℝ) * nn := by positivity
  have hbN0 : 0 ≤ bN := by positivity
  have hccast : (c : ℝ) = ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 := by rw [hc]; push_cast; ring
  have hAc : 16 * ((r : ℝ) * nn + 1) ≤ A / c := by
    rw [le_div_iff₀ hcpos, hccast]
    calc 16 * ((r : ℝ) * nn + 1) * (((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2)
        = 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * nn + 1) := by ring
      _ ≤ A := hA
  have hA4 : 4 * bN ≤ A / c := by rw [hbN]; linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hr2 : ((r : ℝ) + 1) ^ 2 ≤ (r : ℝ) * nn + 1 := by
    rw [hnn]; push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
      (show (0 : ℝ) ≤ r + k - 1 by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])]
  have hMR : 2 * ((r : ℝ) + 1) ^ 2 < M := by
    rw [hM, hbN]; nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hM0 : 0 ≤ M := by nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hA0 : 0 ≤ A := by
    have := div_nonneg_iff.mp (show 0 ≤ A / c by linarith)
    rcases this with h | h
    · exact h.1
    · linarith [h.2]

  have hG : P.Dx2.Rad.Good D γ w d := ⟨P.Dx2.Rad.exists_rho D hγ hpos hd hZ, P.Dx2.Rad.u_inj D hγ hpos hd hZ,
    fun ρ hρ => P.Dx2.Rad.u_lstg D hγ hpos hd hZ hρ⟩
  have hR := P.Dx2.Rad.haar_good D hγ hd hG
  have := P.Dx2.OrbJ.sigmaF hR
  have hI := intR D hγ hd hG hMR
  set μR := Formalism.FourierDecayAlt.D.muR D γ w with hμR
  set cR : ℝ := ∫ x, B.gN (Matrix.of x) ^ (-M) ∂μR with hcRdef
  have hone : Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ B.GV k r := by
    rw [Equiv.apply_symm_apply]
    exact (P.unitary_group_closed k r).one_mem
  have hcR : 0 < cR := by
    have := om_pos hR hM0 hI hone
    simpa only [Om, Equiv.apply_symm_apply, Matrix.mul_one] using this

  set cF := max sharpFunctionalExponent 0 with hcF
  have hFb : ∀ g ∈ B.GV k r, ‖F g‖ ≤ cF * B.gN g ^ (-A) := by
    intro g hg
    have h0 := hb g hg
    have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpw]
    calc ‖F g‖ * B.gN g ^ A = B.gN g ^ A * ‖F g‖ := by ring
      _ ≤ sharpFunctionalExponent := h0
      _ ≤ cF := le_max_left _ _

  obtain ⟨KW, hKW1, hKW⟩ := UW_bound D.z D.z_mem D.T_pos
  obtain ⟨KW', hKW1', hKW'⟩ := UW_bound D.z' D.z'_mem D.T'_pos
  set K1 := KW * KW' with hK1
  set Kγ := B.gN γ⁻¹ * B.gN γ with hKγ
  have hγ1 : 1 ≤ B.gN γ := P.BetaSesquilinearity.gN_ge_one hγ
  have hγi : B.gN γ⁻¹ = B.gN γ := (P.norm_of_inverse k r γ hγ).1
  have hKγ0 : 0 < Kγ := by rw [hKγ, hγi]; nlinarith
  set Kf := cF * K1 ^ A * CP ^ (A / c) * Kγ ^ bN / cR with hKf
  refine ⟨cut μR M, ⟨cut_meas M, cut_nonneg μR M, fun p hp => cut_norm hR hM0 hI p hp.2.1⟩, ?_⟩
  have hmaj := (maj_int D (A / c - 3 * bN) bN (by linarith) le_rfl).const_mul Kf
  refine Integrable.mono' hmaj ((cut_meas M).aestronglyMeasurable.smul (integrand_aesm D hγ hFc)) ?_
  filter_upwards [P.Dx2.OrbJ.ae_inSS D] with p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨ρ, σ, X, hρ, hσ, hnρσ, hσX, hXY, hn'le⟩ := geom D hγ hpos hCP hmono h2 h4
  have hN1 : 1 ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h2.1
  have hN1' : 1 ≤ B.gN (Matrix.of p.2.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h4.1
  have hS1 : 1 ≤ B.gN σ := P.BetaSesquilinearity.gN_ge_one hσ
  have hg0 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hγ) h4.1
  have hY1 : 1 ≤ B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) := P.BetaSesquilinearity.gN_ge_one hg0
  have hsgs := P.B7.sgs_mem D ⟨h1, h2, h3, h4⟩ hγ
  have hGg : 0 < B.gN (B.sgs p γ) := by linarith [P.BetaSesquilinearity.gN_ge_one hsgs]
  have hYG : B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ≤ K1 * B.gN (B.sgs p γ) := by
    have hhu : IsUnit (Matrix.of p.1.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h1.1
    have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
    have e : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 =
        (Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹ := by
      simp only [B.sgs, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hhu, Matrix.mul_nonsing_inv _ hh'u, Matrix.mul_one]
    rw [e]
    calc B.gN ((Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹)
        ≤ B.gN (Matrix.of p.1.1 : B.Mat k r) * B.gN (B.sgs p γ) * B.gN (Matrix.of p.2.1 : B.Mat k r)⁻¹ :=
          (P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (P.B6.gN_mul_le _ _) (P.B6.gN_nonneg _))
      _ ≤ KW * B.gN (B.sgs p γ) * KW' := by
          have a1 := hKW _ h1
          have a2 := hKW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
          have s0 := P.B6.gN_nonneg (B.sgs p γ)
          exact mul_le_mul (mul_le_mul_of_nonneg_right a1 s0) a2 (P.B6.gN_nonneg _)
            (mul_nonneg (by linarith) s0)
      _ = K1 * B.gN (B.sgs p γ) := by rw [hK1]; ring
  have hθ : cut μR M p ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
    have hlow := om_lower hR hM0 hI hρ hσ
    have e : Matrix.of.symm (ρ * σ) = p.1.2 := by rw [← hnρσ]; exact Equiv.symm_apply_apply _ _
    rw [e] at hlow
    have hσp : 0 < B.gN σ ^ (-M) := Real.rpow_pos_of_pos (by linarith) _
    have hpos' : 0 < cR * B.gN σ ^ (-M) := mul_pos hcR hσp
    unfold cut
    calc B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / Om μR M p.1.2
        ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / (cR * B.gN σ ^ (-M)) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg (P.B6.gN_nonneg _) _) hpos' hlow
      _ = B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
          rw [Real.rpow_neg (P.B6.gN_nonneg σ)]
          have : 0 < B.gN σ ^ M := Real.rpow_pos_of_pos (by linarith) _
          field_simp
  have hθ0 := cut_nonneg μR M p
  have hFv : ‖B.rho D p F γ‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A) :=
    (P.B7.norm_rho_le D ⟨h1, h2, h3, h4⟩ F γ).trans (hFb _ hsgs)
  have hCP0 : 0 < CP := by
    by_contra hle'
    have hle := not_lt.mp hle'
    have := mul_nonpos_of_nonpos_of_nonneg hle
      (pow_nonneg (P.B6.gN_nonneg ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2)) (c₁ * (r + 1) ^ 2))
    linarith
  have hec : c₁ * (r + 1) ^ 2 ≤ c := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hXY' : X ≤ CP * B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ^ c :=
    hXY.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hec) hCP0.le)
  have hK10 : 0 < K1 := by rw [hK1]; positivity
  have hkey := key_real hN1 hS1 hσX hY1 hGg hc1 hXY' hn'le hN1' hYG hθ hθ0 hFv (norm_nonneg _) hcR
    (le_max_right _ _) hCP0 hK10 hKγ0 hM hbN0 hA4
  rw [norm_smul, Real.norm_of_nonneg hθ0]
  unfold Formalism.FourierDecayAlt.D.orbIntegrand
  rw [norm_smul, P.B7.norm_xi, one_mul]
  exact hkey

theorem cpt_bound (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef D F) (A : ℝ)
    (hA : 0 ≤ A) : ∃ c : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖F g‖ ≤ c := by
  obtain ⟨hCk, ⟨R, hR⟩, -⟩ := hF
  have hFc : ContinuousOn F (B.GV k r) := P.B5.ckOn_continuousOn hCk
  set K : Set (B.Mat k r) := B.GV k r ∩ {g | B.gN g ≤ R} with hK
  have hgNc : Continuous (fun g : B.Mat k r => B.gN g) := by
    unfold B.gN
    refine Real.continuous_sqrt.comp ?_
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  have hKc : IsCompact K := by
    have hbox : IsCompact (Set.univ.pi fun _ : Fin (2 * r + k + 1) =>
        Set.univ.pi fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) (max R 0)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    refine hbox.of_isClosed_subset ((P.unitary_group_closed k r).closed.inter
      (isClosed_le hgNc continuous_const)) ?_
    intro g hg
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact (entry_le_gN g i j).trans (hg.2.trans (le_max_left _ _))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hFc.mono Set.inter_subset_left)
  refine ⟨(max R 1) ^ A * max C 0, fun g hg => ?_⟩
  by_cases hF0 : F g = 0
  · rw [hF0, norm_zero, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_max_right _ _)
  · have hgR := hR g hg hF0
    have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
    have h1 : B.gN g ^ A ≤ (max R 1) ^ A :=
      Real.rpow_le_rpow (by linarith) (hgR.trans (le_max_left _ _)) hA
    have h2 : ‖F g‖ ≤ max C 0 := (hC g ⟨hg, hgR⟩).trans (le_max_left _ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)

theorem orbJConv_cpt (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (d : Fin (r + 1) → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hγ : γ ∈ B.GV k r) (hrel : C6.IsRelevant S γ)
    (hd : ∀ a, d a ≠ 0) (hZ : Zhat k r S.z S.z' γ = C2.monoP w d) (hpos : 0 < Gf k r S.z S.z' γ)
    (hF : KB.CptCoef S F) :
    ∃ θ, D.IsNormCut S γ (D.muR S γ w) θ ∧ Integrable (fun p => θ p • D.orbIntegrand S γ F p) S.μSS := by
  obtain ⟨c₁, hPP⟩ := Formalism.FourierDecayAlt.P.polynomial_map_proper
  set A : ℝ := 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) with hAdef
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨c, hc⟩ := cpt_bound S F hF A hA0
  exact conv0 S γ w d A F c₁ hPP hγ hd hZ hpos le_rfl (P.B5.ckOn_continuousOn hF.1) c hc

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBJoint
section
open Finset NumberField MeasureTheory Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBJoint

open Formalism.FourierDecayAlt.P

noncomputable section

theorem toBuiltPlace {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {Wp Wq : NumberField.InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cb Cc A₀ : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    (h : KB.IsLeadingFormPlace Cb Cc S p f χ A₀) :
    JCT.IsBuiltPlace Cc S (KB.plT S p) f χ (KB.plν S p) (KB.plm S p) (KB.plTop S p) A₀ := by
  obtain ⟨⟨hg1, hg2, hU, hcut, -, -, -, hl1, hl2, -, hGr, -, hLC, hCA, hA, hv⟩, hE, hIn⟩ := h
  exact ⟨hg1, hg2, hU, ⟨hcut, fun v => ⟨(hv v).2.2.1, (p v).hT, (p v).hF, (p v).hP, (hv v).2.2.2.2, hE v⟩⟩,
    hl1, hl2, hGr, hLC, hCA, fun v => (hv v).2.2.2.1, by omega, hA, hIn⟩

theorem built_setting_to_model_place {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {Wp Wq : NumberField.InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cb Cc c A₀ : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    (hc : c ≤ Cc) (h : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : KB.IsLeadingFormSetting Cb c S p f χ A₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, fun v => le_trans ?_ (h13 v), le_trans hc h14,
    le_trans ?_ h15, h16⟩
  · exact mul_le_mul_of_nonneg_right hc (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)

theorem prod_dlB {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (hU : S6.Unram E) (hg : 0 < S.g) (i : ℕ) :
    ∏ _v : Fin S.f, KB.dlB S i 1 =
      ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) := by
  rw [unipotent_dual_lattice_covolume E hU S.g _ 1 hg, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hf : S.f = S6.deg E := by
    rw [← (Formalism.FourierDecayAlt.P.S6x2.degreeFacts E).2.1, Fintype.card_congr S.pl.symm, Fintype.card_fin]
  rw [hf]
  unfold KB.dlB D.deG
  push_cast
  conv_rhs => rw [zpow_mul, zpow_natCast, pow_mul, ← mul_pow, ← mul_pow]
  rw [div_div_eq_mul_div]
  congr 1
  ring

end

end Formalism.FourierDecayAlt.P.PBJoint

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

end Formalism.FourierDecayAlt.P
end

