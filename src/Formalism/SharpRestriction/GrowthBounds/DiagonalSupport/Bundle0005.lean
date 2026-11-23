module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembTop
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

def RestDecG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DecAt p O Fr deg Y N₁ G' cP Dt No Go

def RestAlgG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → AlgAt p O hk Fr Dt rho No Go

def RestDegG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DegAt p O hk Fr d Dt rho No Go

def RestLabG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → LabAt p O Fr Dt rho

theorem membAt_of (hDec : RestDecG) (hAlg : RestAlgG) (hDeg : RestDegG) (hLab : RestLabG)
    (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ) (hM : MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP) :
    MembAt p O hk Fr deg Y N₁ G' cP d := by
  intro J _ Dt dPl dNo ka rho N0 hT hB hNT Gp g1 g2 g4
  obtain ⟨Go, rfl⟩ := exists_map_of_coefGe S Gp g1
  obtain ⟨No, rfl⟩ := exists_map_of_coefGe S N0 hNT.1
  have hMH : MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go :=
    ⟨hT, hB, hNT, g2, fun mo hmo => g4 mo (by rw [support_of_map]; exact hmo)⟩
  exact membAt_core p O hk Fr deg Y N₁ G' cP d Dt rho No Go
    (hDec p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hAlg p O S hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hDeg p O S hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hLab p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)

theorem margin_real (r : ℕ) (c s : ℝ) (hr : 2 ≤ r) (hc : 0 ≤ c) (h : 100 * (r : ℝ) ^ 2 * c ≤ s) : 128 * c ≤ s := by
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have : 400 * c ≤ 100 * (r : ℝ) ^ 2 * c := by nlinarith
  linarith

theorem mfh_of : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ,
    ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (_hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    MFH p F TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) (flatDeg lam0) (dT TT lam0) Y (r + K)
      (cPrime n' r TT.card c0 cpp cStar) := by
  obtain ⟨C0, hC0, H0⟩ := Formalism.CountingSumsFrames.Top.paramsII0 1 1 le_rfl le_rfl
  refine ⟨max C0 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro C hC CLa p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r hpF _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _
    hk F nb B hD
  obtain ⟨_, H, hF, _, _, _⟩ := hD
  have hC0' : C0 ≤ C := le_trans (le_max_left _ _) hC
  have hC1 : 1 ≤ C := le_trans (le_max_right _ _) hC
  have hB := hyps_basic hC1 H
  have hnb := nb_of hC1 H
  have cg0 := counting_hypotheses_of_hyps hC0 (hyps_mono hC0 hC0' H) 0 (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨h1, h2, h3, _, h5, _, _, _, _, h10, h11, _⟩ := H
  have ha0 : 0 ≤ a := by linarith [hnb.two_le_a]
  have hfd := fun s hs => flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 s hs
  have hcPe : ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) = Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar := by
    unfold cPrime Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII
    push_cast
    ring
  rw [hk] at cg0
  have A0 := (H0 p r TT.card (orbitWindowCount r de h x) 0 1 (r + K) n' L₁ (goodG' r de h x) Y a 0 c0 cpp Dp cStar cg0
    le_rfl (by unfold Formalism.CountingSumsFrames.QII; positivity)).2.1
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  refine ⟨hpF.out, h2, hF, ?_, ?_, ?_⟩
  · intro s hs
    rw [hF.1] at hs
    unfold dT
    rw [if_pos hs]
  · intro s hs
    rw [hF.1] at hs
    unfold dT
    rw [if_neg hs]
  · intro jj xx hx hW
    have hBo := Bo_ge hF.2.1 (by omega) p (by omega) (flatDeg lam0) a
      (fun s hs => (hfd s (by rw [hF.1] at hs; exact hs)).1) jj xx hx hW
    have hE : (F.fr jj (r - 1) - F.fr (jj - 1) 0).toNat ≤ goodG' r de h x := by
      have := hF.2.2.1 jj
      omega
    have hq : a / Formalism.CountingSumsFrames.QII p (goodG' r de h x) ≤ Bo p F (flatDeg lam0) jj xx := by
      refine le_trans ?_ hBo
      apply div_le_div_of_nonneg_left ha0 (by positivity)
      exact pow_le_pow_right₀ hp1 hE
    have q := (A0 _ hq).1
    have n1 : 0 ≤ 24 * (((orbitWindowCount r de h x : ℕ) : ℝ) + r) * c0 := by positivity
    have n2 : 0 ≤ Formalism.CountingSumsFrames.mStarII (orbitWindowCount r de h x) (r + K) (Formalism.CountingSumsFrames.QII p (goodG' r de h x))
        (Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar) 0 := by
      unfold Formalism.CountingSumsFrames.mStarII Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII Formalism.CountingSumsFrames.QII
      positivity
    have q2 : 100 * (r : ℝ) ^ 2 * ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) ≤
        (sl p F (flatDeg lam0) Y (r + K) jj xx : ℝ) := by
      rw [hcPe]
      have e : (sl p F (flatDeg lam0) Y (r + K) jj xx : ℝ) =
          Formalism.CountingSumsFrames.slII Y (r + K) (Bo p F (flatDeg lam0) jj xx) := rfl
      rw [e]
      linarith
    exact margin_real r _ _ h2 (Nat.cast_nonneg _) q2

theorem membership_of_four_parts (hDec : RestDecG) (hAlg : RestAlgG) (hDeg : RestDegG) (hLab : RestLabG)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMemb D CLa Ck Crk Cdeg := by
  intro _
  obtain ⟨C₁, h1, h2⟩ := mfh_of
  refine ⟨C₁, h1, fun C hC => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _
    hk F nb B hD
  exact membAt_of hDec hAlg hDeg hLab p O (dvrOfStd hD.1) hk F TT L₁ L₂ _ _ _ _ Y _
    (h2 C hC CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk F nb B hD)

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickVal
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem support_diagK_subset {σ Kf : Type} [Field Kf] (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) :
    (diagK g F).support ⊆ F.support := by
  intro mo hmo
  rw [mem_support_iff] at hmo ⊢
  rw [coeff_diagK] at hmo
  exact right_ne_zero_of_mul hmo

section Id

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem value_exact (d : Fin n' → ℕ) (hDig : DigFacts Fr p O hk nL d) (G : MvPolynomial (TV n' (m + 1)) (KK O))
    (hG : HasMultideg G d) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (hgn : ∀ bn, ((gamNo Fr p nL rho bn : ℚ) : KK O) ≠ 0)
    (e : Module.End (KK O) (MvPolynomial (TL J nL r × Fin K) (KK O)))
    (hsa : ∀ F G, fock (e F) G = fock F (e G)) (nu : TL J nL r × Fin K →₀ ℕ) (cY : KK O)
    (hpol : e (monomial nu 1) ∈ Pol (KK O) K dNo)
    (A : MvPolynomial (TL J nL r × Fin r) (KK O)) (hA : A ∈ Pol (KK O) r dPl) :
    fock G (asm Fr p O hk nL rho A
        (diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)))) =
      ((cstOf Fr p nL rho dPl dNo : ℕ) : KK O) * cY * ((expFact nu : ℕ) : KK O) *
        fock (planeCoeff nu (oneT e (levImg Fr p hk nL rho dPl dNo G)))
          (diagK (fun bp => ((gamPl Fr p nL rho bp : ℚ) : KK O)) A) := by
  have hNpol0 : diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)) ∈ Pol (KK O) K dNo :=
    diagK_mem_pol _ _ (Submodule.smul_mem _ _ hpol)
  obtain ⟨Nex, hNex⟩ : ∃ Nex, Nex = diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)) :=
    ⟨_, rfl⟩
  rw [← hNex]
  have hNpol : Nex ∈ Pol (KK O) K dNo := by rw [hNex]; exact hNpol0
  rw [(hDig G hG).1 rho dPl dNo hrho A hA Nex hNpol]
  have hback : diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)) Nex = cY • e (monomial nu 1) := by
    ext bn
    rw [coeff_diagK, hNex, coeff_diagK, ← mul_assoc, mul_inv_cancel₀ (hgn bn), one_mul]
  have hin : ∀ bp : TL J nL r × Fin r →₀ ℕ,
      ∑ bn ∈ Nex.support, ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn *
            (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
            (((gamNo Fr p nL rho bn : ℚ) : KK O) * Nex.coeff bn * ((expFact bn : ℕ) : KK O)) =
        (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
          (cY * ((e ((levImg Fr p hk nL rho dPl dNo G).coeff bp)).coeff nu * ((expFact nu : ℕ) : KK O))) := by
    intro bp
    have h1 : fock ((levImg Fr p hk nL rho dPl dNo G).coeff bp)
        (diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)) Nex) =
        cY * ((e ((levImg Fr p hk nL rho dPl dNo G).coeff bp)).coeff nu * ((expFact nu : ℕ) : KK O)) := by
      rw [hback, fock_smul_right, ← hsa, fock_monomial_right]
    rw [← h1, fock_eq_sum _ _ Nex.support (support_diagK_subset _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun bn _ => ?_
    rw [coeff_diagK]; ring
  rw [Finset.sum_congr rfl fun bp _ => hin bp]
  rw [fock_eq_sum _ _ A.support (support_diagK_subset _ _), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun bp _ => ?_
  rw [coeff_planeCoeff, coeff_oneT, coeff_diagK]; ring

theorem asm_add_right (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N N' : MvPolynomial (TL J nL r × Fin K) (KK O)) :
    asm Fr p O hk nL rho A (N + N') = asm Fr p O hk nL rho A N + asm Fr p O hk nL rho A N' := by
  unfold asm
  rw [map_add (f := _)]; ring

end Id

theorem asm_coefGe' {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
    (rho : TL J nL r × Fin (r + K) → ℕ) {A : MvPolynomial (TL J nL r × Fin r) (KK O)}
    {N : MvPolynomial (TL J nL r × Fin K) (KK O)} {t : ℝ} (hA : CoefGe p A 0) (hN : CoefGe p N t) :
    CoefGe p (asm Fr p O hk nL rho A N) t := by
  unfold asm
  have h1 : CoefGe p (monomial (labMon Fr hk nL rho) (1 : KK O)) 0 := CoefGe.monomial _ geQ_one
  have h2 : CoefGe p (upPl Fr p O hk nL A) 0 := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hA
  have h3 : CoefGe p (upNo Fr p O hk nL N) t := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hN
  have h4 := CoefGe.mul (CoefGe.mul h1 h2) h3
  simpa using h4

theorem padicVal_expFact_le (p : ℕ) [hp : Fact p.Prime] {n' k : ℕ} (d : Fin n' → ℕ) (α : Fin n' × Fin k →₀ ℕ)
    (hα : ∀ s, multideg α s = d s) : padicValNat p (expFact α) ≤ padicValNat p (∏ s, (d s).factorial) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : Fin n', ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) * expFact α := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact α ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  rw [h3, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hMn0 hE0]
  omega

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TriangularCountLeSq
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Reals

theorem natlog_le_three (p M : ℕ) (a : ℝ) (hp : 2 ≤ p) (ha : 1 ≤ a) (hM : (M : ℝ) ≤ a ^ 3) :
    ((Nat.log p M : ℕ) : ℝ) ≤ 3 * Real.logb p a := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hℓ : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 ha
  by_cases h0 : M = 0
  · subst h0
    simp only [Nat.log_zero_right, Nat.cast_zero]
    linarith
  · have hpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have l1 : ((Nat.log p M : ℕ) : ℝ) ≤ Real.logb p (M : ℝ) := Real.natLog_le_logb _ _
    have l2 : Real.logb p (M : ℝ) ≤ Real.logb p (a ^ 3) := Real.logb_le_logb_of_le hp1 hpos hM
    have l3 : Real.logb p (a ^ 3) = 3 * Real.logb p a := by rw [Real.logb_pow]; norm_num
    linarith

theorem two_a_le_cube (a : ℝ) (h : 2 ≤ a) : 2 * a ≤ a ^ 3 := by nlinarith [sq_nonneg a]

theorem sq_add_le_cube (a : ℝ) (h : 2 ≤ a) : a ^ 2 + a ≤ a ^ 3 := by nlinarith [sq_nonneg a]

theorem four_N_a (N a : ℝ) (ha : 0 ≤ a) (h : 4 * N ≤ a) : 2 * (N * (2 * a)) ≤ a ^ 2 := by nlinarith

theorem size_fin (N k r K ℓ A B Cc : ℝ) (hN : 0 ≤ N) (hℓ : 0 ≤ ℓ) (hk : 1 ≤ k) (hr0 : 0 ≤ r) (hK0 : 0 ≤ K) (hr : r ≤ k)
    (hK : K ≤ k)
    (hA : A ≤ 2 * N * (k ^ 2 * (3 * ℓ))) (hB : B ≤ N * (r * (3 * ℓ))) (hC : Cc ≤ N * (K * (3 * ℓ))) :
    A + B / 2 + Cc / 2 ≤ 9 * (N * k ^ 2 * ℓ) := by
  have h1 : k ≤ k ^ 2 := le_sq_of_one_le k hk
  have h2 : 0 ≤ N * ℓ := mul_nonneg hN hℓ
  have h3 : (N * ℓ) * r ≤ (N * ℓ) * k ^ 2 := mul_le_mul_of_nonneg_left (le_trans hr h1) h2
  have h4 : (N * ℓ) * K ≤ (N * ℓ) * k ^ 2 := mul_le_mul_of_nonneg_left (le_trans hK h1) h2
  nlinarith

theorem sl_lt_real (B Y k : ℝ) (s : ℤ) (hs : s = ⌊B / (Y * k ^ 2)⌋) (hB : 0 < B) (hY : 2 ≤ Y) (hk : 1 ≤ k) :
    3 / 8 * (s : ℝ) < B / 2 := by
  have h1 : (s : ℝ) ≤ B / (Y * k ^ 2) := by rw [hs]; exact Int.floor_le _
  have h2 : (2 : ℝ) ≤ Y * k ^ 2 := by
    have : (1 : ℝ) ≤ k ^ 2 := one_le_pow₀ hk
    nlinarith
  have h3 : B / (Y * k ^ 2) ≤ B / 2 := div_le_div_of_nonneg_left hB.le (by norm_num) h2
  linarith

end Reals

section Mult

theorem mult_level (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] {n : ℕ} (d : ι → ℕ) (be : ι × Fin n →₀ ℕ)
    (hbe : ∀ x, multideg be x = d x) :
    padicValNat p (∏ x, (d x).factorial) ≤ padicValNat p (expFact be) + ∑ x, n * Nat.log p (d x) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin n => be (s, c)) *
      ∏ c : Fin n, (be (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hbe s]
    rfl
  have h2 : expFact be = ∏ s : ι, ∏ c : Fin n, (be (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin n => be (s, c))) * expFact be := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin n => be (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact be ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  have h4 : padicValNat p (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin n => be (s, c))) ≤
      ∑ x, n * Nat.log p (d x) := by
    rw [Formalism.CountingSumsFrames.fock_val_prod p _ _ (fun s _ => (Nat.multinomial_pos _ _).ne')]
    refine Finset.sum_le_sum fun s _ => ?_
    have := Formalism.CountingSumsFrames.fock_mult_val_le p (fun c : Fin n => be (s, c)) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at this
    have e : ∑ c : Fin n, be (s, c) = d s := hbe s
    rw [e] at this
    exact this
  rw [h3, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hMn0 hE0]
  omega

theorem mult_level_real (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] {n : ℕ} (d : ι → ℕ) (be : ι × Fin n →₀ ℕ)
    (hbe : ∀ x, multideg be x = d x) (N : ℕ) (a : ℝ) (ha : 2 ≤ a) (hcard : Fintype.card ι ≤ N)
    (hd : ∀ x, (d x : ℝ) ≤ 2 * a) :
    (padicValNat p (∏ x, (d x).factorial) : ℝ) - (padicValNat p (expFact be) : ℝ) ≤
      (N : ℝ) * ((n : ℝ) * (3 * Real.logb p a)) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hℓ : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 (by linarith)
  have h := mult_level p d be hbe
  have h' : (padicValNat p (∏ x, (d x).factorial) : ℝ) ≤
      (padicValNat p (expFact be) : ℝ) + ((∑ x, n * Nat.log p (d x) : ℕ) : ℝ) := by exact_mod_cast h
  have hs : ((∑ x, n * Nat.log p (d x) : ℕ) : ℝ) ≤ (N : ℝ) * ((n : ℝ) * (3 * Real.logb p a)) := by
    push_cast
    calc ∑ x, (n : ℝ) * ((Nat.log p (d x) : ℕ) : ℝ) ≤ ∑ _x : ι, (n : ℝ) * (3 * Real.logb p a) := by
          refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact natlog_le_three p _ a hp2 (by linarith) (le_trans (hd x) (two_a_le_cube a ha))
      _ = (Fintype.card ι : ℝ) * ((n : ℝ) * (3 * Real.logb p a)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((n : ℝ) * (3 * Real.logb p a)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  linarith

end Mult

section Dno

variable {r K J : ℕ} [NeZero J]

theorem degIn_le_sum {ι : Type} [Fintype ι] (d : ι → ℕ) (S : Set ι) : degIn d S ≤ ∑ x, d x := by
  unfold degIn
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem triangular_count_le_sq (K k : ℕ) (hK : K ≤ k) : N0 K ≤ k ^ 2 := by
  unfold N0
  calc K * (K - 1) / 2 ≤ K * (K - 1) := Nat.div_le_self _ _
    _ ≤ K * K := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ ≤ k * k := Nat.mul_le_mul hK hK
    _ = k ^ 2 := by ring

theorem card_idx (nL : ZMod J → ℕ) :
    Fintype.card (Σ j : ZMod J, Fin (nL j + r + 1)) = Fintype.card (TL J nL r) + J := by
  rw [card_TL_eq, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]

theorem J_le_card (nL : ZMod J → ℕ) (hr : 1 ≤ r) : J ≤ Fintype.card (TL J nL r) := by
  rw [card_TL_eq]
  calc J = ∑ _j : ZMod J, 1 := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one]
    _ ≤ ∑ j : ZMod J, (nL j + r) := Finset.sum_le_sum fun j _ => by omega

theorem DnoOf_le (p : ℕ) (hp : 2 ≤ p) (nL : ZMod J → ℕ) (dNo : TL J nL r → ℕ) (N k : ℕ) (a : ℝ) (hr : 1 ≤ r)
    (hK : K ≤ k) (hcard : Fintype.card (TL J nL r) ≤ N) (hd : ∀ x, (dNo x : ℝ) ≤ 2 * a) (ha2 : 2 ≤ a)
    (h4N : 4 * (N : ℝ) ≤ a) (hka : (k : ℝ) ≤ a) :
    (DnoOf (K := K) p nL dNo : ℝ) ≤ 2 * (N : ℝ) * ((k : ℝ) ^ 2 * (3 * Real.logb p a)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hℓ : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 (by linarith)
  have hcard' : (Fintype.card (TL J nL r) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
  have hsum : ((∑ x, dNo x : ℕ) : ℝ) ≤ (N : ℝ) * (2 * a) := by
    push_cast
    calc ∑ x, (dNo x : ℝ) ≤ ∑ _x : TL J nL r, 2 * a := Finset.sum_le_sum fun x _ => hd x
      _ = (Fintype.card (TL J nL r) : ℝ) * (2 * a) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (2 * a) := mul_le_mul_of_nonneg_right hcard' (by linarith)
  have hterm : ∀ i : Σ j : ZMod J, Fin (nL j + r + 1),
      ((N0 K * Nat.log p (2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1) : ℕ) : ℝ) ≤
        (k : ℝ) ^ 2 * (3 * Real.logb p a) := by
    intro i
    have hM : ((2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1 : ℕ) : ℝ) ≤ a ^ 3 := by
      have e1 : 2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1 ≤ 2 * (∑ x, dNo x) + k := by
        have := degIn_le_sum dNo (NSet nL i.1 i.2.val)
        omega
      have e2 : ((2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1 : ℕ) : ℝ) ≤ ((2 * (∑ x, dNo x) + k : ℕ) : ℝ) := by
        exact_mod_cast e1
      have e3 : ((2 * (∑ x, dNo x) + k : ℕ) : ℝ) = 2 * ((∑ x, dNo x : ℕ) : ℝ) + (k : ℝ) := by push_cast; ring
      have e4 := four_N_a (N : ℝ) a (by linarith) h4N
      have e5 := sq_add_le_cube a ha2
      rw [e3] at e2
      linarith
    have l := natlog_le_three p _ a hp (by linarith) hM
    have hN0 : ((N0 K : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast triangular_count_le_sq K k hK
    rw [Nat.cast_mul]
    exact mul_le_mul hN0 l (Nat.cast_nonneg _) (by positivity)
  have hidx : (Fintype.card (Σ j : ZMod J, Fin (nL j + r + 1)) : ℝ) ≤ 2 * (N : ℝ) := by
    have h1 := card_idx (r := r) nL
    have h2 := J_le_card (r := r) nL hr
    have : Fintype.card (Σ j : ZMod J, Fin (nL j + r + 1)) ≤ 2 * N := by omega
    exact_mod_cast this
  unfold DnoOf
  rw [Nat.cast_sum]
  calc ∑ i : Σ j : ZMod J, Fin (nL j + r + 1),
        ((N0 K * Nat.log p (2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1) : ℕ) : ℝ)
      ≤ ∑ _i : Σ j : ZMod J, Fin (nL j + r + 1), (k : ℝ) ^ 2 * (3 * Real.logb p a) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card (Σ j : ZMod J, Fin (nL j + r + 1)) : ℝ) * ((k : ℝ) ^ 2 * (3 * Real.logb p a)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 * (N : ℝ) * ((k : ℝ) ^ 2 * (3 * Real.logb p a)) := mul_le_mul_of_nonneg_right hidx (by positivity)

end Dno

end Formalism.MainNotions.Proposition5Numerics
end
end

