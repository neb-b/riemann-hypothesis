module

public import Formalism.LocalToGlobal.Columns.Bundle0039

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

open Classical

theorem twIdx_h_g {j : ℕ} {b : (twIdx Ch sel mu cst m2).β j} {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) :
    (twIdx Ch sel mu cst m2).h j b P = 1 :=
  twSt_h_g Ch sel mu cst m2 j b P hP

theorem twIdx_levQ_zero (b : (twIdx Ch sel mu cst m2).β 0) :
    (twIdx Ch sel mu cst m2).levQ 0 b = LevQFam.top X.E X.K (R.N 0) (QE sel (mu : Chr X.F X.E X.K)) := rfl

theorem twIdx_levQ_pos {j : ℕ} (hj : j ≠ 0) (b : (twIdx Ch sel mu cst m2).β j) :
    (twIdx Ch sel mu cst m2).levQ j b = twLevQ Ch sel mu cst j ((twSt Ch sel mu cst m2 j).h b) := ite_eq_right hj

theorem twIntAt_pow_inv {P : HeightOneSpectrum (𝓞 X.E)} {z : X.E} {B : ℕ} (hB : 1 ≤ B) (hq : (qOf P : X.E) ≠ 0)
    (hz : IntAt P (((qOf P : X.E) ^ B)⁻¹ * z)) : IntAt P (((qOf P : X.E) ^ 1)⁻¹ * z) := by
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  have e : ((qOf P : X.E) ^ 1)⁻¹ * z = (qOf P : X.E) ^ B' * (((qOf P : X.E) ^ (B' + 1))⁻¹ * z) := by
    field_simp
    ring
  rw [e]
  refine IntAt.mul ?_ hz
  have e2 : (qOf P : X.E) ^ B' = algebraMap (𝓞 X.E) X.E ((qOf P : 𝓞 X.E) ^ B') := by simp
  rw [e2]
  exact IntAt.coe P _

theorem twSt_chrOk (hN : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i)) (hC : TwChrQ Ch sel mu cst m2) :
    ∀ (j : ℕ) (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → TwDegOne X P.1 → j ≠ 0 →
      TwChrOk Ch sel mu cst j P ((twSt Ch sel mu cst m2 j).h b P) := by
  intro j
  cases j with
  | zero =>
    intro _ _ _ _ h0
    exact absurd rfl h0
  | succ i =>
    intro b P hP hd _
    by_cases h1 : i + 1 ≤ m2
    · have hi : i < m2 := Nat.lt_of_succ_le h1
      obtain ⟨hb, hnf, ⟨al, hal⟩, hint⟩ :=
        twSt_cand (Ch := Ch) (cst := cst) (m2 := m2) (i := i) h1 (hN i hi) b P hP
      have hs := twSt_of_twNormAt (Ch := Ch) (cst := cst) hN i hi al P hP
      exact hC.1 i hi P hP hd _ _ hs.1 hs.2 hb hnf hint hal
    · have hle : i + 1 ≤ m2 + 1 := twSt_le Ch sel mu cst m2 (i + 1) b
      have he : i = m2 := by omega
      subst i
      revert b
      rw [twSt_last Ch sel mu cst m2]
      intro _
      exact hC.2 P hP hd


variable (Ch sel mu cst m2) in
theorem twIdx_ok_of (hB : OcbBase Ch sel mu cst m2) (hs : cst.sharp = true) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta)
    (hxi : XiUnitAt (rowSG Pr sel mu) G.xi0) (hwe : cst.WeilTied G.σ₀ G.xi0)
    (hmQ : ∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
      cst.muq (i + 1) P = (((Ch.muVal ⟨i, h⟩ P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K))
    (hmG : ∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ qu : X.Eˣ, (qu : X.E) = (qOf P.1 : X.E) →
      G.σ₀ (cst.muq (i + 1) P) = (((G.mu0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ)⁻¹ * G.σ₀ ((((qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ)) : X.K))
    (hA : R.m ≤ cst.A) (hB1 : 1 ≤ cst.B)
    (hDQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P)
    (hDQ' : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P)
    (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hF : TwFinQ X Pr R cst.sharp) (hN : TwNormDC Ch sel mu cst m2) (hC : TwChrQ Ch sel mu cst m2) (hZ : TwZeroQ Ch sel mu cst)
    (hAn : TwAnQ Ch sel mu cst m2) :
    (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 := by
  have hm := hB.hm
  have hX := hB.hX
  have hPr := hB.hPr
  have hNall : ∀ i, i < m2 → TwNormAt (Ch := Ch) (cst := cst) (twSt Ch sel mu cst m2 i) := twNormAt_all hN hd
  have hψ : ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ a, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a) :=
    fun P hP a ha => hB.psi0 P a hP ha
  obtain ⟨hc', hc, -, -, -, -⟩ := ookLast (R := R) hm
  have hΛ := closedLevels_by_entries_holds X Pr R Ch m2 hm
  have hGG := ocbGrpGLoc_holds Ch sel mu cst m2
  have hLam {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]
      {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
      (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ t j n c : ℕ}
      (hk1 : 1 ≤ k₀) (hcj : 1 ≤ c + j) (hn : k₀ + j + j * t ≤ n)
      {rr : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hrr : rr ∈ stabL E (n + c) (LocE.lamY P q n c fun i => i + 1))
      {g : Sp E n ≃ₗ[E] Sp E n} (hg : ∀ x, rr (Loc.inX E n c x) = Loc.inX E n c (g x))
      {hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)} (hred : ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)) :
      LocE.lamGBS q ψ₀ χ k₀ (k₀ + c + j) t j n c rr.toLinearMap = ψ₀ (redP P ((q : E) * Loc.n1Arg rr)) * ocbXLam ψ₀ χ k₀ j t hbar := by
    have hq0 := ciQ_ne_zero hu
    have hk : k₀ ≤ n := by omega
    have hint : ∀ p p', p < n + c → p' < n + c →
        IntAt P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap p p') :=
      fun p p' hp hp' => frameEntry_integral_of_stabilizer hq0 hk hp hp' hrr
    have hS : redP P (∑ i ∈ Finset.range (k₀ - 1), LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap i (i + 1) +
        ∑ i ∈ Finset.range (k₀ + c + j - k₀ - 1),
          LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + i) (k₀ + i + 1)) =
        (∑ i ∈ Finset.range (k₀ - 1), ocbM hbar i (i + 1) + ∑ i ∈ Finset.range (j - 1), ocbM hbar (k₀ + i) (k₀ + i + 1)) +
          redP P ((q : E) * Loc.n1Arg rr) := by
      rw [reduction_sum_superdiagonal (show k₀ < k₀ + c + j by omega) _ (fun p hp => hint p (p + 1) (by omega) (by omega)),
        show k₀ + c + j - k₀ - 1 = c + j - 1 by omega, finset_range_sum_split _ c j, columns_fact (k₀ := k₀) rr,
        redP_sum _ _ (fun i hi => hint _ _ (by have := Finset.mem_range.1 hi; omega) (by have := Finset.mem_range.1 hi; omega))]
      have hE : ∀ i ∈ Finset.range (k₀ - 1),
          redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap i (i + 1)) = ocbM hbar i (i + 1) := by
        intro i hi
        have := Finset.mem_range.1 hi
        exact reduction_frameEntry_of_extension hg hred (by omega) (by omega) (frameIndex_of_lt (by omega)) (frameIndex_of_lt (by omega))
      have hF : ∀ i ∈ Finset.range (j - 1),
          redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + (c + i)) (k₀ + (c + i) + 1)) =
            ocbM hbar (k₀ + i) (k₀ + i + 1) := by
        intro i hi
        have := Finset.mem_range.1 hi
        exact reduction_frameEntry_of_extension hg hred (by omega) (by omega)
          (by rw [frameIndex_of_ge (s := k₀ + (c + i)) (by omega)]; omega)
          (by rw [frameIndex_of_ge (s := k₀ + (c + i) + 1) (by omega)]; omega)
      have hM : (if 1 ≤ c ∧ 1 ≤ j then
          redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + (c - 1)) (k₀ + (c - 1) + 1)) else 0) = 0 := by
        split_ifs with h
        · rw [frameEntry_last_auxiliary_zero h.1 (by omega) hg, redP_zero]
        · rfl
      rw [Finset.sum_congr rfl hE, Finset.sum_congr rfl hF, hM]
      abel
    have hBl : ∀ i ∈ Finset.range j, LocE.unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
          LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) rr.toLinearMap (k₀ + c + j + i * t + s.1) (k₀ + c + j + i * t + s'.1))) =
        ocbChiK (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => ocbM hbar (k₀ + j + i * t + s.1) (k₀ + j + i * t + s'.1))) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have hjt : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right t hi'
      rw [Nat.succ_mul] at hjt
      have hbd : ∀ u : Fin t, k₀ + j + i * t + u.1 < n := fun u => by have := u.2; omega
      show ocbChiK (χ i) (redP P _) = _
      rw [reduction_det_eq_det_reduction _ fun s s' => hint _ _ (by have := hbd s; omega) (by have := hbd s'; omega)]
      congr 1
      congr 1
      ext s s'
      simp only [Matrix.of_apply]
      exact reduction_frameEntry_of_extension hg hred (hbd s) (hbd s')
        (by rw [frameIndex_of_ge (s := k₀ + c + j + i * t + s.1) (by omega)]; omega)
        (by rw [frameIndex_of_ge (s := k₀ + c + j + i * t + s'.1) (by omega)]; omega)
    unfold LocE.lamGBS LocE.lamGvS ocbXLam
    rw [hS, AddChar.map_add_eq_mul, Finset.prod_congr rfl hBl]
    ring
  have hCG : OcbChrGLoc Ch sel mu cst m2 := by
    intro hBase j hj w hbar g r hr hg hred
    have hw := w.2
    have h2 := R.two_le_m
    have hm := hBase.hm
    have hk5 := R.m_add_three_le_k
    have e : j * (R.t + 1) = j * R.t + j := by ring
    have hJ : r ∈ Jat (Pr := Pr) cst.sharp j w.1 := by
      have h := hr.2
      simpa [MulAut.conj_apply] using h
    rw [hBase.sharp] at hJ
    have hJ' : r ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
      unfold Jat at hJ
      rwa [ite_eq_left hw, ite_eq_left rfl] at hJ
    have hu := ciQ_notMem_sq hBase.hX hBase.hPr hw
    have hq0 := ciQ_ne_zero hu
    have hrE : R.r = R.k + cOf R j + j := by
      unfold Ranks.r cOf
      omega
    have hn : R.k + j + j * R.t ≤ R.N j := by
      unfold Ranks.N
      rw [e]
      omega
    have hint : IntAt w.1 ((qOf w.1 : X.E) * Loc.n1Arg r) := by
      rw [columns_fact (k₀ := R.k) r]
      refine ciIntAt_sum _ _ fun i hi => frameEntry_integral_of_stabilizer hq0 (by unfold Ranks.N; omega) ?_ ?_ hJ'.1
      · have := Finset.mem_range.1 hi
        unfold Ranks.N
        omega
      · have := Finset.mem_range.1 hi
        unfold Ranks.N
        omega
    have hpsi := hBase.psi0 ⟨w.1, by classical exact Finset.mem_union_left _ w.2⟩ ((qOf w.1 : X.E) * Loc.n1Arg r) hw hint
    rw [mul_div_cancel_left₀ _ hq0] at hpsi
    dsimp only at hpsi
    unfold chiInv lamRow
    dsimp only
    rw [hBase.sharp, ite_eq_left hw, ite_eq_left rfl, inv_one, one_mul, mul_one, hpsi, hrE,
      hLam hu _ _ (by omega) (by unfold cOf; omega) hn hJ'.1 hg hred, ← mul_assoc,
      inv_mul_cancel₀ (addChar_apply_ne_zero' _ _), one_mul]
  have hq0 : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → (qOf P.1 : X.E) ≠ 0 := fun P hP => by
    exact_mod_cast (ciQOf_prime hPr hP).ne_zero
  let c1 : LocCst X (rowSG Pr sel mu) := { cst with B := 1 }
  have hE1 : ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → E1at Ch sel mu cst i P 1 1 = E1at Ch sel mu c1 i P 1 1 :=
    fun i hi P hP => ookE1at_indep Ch sel mu hX hPr c1 hs hm hi P hP (hψ P hP) G.σ₀ hA (le_refl 1) hA hB1
  have hXi : ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → XiAt Ch sel mu cst i P 1 1 = XiAt Ch sel mu c1 i P 1 1 :=
    fun i hi P hP => by
      funext y
      show _ * E1at Ch sel mu cst i P 1 1 y = _ * E1at Ch sel mu c1 i P 1 1 y
      rw [hE1 i hi P hP]
  exact
    { hm := hm
      cst_ok := hB.cst_ok
      xiUnitAtPrime := hxi
      weil := hwe
      muqQ := hmQ
      muqG := hmG
      mu0G := fun j => (hT.mu0 j).atg
      psi0 := fun P a hP ha => hB.psi0 P a hP ha
      deep := fun A' B' hA' hB' i hi al be P => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG, twIdx_h_g hG]
          exact ookE1at_indep Ch sel mu hX hPr cst hs hm hi P hG (hψ P hG) G.σ₀ hA hB1 (le_trans hA hA') (le_trans hB1 hB')
        · exact hAn.deep A' B' hA' hB' i hi P hG _ _ (twSt_bdd hNall i al P hG) (twSt_bdd hNall (i + 1) be P hG)
      zero_uniq := ⟨(), fun _ => rfl⟩
      zero_h := fun _ _ => rfl
      zero_G := fun _ => colLevSym_zero Ch
      zero_Q := fun b => twIdx_levQ_zero b
      last_uniq := by
        show ∃ b : (twSt Ch sel mu cst m2 (m2 + 1)).β, ∀ b', b' = b
        rw [twSt_last]
        exact ⟨(), fun _ => rfl⟩
      last_h := by
        show ∀ (b : (twSt Ch sel mu cst m2 (m2 + 1)).β) P, (twSt Ch sel mu cst m2 (m2 + 1)).h b P = 1
        rw [twSt_last]
        intro _ _
        rfl
      nonvan := fun i hi => by
        have K := fun b P => twNext_nonvan (hNall i hi) b P
        rw [← twSt_succ_le Ch sel mu cst (show i + 1 ≤ m2 by omega)] at K
        exact K
      inj := fun i hi b b' H => by
        have K := fun b b' H => twNext_inj (hNall i hi) b b' H
        rw [← twSt_succ_le Ch sel mu cst (show i + 1 ≤ m2 by omega)] at K
        exact K b b' H
      surj := fun i hi hh hs' hb H => by
        have hfin : ∀ P, (twCSet Ch sel mu cst (twSt Ch sel mu cst m2 i) P).Finite := fun P =>
          (hF (i + 1) P.1 (Finset.mem_sdiff.1 P.2).2 (hd (twRow P) (Finset.mem_sdiff.1 P.2).2)).subset (fun D ⟨h, hD, hc⟩ => ⟨h, hD, hc.1⟩)
        have K := fun hh hs' hb H => twNext_surj (hNall i hi) hfin (fun al P hP => twSt_h_g Ch sel mu cst m2 i al P hP)
          (fun P hP h hsh H => twSurjG G.σ₀ hB hi P hP h hsh H) (fun P hP => twNonVanG G.σ₀ hB hi P hP) hh hs' hb H
        rw [← twSt_succ_le Ch sel mu cst (show i + 1 ≤ m2 by omega)] at K
        exact K hh hs' hb H
      stabG := fun j b P hP => by
        rw [twIdx_h_g hP]
        exact Subgroup.one_mem _
      depthG := hB.depthG
      depthQ := hDQ
      depthQ' := hDQ'
      boundQ := fun j b P hP => twSt_bdd hNall j b P hP
      psiSupp := fun al P x₀ y' h i => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [ite_eq_left hG, pow_one]
          rw [twIdx_h_g hG] at h
          exact (psiAt_sym Ch sel mu cst hc' hc hs P hG x₀ y' h i).1
        · rw [ite_eq_right hG]
          exact hAn.psiSupp P hG _ (twSt_bdd hNall m2 al P hG) x₀ y' h i
      psiInv := fun al P x₀ y' z hz => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG]
          exact ookPsiInv Ch sel mu hX hPr cst hs hm P hG x₀ y' z fun i => by
            have h1 := hz i
            rwa [ite_eq_left hG, pow_zero, inv_one, one_mul] at h1
        · exact hAn.psiInv P hG _ (twSt_bdd hNall m2 al P hG) x₀ y' z fun i => by
            have h1 := hz i
            rwa [ite_eq_right hG] at h1
      xiSupp := fun i hi al be P x h s l => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG, twIdx_h_g hG] at h
          exact ookXiSupp Ch sel mu cst hs hm hi P hG x h s l
        · exact hAn.xiSupp i hi P hG _ _ (twSt_bdd hNall i al P hG) (twSt_bdd hNall (i + 1) be P hG) x h s l
      xiInv := fun i hi al be P x z hz => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG, twIdx_h_g hG, hXi i hi P hG]
          exact ookXiInv Ch sel mu hX hPr c1 hs hm hi P hG (hψ P hG) G.σ₀ hA rfl x z fun s l =>
            twIntAt_pow_inv hB1 (hq0 P hG) (hz s l)
        · exact hAn.xiInv i hi P hG _ _ (twSt_bdd hNall i al P hG) (twSt_bdd hNall (i + 1) be P hG) x z hz
      psiSuppX := fun al P x₀ y' h s l => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG] at h
          exact ookPsiSuppX Ch sel mu cst hs hm P hG x₀ y' h s l
        · exact hAn.psiSuppX P hG _ (twSt_bdd hNall m2 al P hG) x₀ y' h s l
      psiInvX := fun al P x₀ z y' hz => by
        by_cases hG : P.1 ∈ Pr.vGs
        · rw [twIdx_h_g hG]
          exact ookPsiInvX Ch sel mu hX hPr c1 hs hm P hG rfl x₀ z y' fun s l => twIntAt_pow_inv hB1 (hq0 P hG) (hz s l)
        · exact hAn.psiInvX P hG _ (twSt_bdd hNall m2 al P hG) x₀ z y' hz
      int := fun j b P => twSt_int hs hNall j b P
      grpQ := fun j b P => by
        have hP : P.1 ∉ Pr.vGs := hQG P.1 P.2
        cases j with
        | zero =>
          rw [twIdx_levQ_zero]
          exact (Subgroup.subgroupOf_eq_top.2 (hZ ⟨P.1, Finset.mem_union_right _ P.2⟩ hP).1).symm
        | succ j' =>
          rw [twIdx_levQ_pos (Nat.succ_ne_zero j')]
          rfl
      chrQ := fun j b P g r hr hx => by
        have hP : P.1 ∉ Pr.vGs := hQG P.1 P.2
        cases j with
        | zero =>
          have e : ((((twIdx Ch sel mu cst m2).levQ 0 b P).lam g : X.Kˣ) : X.K) = 1 := rfl
          rw [e]
          exact ((hZ ⟨P.1, Finset.mem_union_right _ P.2⟩ hP).2 r hr).symm
        | succ j' =>
          have hok := twSt_chrOk hNall hC (j' + 1) b ⟨P.1, Finset.mem_union_right _ P.2⟩ hP (hd _ hP) (Nat.succ_ne_zero j')
          show (((twLam Ch sel mu cst (j' + 1) ⟨P.1, Finset.mem_union_right _ P.2⟩
            ((twSt Ch sel mu cst m2 (j' + 1)).h b ⟨P.1, Finset.mem_union_right _ P.2⟩)) g : X.Kˣ) : X.K) = _
          rw [twLam, dite_eq_left hok]
          exact twChiVal_eq hok hr hx
      grpG := fun j b w hbar => by
        have hj := twSt_le Ch sel mu cst m2 j b
        rw [twIdx_h_g (P := ⟨w.1, Finset.mem_union_left _ w.2⟩) w.2]
        exact (hΛ.H j hj w hbar).trans (hGG hB j hj w hbar).symm
      chrG := fun j b w hbar g r hr hg hred => by
        have hj := twSt_le Ch sel mu cst m2 j b
        rw [twIdx_h_g (P := ⟨w.1, Finset.mem_union_left _ w.2⟩) w.2] at hr ⊢
        exact (hΛ.lam j hj w hbar).trans (hCG hB j hj w hbar.1 g r hr hg hred).symm }

theorem twIdx_ok (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hK : TwCstQ (Pr := Pr) sel mu G) (hF : TwFinQ X Pr R true) (hN : TwNormDC Ch sel mu (twCst Ch sel mu G) m2)
    (hC : TwChrQ Ch sel mu (twCst Ch sel mu G) m2) (hZ : TwZeroQ Ch sel mu (twCst Ch sel mu G))
    (hAn : TwAnQ Ch sel mu (twCst Ch sel mu G) m2) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 := by
  have h2 := R.two_le_m
  have hBase : OcbBase Ch sel mu (twCst Ch sel mu G) m2 :=
    { hX := hX
      hPr := hPr
      hCh := hCh
      hm := hm
      cst_ok := twCst_ok hPr hCh h4 hK
      sharp := rfl
      psi0 := fun P a hP ha => localConstants_psi_depth_one hPr P hP a ha
      depthG := fun _ hP => twCst_D_g hP }
  refine twIdx_ok_of Ch sel mu (twCst Ch sel mu G) m2 hBase rfl G hT
    (fun P => if hP : P.1 ∈ Pr.vGs then ookXiUnit hCh hW P.1 hP else hK.xi0 P hP) (twCst_weil hX hPr hCh hW hK)
    (fun i h P hP => ?_) (fun i h P hP qu hqu => ?_) (by show R.m ≤ R.m + 1; omega) (by show 1 ≤ R.m + 1; omega)
    (fun P hP => by rw [twCst_D_Q hP]; show 2 * R.m ≤ 2 * R.m; exact le_refl _)
    (fun P hP => by rw [twCst_D_Q hP]; omega) hQG hd hF hN hC hZ hAn
  · show twMuq Ch sel mu G (i + 1) P = _
    unfold twMuq
    rw [ite_eq_right hP, dite_eq_left (by omega)]
    rfl
  · show G.σ₀ (twMuq Ch sel mu G (i + 1) P) = _
    unfold twMuq
    rw [ite_eq_left hP]
    exact ciMuq_tie G _ hval i h P hP qu hqu

end TwMain

end Formalism.L2.Col
