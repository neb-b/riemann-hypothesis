module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormsMatrixStepsCoupledFactorBoundedAnyLevelPrim
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem factors_leS : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (B : Base D D.host.ccK dl) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok), FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), (∀ i, i + 2 < N.R.m → StepBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) i (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (i + 1))) ∧ CplBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (N.R.m - 1) + liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ N.R.m)  := by
  intro hB hT hV hL hR hP
  obtain ⟨Cd, hdat⟩ := GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size
  obtain ⟨C₁, hC₁, hker⟩ := GlobalTheory.T.chainKernel_bound_at_embedding_anyLevelPrime hB hT hV hL hR hP Cd
  obtain ⟨Cc, hCc, hcl⟩ := GlobalTheory.ChainClassNumbersS.classNumbers_leS
  obtain ⟨Ci, hCi, hidx⟩ := _root_.GlobalTheory.Core.Ht2.IndexCountS.card_index_le_sharp
  obtain ⟨Cy, hCy, hyb⟩ := GlobalTheory.CouplingCosetsS.ncard_ybSet_le
  refine ⟨C₁ + (Cc + Ci + Cy), by positivity, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B b hY hK hF hE hFD M _ hM ρ
  have hPr : Pr.Ok := H.1.2.2.2.2.2.2.2.2.2.1
  have hU := errUnit_nonneg N (hPr.T_prime u).one_lt.le
  have hm := N.R.two_le_m
  set U := errUnit N (Pr.T u) with hUdef
  set σ : X.K →+* ℂ := (ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1) with hσ
  set Q := KerChain.ofCol W Ch sel mu cst I
    (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE with hQ
  set kb : ℕ → ℝ := fun j => kernelBound_sq N δ (Pr.T u) C₁ j (fun z => logOmAt B cD M ρ (s.iT (pl z)))
    (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1 with hkb
  have hlift : ∀ j, kb j + 2 * ((Cc + Ci + Cy) * U) ≤
      liftBound_sq N s W Ch sel mu cst I B cD pl u δ (C₁ + (Cc + Ci + Cy)) M ρ j := fun j =>
    kernelBound_ge N δ _ _ _ j _ _ _ _ _ _
  have hpos : ∀ {n : ℕ} (lam : X.Tau → DomWeight n),
      ((Matrix.of fun i j => pairVr X.emb lam 1 (bVV X.K lam i) (bVV X.K lam j)).map
        (placeUnder s.σ₀ hM.1 ρ).embedding).PosSemidef := fun lam => (_root_.GlobalTheory.ColNorms.gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb _ lam _).1
  have hsq := fun {n : ℕ} (lam : X.Tau → DomWeight n) => (_root_.GlobalTheory.ColNorms.gram_posSemidef_and_sqAt X.E X.K X.Tau X.emb n lam σ).2
  have hk := hker CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B hFD
  obtain ⟨hc1, hc2, -⟩ := hcl CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hi1 := hidx CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hfam : ∀ j, ∀ φ : (Q.F j).Forms, 0 ≤ (famIpAt (Q.F j) (Q.hF j) (placeUnder s.σ₀ hM.1 ρ) φ φ).re := by
    intro j φ
    unfold famIpAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b' _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    refine mul_nonneg (by positivity) ?_
    exact (sqAt_nonneg (W.lamTrue u j) σ _).trans_eq (hsq (W.lamTrue u j) _).symm
  have hone : (1 : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (Cd * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
    have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
    exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le h0 h1)
  refine ⟨fun i hi φ => ?_, fun φ => ?_⟩
  · have h1 := GlobalTheory.T.sq_norm_classSumMatrix_le_cauchySchwarz X.K Q i (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (i + 1))) (Real.exp (Cc * U)) (Real.exp (Cc * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (fun _ => hpos (W.lamTrue u i))
      (fun _ => hpos (W.lamTrue u (i + 1))) (hc1 i (by omega)) (hc1 (i + 1) (by omega)) (by
        intro al be p p' x
        have h2 := hk i (i + 1) rfl (by omega) _ (frsF sel mu p) _ (frsF sel mu p') ⟨p.deco.2.lat, p.deco.2.uni⟩
          ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ (hdat CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p') M hM ρ x
        have e : (Q.kk i al be).k p p' = matK W Ch sel mu cst I (chTh W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2)) i al be p p' := by
          exact congrArg (fun k : ClsKer _ _ => k.k p p') (dif_pos (show i < N.R.m - 2 by omega))
        rw [e]
        exact (hsq (W.lamTrue u (i + 1)) _).trans_le (h2.trans_eq (congrArg _ (hsq (W.lamTrue u i) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam i φ))
    have b1 : (Fintype.card (Q.F i).β : ℝ) ≤ Real.exp (Ci * U) := hi1 i (by omega)
    have b2 : (Fintype.card (Q.F (i + 1)).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (i + 1) (by omega)
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) * Real.exp (kb (i + 1)) := by gcongr
      _ ≤ _ := by
        simp only [← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (hlift _))
        nlinarith [mul_nonneg hCy hU]
  · have hNle : N.R.N (N.R.m - 2 + 1) ≤ N.Nm := by
      unfold NumDatum.Nm Ranks.N
      have : N.R.m - 2 + 1 ≤ N.R.m := by omega
      gcongr
    have h1 := _root_.GlobalTheory.ColNorms.CplCS.cpl_le X.K Q (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (N.R.m - 2 + 1))) (Real.exp (kb N.R.m))
      (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cy * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le
      (fun _ => hpos (W.lamTrue u (N.R.m - 2))) (hpos (W.lamTrue u (N.R.m - 2 + 1))) (hpos (W.lamTrue u N.R.m))
      (hc1 (N.R.m - 2) (by omega)) (hc1 (N.R.m - 2 + 1) (by omega) b) hc2
      (fun p => (hyb CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H _ hNle).2 _ p.deco.2.lat) (by
        intro al p₀ p Y hYm x
        have h2 := hk (N.R.m - 2) (N.R.m - 2 + 1) rfl (by omega) _ (frsF sel mu p₀) _ (frsF sel mu p)
          ⟨p₀.deco.2.lat, p₀.deco.2.uni⟩ ⟨p.deco.2.lat, p.deco.2.uni⟩ _
          ((GlobalTheory.T.firstCoupledKernel_finiteDatum_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H al p₀ p Y).mono hone) M hM ρ x
        have e : (Q.cp al).k1 p₀ p Y = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2) (W.lamTrue u (N.R.m - 2 + 1)))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N (frsF sel mu p₀) p.deco.1.N (frsF sel mu p)
            (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2)) _).symm))) (by
        intro al p d Y hYm x
        have h2 := hk (N.R.m - 2 + 1) N.R.m (by omega) (by omega) _ (frsF sel mu p) _ (frsT sel mu u d)
          ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ _
          ((GlobalTheory.T.lastKernelFiniteDatum_bounded_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H p d Y hYm).mono hone) M hM ρ x
        have e : (Q.cp al).k2 p Y d = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2 + 1) (W.lamTrue u N.R.m))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p) (tilQ sel mu u d).1.N
            (frsT sel mu u d) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u N.R.m) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam _ φ))
    have b1 : (Fintype.card (Q.F Q.n).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (N.R.m - 2) (by omega)
    have e1 : N.R.m - 2 + 1 = N.R.m - 1 := by omega
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) ^ 2 * Real.exp (Cc * U) * Real.exp (Cy * U) ^ 2 *
          Real.exp (kb (N.R.m - 2 + 1)) * Real.exp (kb N.R.m) := by gcongr
      _ ≤ _ := by
        simp only [sq, ← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (add_le_add (hlift _) (hlift _)))
        rw [e1]
        nlinarith [mul_nonneg hCy hU, mul_nonneg hCi hU]

end GlobalTheory.Core.Ht2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderDetOneAddOfIntegralInverseUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CayleyOrd

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_mul' {α β γ : Type} [Fintype β] {x : Matrix α β L} {y : Matrix β γ L}
    (hx : x ∈ intMat L α β) (hy : y ∈ intMat L β γ) : x * y ∈ intMat L α γ := fun i j =>
  Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hx i k) (hy k j)

theorem intMat_one' {α : Type} [DecidableEq α] : (1 : Matrix α α L) ∈ intMat L α α := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem det_mem' {n : ℕ} {x : Matrix (Fin n) (Fin n) L} (hx : x ∈ intMat L (Fin n) (Fin n)) :
    x.det ∈ Formalism.UG.intL L := by
  have : x = (Formalism.UG.intL L).subtype.mapMatrix (Matrix.of fun i j => (⟨x i j, hx i j⟩ : Formalism.UG.intL L)) := by
    ext i j; rfl
  rw [this, ← RingHom.map_det]; exact SetLike.coe_mem _

theorem v_det_eq_one {n : ℕ} {x y : Matrix (Fin n) (Fin n) L} (hx : x ∈ intMat L (Fin n) (Fin n))
    (hy : y ∈ intMat L (Fin n) (Fin n)) (h : x * y = 1) : Valued.v x.det = 1 := by
  have h1 : Valued.v x.det * Valued.v y.det = 1 := by rw [← map_mul, ← Matrix.det_mul, h, Matrix.det_one, map_one]
  have ha : Valued.v x.det ≤ 1 := GlobalTheory.SphTheta.mem_intL.1 (det_mem' hx)
  have hb : Valued.v y.det ≤ 1 := GlobalTheory.SphTheta.mem_intL.1 (det_mem' hy)
  refine le_antisymm ha ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
    _ ≤ Valued.v x.det * 1 := by gcongr
    _ = _ := mul_one _

theorem ku_int {σ : L →+* L} {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) : k.1.1 ∈ intMat L (Fin n) (Fin n) := by
  obtain ⟨m, hm⟩ := (Subgroup.mem_subgroupOf.1 hk).2
  intro i j
  rw [← hm]; exact (m.1 i j).2

theorem zpow_int {ϖ : L} (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (m : ℤ) (hm : 0 ≤ m) : ϖ ^ m ∈ Formalism.UG.intL L := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rw [zpow_natCast]
  refine Subring.pow_mem _ (GlobalTheory.SphTheta.mem_intL.2 ?_) k
  rw [hv]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)

theorem v_zpow {ϖ : L} (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (m : ℤ) : Valued.v (ϖ ^ m) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, hv, ← WithZero.coe_zpow, ← ofAdd_zsmul]; congr 2; simp

end GlobalTheory.ChainOnto.CayleyOrd

namespace GlobalTheory.ChainOnto


open GlobalTheory.ChainOnto.CayleyOrd in
theorem ordL_det_one_add_of_inv_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (g t : GU σ n) (d : Fin n → ℤ), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU σ n, ∀ k₂ ∈ KU σ n, g⁻¹ = k₁ * t * k₂ → (1 + g.1.1).det ≠ 0 → (1 + g.1.1)⁻¹ ∈ intMat L (Fin n) (Fin n) → ordL (1 + g.1.1).det = -∑ i, max (d i) 0 := by
  intro L _ _ _ ϖ σ q hU n g t d ht k₁ hk₁ k₂ hk₂ hg hdet hc
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hU.2.2.2.1
  have hϖ : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  have hK1 := ku_int hk₁
  have hK1i := ku_int (inv_mem hk₁)
  have hK2 := ku_int hk₂
  have hK2i := ku_int (inv_mem hk₂)
  have e1 : k₁.1.1 * (k₁⁻¹).1.1 = 1 := by
    rw [show k₁.1.1 * (k₁⁻¹).1.1 = (k₁ * k₁⁻¹).1.1 from rfl, mul_inv_cancel]; rfl
  have e1' : (k₁⁻¹).1.1 * k₁.1.1 = 1 := by
    rw [show (k₁⁻¹).1.1 * k₁.1.1 = (k₁⁻¹ * k₁).1.1 from rfl, inv_mul_cancel]; rfl
  have e2 : k₂.1.1 * (k₂⁻¹).1.1 = 1 := by
    rw [show k₂.1.1 * (k₂⁻¹).1.1 = (k₂ * k₂⁻¹).1.1 from rfl, mul_inv_cancel]; rfl
  have eg : g.1.1 * (g⁻¹).1.1 = 1 := by
    rw [show g.1.1 * (g⁻¹).1.1 = (g * g⁻¹).1.1 from rfl, mul_inv_cancel]; rfl
  have hgi : (g⁻¹).1.1 = k₁.1.1 * t.1.1 * k₂.1.1 := by rw [hg]; rfl
  set Ti : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => ϖ ^ (-d i) with hTi
  have eT : t.1.1 * Ti = 1 := by
    rw [ht, hTi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hG : g.1.1 = (k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1 := by
    have X : (k₁.1.1 * t.1.1 * k₂.1.1) * ((k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1) = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂.1.1, e2, Matrix.one_mul, ← Matrix.mul_assoc t.1.1, eT, Matrix.one_mul, e1]
    calc g.1.1 = g.1.1 * ((k₁.1.1 * t.1.1 * k₂.1.1) * ((k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1)) := by rw [X, Matrix.mul_one]
      _ = (g.1.1 * (g⁻¹).1.1) * ((k₂⁻¹).1.1 * Ti * (k₁⁻¹).1.1) := by rw [hgi]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [eg, Matrix.one_mul]
  have hu : IsUnit (1 + g.1.1).det := Ne.isUnit hdet
  have hCG : (1 + g.1.1)⁻¹ * (1 + g.1.1) = 1 := Matrix.nonsing_inv_mul _ hu
  have hGC : (1 + g.1.1) * (1 + g.1.1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hCG' : (1 + g.1.1)⁻¹ * g.1.1 = 1 - (1 + g.1.1)⁻¹ := by
    rw [Matrix.mul_add, Matrix.mul_one] at hCG; exact eq_sub_of_add_eq' hCG
  set D : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => ϖ ^ max (d i) 0 with hD
  set Di : Matrix (Fin n) (Fin n) L := Matrix.diagonal fun i => ϖ ^ (-max (d i) 0) with hDi
  have eD : D * Di = 1 := by
    rw [hD, hDi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  have hyZ : (D * k₂.1.1 * (1 + g.1.1)) * ((1 + g.1.1)⁻¹ * (k₂⁻¹).1.1 * Di) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 + g.1.1), hGC, Matrix.one_mul, ← Matrix.mul_assoc k₂.1.1, e2, Matrix.one_mul, eD]
  have hDint : D ∈ intMat L (Fin n) (Fin n) := fun i j => by
    rw [hD, Matrix.diagonal_apply]; split_ifs
    · exact zpow_int hv _ (le_max_right _ _)
    · exact Subring.zero_mem _
  have hy : D * k₂.1.1 * (1 + g.1.1) ∈ intMat L (Fin n) (Fin n) := by
    have : D * k₂.1.1 * (1 + g.1.1) = D * k₂.1.1 + (D * Ti) * (k₁⁻¹).1.1 := by
      rw [Matrix.mul_add, Matrix.mul_one, hG]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂.1.1, e2, Matrix.one_mul]
    rw [this]
    refine add_mem (intMat_mul' hDint hK2) (intMat_mul' ?_ hK1i)
    intro i j
    rw [hD, hTi, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]; split_ifs
    · rw [← zpow_add₀ hϖ]; exact zpow_int hv _ (by omega)
    · exact Subring.zero_mem _
  have hCK : (1 + g.1.1)⁻¹ * (k₂⁻¹).1.1 * Ti = (1 - (1 + g.1.1)⁻¹) * k₁.1.1 := by
    rw [← hCG', hG]; simp only [Matrix.mul_assoc]; rw [e1', Matrix.mul_one]
  have hZ : (1 + g.1.1)⁻¹ * (k₂⁻¹).1.1 * Di ∈ intMat L (Fin n) (Fin n) := by
    intro i j
    rw [hDi, Matrix.mul_diagonal]
    rcases le_or_gt (d j) 0 with h | h
    · rw [max_eq_right h, neg_zero, zpow_zero, mul_one]; exact intMat_mul' hc hK2i i j
    · rw [max_eq_left h.le]
      have := congrFun (congrFun hCK i) j
      rw [hTi, Matrix.mul_diagonal] at this
      rw [this]
      exact intMat_mul' (sub_mem intMat_one' hc) hK1 i j
  have vy := v_det_eq_one hy hZ hyZ
  have vK := v_det_eq_one hK2 hK2i e2
  rw [Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, vK, mul_one, hD, Matrix.det_diagonal, map_prod] at vy
  simp only [v_zpow hv] at vy
  have hP : ∀ s : Finset (Fin n), ∏ i ∈ s, (((Multiplicative.ofAdd (-max (d i) 0) : Multiplicative ℤ)) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-∑ i ∈ s, max (d i) 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← WithZero.coe_mul, ← ofAdd_add, neg_add]
  rw [hP] at vy
  have vX : Valued.v (1 + g.1.1).det = ((Multiplicative.ofAdd (∑ i, max (d i) 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [eq_inv_of_mul_eq_one_right vy, ← WithZero.coe_inv, ← ofAdd_neg, neg_neg]
  have h0 : Valued.v (1 + g.1.1).det ≠ 0 := by rw [vX]; exact WithZero.coe_ne_zero
  unfold ordL
  rw [dite_eq_right h0]
  have hu : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (∑ i, max (d i) 0) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    (WithZero.coe_unzero h0).trans vX
  rw [WithZero.coe_injective hu, toAdd_ofAdd]

end GlobalTheory.ChainOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalIsometryNormalisesIsotropicUnipotentRadi
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

noncomputable section
namespace GlobalTheory.FrameNorm

open Formalism.L2.Theta (mt)


set_option maxHeartbeats 1600000 in
theorem norm : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), ∀ δ ∈ GQ V,
    ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) →
    ∀ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G → δ₀ * C = C * G → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  intro D V r C δ hδ δ₀ hδ₀ G hG hC
  obtain ⟨g, hg, e1, e2⟩ := exists_rat V hδ
  have hg0 : (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = δ₀ := by
    apply Matrix.map_injective (GlobalTheory.FrameStab.incA_injective D)
    exact e1.symm.trans hδ₀
  obtain ⟨σ, hσ⟩ : ∃ σ : D.host.E →+* D.host.E, σ = (D.sp.cm.sig : D.host.E →+* D.host.E) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = V.gram := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r) (Fin V.rank) D.host.E, P = Formalism.UG.cT σ C * J := ⟨_, rfl⟩
  obtain ⟨δi, hδi⟩ : ∃ δi : Matrix (Fin V.rank) (Fin V.rank) D.host.E, δi = (g⁻¹ : GL (Fin V.rank) D.host.E).1 :=
    ⟨_, rfl⟩
  have hδδi : δ₀ * δi = 1 := by rw [← hg0, hδi]; exact Units.mul_inv g
  have hδiδ : δi * δ₀ = 1 := by rw [← hg0, hδi]; exact Units.inv_mul g
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hGGi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  have hGiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hU : Formalism.UG.cT σ δ₀ * J * δ₀ = J := by rw [← hg0, hσ, hJ]; exact hg
  have hiC : δi * C = C * G⁻¹ := by
    calc δi * C = δi * (C * G * G⁻¹) := by rw [Matrix.mul_assoc C, hGGi, Matrix.mul_one]
      _ = δi * (δ₀ * C) * G⁻¹ := by rw [← hC]; simp only [Matrix.mul_assoc]
      _ = C * G⁻¹ := by rw [← Matrix.mul_assoc δi, hδiδ, Matrix.one_mul]
  have hc1 : Formalism.UG.cT σ δi * Formalism.UG.cT σ δ₀ = 1 := by
    rw [← Formalism.UG.cT_mul, hδδi]; simp [Formalism.UG.cT]
  have hcG : Formalism.UG.cT σ G * Formalism.UG.cT σ G⁻¹ = 1 := by
    rw [← Formalism.UG.cT_mul, hGiG]; simp [Formalism.UG.cT]
  have hJδ : J * δ₀ = Formalism.UG.cT σ δi * J := by
    calc J * δ₀ = Formalism.UG.cT σ δi * Formalism.UG.cT σ δ₀ * J * δ₀ := by rw [hc1, Matrix.one_mul]
      _ = Formalism.UG.cT σ δi * (Formalism.UG.cT σ δ₀ * J * δ₀) := by simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ δi * J := by rw [hU]
  have hPδ : P * δ₀ = Formalism.UG.cT σ G⁻¹ * P := by
    calc P * δ₀ = Formalism.UG.cT σ C * (J * δ₀) := by rw [hP, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (δi * C) * J := by rw [hJδ, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ G⁻¹ * P := by rw [hiC, Formalism.UG.cT_mul, hP, Matrix.mul_assoc]
  have hPδi : P * δi = Formalism.UG.cT σ G * P := by
    calc P * δi = Formalism.UG.cT σ G * Formalism.UG.cT σ G⁻¹ * P * δi := by rw [hcG, Matrix.one_mul]
      _ = Formalism.UG.cT σ G * (P * δ₀) * δi := by rw [hPδ]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ G * P := by simp only [Matrix.mul_assoc, hδδi, Matrix.mul_one]

  have hΔ : mt V δ = δ₀.map (incA D) := hδ₀
  have hΔi : mt V δ⁻¹ = δi.map (incA D) := by rw [hδi]; exact e2
  have hΓiL : mt V δ⁻¹ * C.map (incA D) = C.map (incA D) * (G⁻¹).map (incA D) := by
    rw [hΔi, ← Matrix.map_mul, hiC, Matrix.map_mul]
  have hPΓ : P.map (incA D) * mt V δ = (Formalism.UG.cT σ G⁻¹).map (incA D) * P.map (incA D) := by
    rw [hΔ, ← Matrix.map_mul, hPδ, Matrix.map_mul]
  have key : NI V C ≤ (NI V C).comap (MulAut.conj δ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun m hm => ?_
    have h1 : (mt V m - 1) * C.map (incA D) = 0 := hm.1
    have h2 : P.map (incA D) * (mt V m - 1) = 0 := by
      have := hm.2.1
      rw [hP, hσ, hJ]; exact this
    have h3 : ∀ x : Fin V.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin r → AE D,
        (mt V m - 1) *ᵥ (fun i => incA D (x i)) = C.map (incA D) *ᵥ a := by
      rw [hP, hσ, hJ]; exact hm.2.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨?_, ?_, ?_⟩
    · show (mt V (δ * m * δ⁻¹) - 1) * C.map (incA D) = 0
      rw [GlobalTheory.FrameStab.mt_conj_sub_one]
      simp only [Matrix.mul_assoc]
      rw [hΓiL, ← Matrix.mul_assoc (mt V m - 1), h1, Matrix.zero_mul, Matrix.mul_zero]
    · have c2 : P.map (incA D) * (mt V (δ * m * δ⁻¹) - 1) = 0 := by
        rw [GlobalTheory.FrameStab.mt_conj_sub_one]
        simp only [← Matrix.mul_assoc]
        rw [hPΓ]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P.map (incA D)) (mt V m - 1), h2, Matrix.zero_mul, Matrix.mul_zero]
      rw [hP, hσ, hJ] at c2; exact c2
    · intro x hx
      rw [← hJ, ← hσ, ← hP] at hx
      have hy : P *ᵥ (δi *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hPδi, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      obtain ⟨a, ha⟩ := h3 _ hy
      refine ⟨G.map (incA D) *ᵥ a, ?_⟩
      have hxi : mt V δ⁻¹ *ᵥ (fun i => incA D (x i)) = fun i => incA D ((δi *ᵥ x) i) := by
        rw [hΔi]; funext i; exact (RingHom.map_mulVec (incA D) δi x i).symm
      show (mt V (δ * m * δ⁻¹) - 1) *ᵥ (fun i => incA D (x i)) = C.map (incA D) *ᵥ (G.map (incA D) *ᵥ a)
      rw [GlobalTheory.FrameStab.mt_conj_sub_one, ← Matrix.mulVec_mulVec, hxi, ← Matrix.mulVec_mulVec, ha,
        Matrix.mulVec_mulVec, hΔ, ← Matrix.map_mul, hC, Matrix.map_mul, Matrix.mulVec_mulVec]
  intro n hn
  exact key hn

end GlobalTheory.FrameNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealInvariantSesquilinearFormEqSmulInner
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.CoefRealSchur

theorem scalar_of_comm {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (P : Module.End ℂ W → Prop) (hirr : ∀ U : Submodule ℂ W, (∀ a, P a → U.map a ≤ U) → U = ⊥ ∨ U = ⊤)
    (T₀ : Module.End ℂ W) (hT : ∀ a, P a → a * T₀ = T₀ * a) : ∃ c : ℂ, T₀ = c • 1 := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T₀
  refine ⟨c, ?_⟩
  have hU : ∀ a, P a → (T₀.eigenspace c).map a ≤ T₀.eigenspace c := by
    intro a ha
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
    rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply, ← hT a ha, Module.End.mul_apply, hv, map_smul]
  rcases hirr _ hU with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
  · refine LinearMap.ext fun v => ?_
    have hv : v ∈ T₀.eigenspace c := h ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]
    rfl

def repOp {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Module.End ℂ W where
  toFun x := (InnerProductSpace.toDual ℂ W).symm (LinearMap.toContinuousLinearMap (B x))
  map_add' x x' := by
    apply ext_inner_right ℂ
    intro w
    simp [InnerProductSpace.toDual_symm_apply, inner_add_left]
  map_smul' a x := by
    apply ext_inner_right ℂ
    intro w
    simp [InnerProductSpace.toDual_symm_apply, inner_smul_left]

theorem inner_repOp {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (x y : W) : ⟪repOp B x, y⟫_ℂ = B x y := by
  simp [repOp, InnerProductSpace.toDual_symm_apply]

theorem form_eq_smul_inner : ∀ (D : D7) (V : HSp D) (c : CoefA V), c.Is → ∀ (B : c.W →ₗ⋆[ℂ] c.W →ₗ[ℂ] ℂ), (∀ u ∈ GinfC V, ∀ x y, B (c.ρ u x) (c.ρ u y) = B x y) → ∃ z : ℂ, ∀ x y, B x y = z * ⟪x, y⟫_ℂ := by
  intro D V c hc B hB
  have hirr : ∀ U : Submodule ℂ c.W, (∀ a, (∃ u ∈ GinfC V, c.ρ u = a) → U.map a ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hc.2.2.2.2 U fun h => ?_
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    rw [map_mul, hc.1 k hk, mul_one]
    exact hU _ ⟨a, ha, rfl⟩
  haveI := hc.2.2.2.1
  have hcomm : ∀ a, (∃ u ∈ GinfC V, c.ρ u = a) → a * repOp B = repOp B * a := by
    rintro _ ⟨u, hu, rfl⟩
    apply LinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    obtain ⟨y', rfl⟩ : ∃ y', y = c.ρ u y' :=
      ⟨c.ρ u⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
    rw [Module.End.mul_apply, Module.End.mul_apply, hc.2.1, inner_repOp, inner_repOp, hB u hu]
  obtain ⟨z, hz⟩ := scalar_of_comm _ hirr (repOp B) hcomm
  refine ⟨starRingEnd ℂ z, fun x y => ?_⟩
  rw [← inner_repOp B x y, hz, LinearMap.smul_apply, Module.End.one_apply, inner_smul_left]

end GlobalTheory.CoefRealSchur
end
end

