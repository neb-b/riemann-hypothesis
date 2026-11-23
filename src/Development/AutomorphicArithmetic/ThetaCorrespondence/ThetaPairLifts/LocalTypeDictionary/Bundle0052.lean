module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0048
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatesOfRationalThetaLiftFromCharacterisatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjTopAtOfRankLeOfWeightLe
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
noncomputable section
namespace GlobalTheory.KerConjMean
theorem conjTopAt_of_rank_le_of_weight_le : (_root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b =>
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ,
      ∃ (ρ' : Qbar →ₐ[ℚ] ℂ) (e0 : VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank → ℂ)
        (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top j)).rank → D.host.E))
        (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.V (.top (j + 1))).rank → D.host.E)) (κ : ℂ) (k n : ℕ) (r : Fin n → Qbar)
        (s : Fin n → VC D (ch.G.V (.top j)).rank (ch.G.V (.top (j + 1))).rank),
        Even ((ch.G.V (.top j)).rank * (ch.G.V (.top (j + 1))).rank) ∧
        oddE0 D D.host.ccK ch.S.Z.δ ch.S.Z.t0 _ _ e0 ∧ SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ 0 < k ∧
        (∀ i, k • s i ∈ La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) ∧ (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) ∧
        lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) = lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ) ∧
        (∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D ch.S.Z.δ ch.S.Z.t0) ρ (lat D ch.S.Z.δ)) t) ∧
        Formalism.L2.Ker.JetInVV ℂ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) (nuEnd ch.G (.top A.μ0 j)) ∧
        ∀ u, GlobalTheory.CoefModel.mapVV σ _ (f u) =
          Formalism.L2.Ker.jetOp (wt ch.G (.top j)) (wt ch.G (.top (j + 1)))
            (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) *
              U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) (Iop D (tor0 D D.host.ccK ch.S.Z.δ)
                (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) e0) z))
            (nuEnd ch.G (.top A.μ0 j)) (GlobalTheory.CoefModel.mapVV σ _ u)) → (∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
  ∀ (a b : ℕ) (e0 : VC D a b → ℂ), Even (a * b) → oddE0 D cc δ t0 a b e0 →
  ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
  ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ) (r : Fin n → Qbar) (s : Fin n → VC D a b), 0 < k →
  (∀ i, k • s i ∈ La D (tor0 D cc δ) Ls Lt) → (∀ ρ₁ : Qbar →+* ℂ, ∑ i, ‖ρ₁ (r i)‖ ≤ 1) →
  ∀ (ρ : Qbar →ₐ[ℚ] ℂ) (t' : ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t' →
    0 < area (lamConj Qbar ρ (lamOf D cc δ)) ∧
    CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) Qbar ∧
    Differentiable ℂ (fnConj D Qbar ρ fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) ∧
    ∀ z, ‖fnConj D Qbar ρ (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (s i)
      (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0) z) z‖ ^ 2 ≤
      3 * (2 * ((fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * b) *
        nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t') ^ (fF D * a * b) *
        Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ)))) → (∃ K : ℝ, 0 ≤ K ∧ ∀ (D : D7) (a b : ℕ) (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b)
  (n : D.what₂.Tau → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ v, 0 ≤ nrm lam (fun _ => 1) v) ∧
  ∃ Kx : ℝ, 0 < Kx ∧ Real.log Kx ≤ K * ((∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) +
      (Fintype.card D.what₂.Tau : ℝ) * ((a : ℝ) + b) ^ 2 + 1) *
      Real.log (2 + (∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) + a + b + Fintype.card D.what₂.Tau) ∧
    ∀ (H : VC D a b → ℂ) (S A : ℝ), 0 < A → 0 ≤ S → Differentiable ℂ H →
      (∀ z, ‖H z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ v,
      nrm lam' (fun _ => 1) (Formalism.L2.Ker.jetOp lam lam' (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H) n v) ≤
        S * Kx * max 1 A⁻¹ ^ (∑ τ, ∑ i, (lam' τ).natW i) * nrm lam (fun _ => 1) v) → (BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjTopAt ch C b C1 := by
  intro tA tB tC tD hPr hInp hDict hDepth C1 hC1
  obtain ⟨K, hK0, hFock⟩ := tC
  obtain ⟨CF0, h⟩ := BigC.and (tA hPr hInp hDict hDepth) tD
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨max C0 (2 * (6 + 126 * K) + 9 * C1), fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C ((le_max_left _ _).trans hC)
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨hA, hb3, hN1, hNb, hf1, hfb, hcard, hrd0, hrd, hj⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  have hCb : 2 * (6 + 126 * K) + 9 * C1 ≤ C := (le_max_right _ _).trans hC
  have hlogb : 1 ≤ Real.log large₂.sc.b := by
    have : Real.exp 1 ≤ large₂.sc.b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hN1' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN1
  have hf1' : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf1
  have hfNb : 1 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b := by
    have : 1 ≤ (D.R.f : ℝ) * (bigN D : ℝ) := one_le_mul_of_one_le_of_one_le hf1' hN1'
    nlinarith
  have hX : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine ⟨(6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b, 8 * D.R.f * bigN D * large₂.sc.b,
    D.R.f * bigN D * large₂.sc.b, by positivity, by positivity, by positivity, ?_, ?_⟩
  · have hsig : 0 ≤ sig ch.G :=
      Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hC0 : 0 ≤ C := by linarith
    have h2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
    have h3 := mul_le_mul_of_nonneg_right hCb hX
    unfold aOne
    nlinarith
  · intro Φ β d hocc c j fm hfm σ ρ hρ u B hu
    obtain ⟨ρ', e0, Ls, Lt, κ, k, n, r, s, hev, he0, hLs, hLt, hκ, hk, hs, hr, hlam, ⟨t, ht⟩, hJ, hfeq⟩ :=
      hA Φ β d hocc c j fm hfm σ ρ hρ
    have htc : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)) (tc D ch.S.Z.δ ch.S.Z.t0 ρ) := by
      rw [hlam]; unfold tc; rw [dite_eq_left ⟨t, ht⟩]; exact Exists.choose_spec _
    obtain ⟨harea, -, hdiff, hgr⟩ := tB D (hInp D) D.host.ccK ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ _ e0 hev he0
      Ls Lt hLs hLt κ hκ k n r s hk hs hr ρ' _ htc
    obtain ⟨hpos, Kx, hKx, hlogKx, hop⟩ := hFock D _ _ (wt ch.G (.top j)) (wt ch.G (.top (j + 1))) _ hJ
    have eA : hArea D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (area (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)))⁻¹ := by
      unfold hArea; rw [hlam]
    have eT : hTh D ch.S.Z.δ ch.S.Z.t0 ρ = Real.posLog (nrm1Sq (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ))
        (GL3Theta.th0 (lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ)) (tc D ch.S.Z.δ ch.S.Z.t0 ρ))) := by
      unfold hTh; rw [hlam]
    set L := lamConj Qbar ρ' (lamOf D D.host.ccK ch.S.Z.δ) with hL
    set X := nrm1Sq L (GL3Theta.th0 L (tc D ch.S.Z.δ ch.S.Z.t0 ρ)) with hXdef
    set a := (ch.G.V (.top j)).rank with ha
    set bb := (ch.G.V (.top ((j : ℕ) + 1))).rank with hbb
    set g := fF D * a * bb with hg
    set P := 3 * (2 * ((g : ℕ) : ℝ) * D.host.rdE + 1) ^ g with hP
    set deg := ∑ τ, ∑ i, (wt ch.G (.top ((j : ℕ) + 1)) τ).natW i with hdeg
    have hS : 0 ≤ P * X ^ g := by
      have h0 := hgr 0
      have : (∑ τ, ∑ i, ∑ j, ‖(0 : VC D a bb) τ i j‖ ^ 2) = 0 := by simp
      rw [this, mul_zero, zero_div, Real.exp_zero, mul_one] at h0
      exact le_trans (sq_nonneg _) h0
    have hop' := hop _ (P * X ^ g) _ harea hS hdiff hgr (GlobalTheory.CoefModel.mapVV σ _ u)
    have hM0 : 0 ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg :=
      mul_nonneg (mul_nonneg hS hKx.le) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    have hrdpos : 0 < 2 * ((g : ℕ) : ℝ) * D.host.rdE + 1 := by
      have := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg g)) hrd0; linarith
    have hPpos : 0 < P := by rw [hP]; exact mul_pos (by norm_num) (pow_pos hrdpos g)
    have hW : ∀ jj : ℕ, jj ≤ D.R.m → (∑ τ, ∑ i, ((wt ch.G (.top jj) τ).natW i : ℝ)) ≤
        (D.R.f : ℝ) * (bigN D : ℝ) * (8 * large₂.sc.b) := by
      intro jj hjj
      calc (∑ τ, ∑ i, ((wt ch.G (.top jj) τ).natW i : ℝ)) ≤
            ∑ τ : D.what₂.Tau, ∑ i : Fin (ch.G.V (.top jj)).rank, (8 * large₂.sc.b) :=
            Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => (hj jj hjj).2 τ i
        _ = (Fintype.card D.what₂.Tau : ℝ) * (((ch.G.V (.top jj)).rank : ℝ) * (8 * large₂.sc.b)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (D.R.f : ℝ) * ((bigN D : ℝ) * (8 * large₂.sc.b)) := by
            have h1 : (Fintype.card D.what₂.Tau : ℝ) ≤ D.R.f := by exact_mod_cast hcard
            have h2 : ((ch.G.V (.top jj)).rank : ℝ) ≤ bigN D := by exact_mod_cast (hj jj hjj).1
            exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity) (by positivity)
        _ = _ := by ring
    have hW0 : ∀ jj : ℕ, 0 ≤ (∑ τ, ∑ i, ((wt ch.G (.top jj) τ).natW i : ℝ)) := fun jj =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have haN : (a : ℝ) ≤ bigN D := by exact_mod_cast (hj j j.2.le).1
    have hbN : (bb : ℝ) ≤ bigN D := by exact_mod_cast (hj ((j : ℕ) + 1) (Nat.succ_le_of_lt j.2)).1
    have hgc : (g : ℝ) = (D.R.f : ℝ) * a * bb := by rw [hg]; push_cast; rfl
    obtain ⟨hc0, hgG⟩ := size_bound K D.R.f (bigN D) large₂.sc.b D.host.rdE Kx _ _ a bb (Fintype.card D.what₂.Tau) g hK0 (Nat.cast_nonneg _) (by exact_mod_cast hcard) hb3 hN1' hNb hf1' hfb
      hrd0 hrd (Nat.cast_nonneg _) haN (Nat.cast_nonneg _) hbN (hW j j.2.le) (hW _ (Nat.succ_le_of_lt j.2))
      (hW0 _) (hW0 _) hgc hKx hlogKx
    have hc : Real.log (P * Kx) ≤ (6 + 126 * K) * D.R.f * bigN D * large₂.sc.b * Real.log large₂.sc.b := by
      rw [hP]; exact hc0
    have hdN : (deg : ℝ) ≤ 8 * D.R.f * bigN D * large₂.sc.b := by
      have e : (deg : ℝ) = ∑ τ, ∑ i, ((wt ch.G (.top ((j : ℕ) + 1)) τ).natW i : ℝ) := by rw [hdeg]; push_cast; rfl
      rw [e]; refine (hW _ (Nat.succ_le_of_lt j.2)).trans (le_of_eq ?_); ring
    have hpA : 0 ≤ Real.posLog (area L)⁻¹ := by unfold Real.posLog; exact le_max_left _ _
    have hpX : 0 ≤ Real.posLog X := by unfold Real.posLog; exact le_max_left _ _
    have hMexp : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤ Real.exp ((6 + 126 * K) * D.R.f * bigN D * large₂.sc.b *
        Real.log large₂.sc.b + 8 * D.R.f * bigN D * large₂.sc.b * hArea D ch.S.Z.δ ch.S.Z.t0 ρ +
        D.R.f * bigN D * large₂.sc.b * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) := by
      have hXg := pow_le_exp_posLog X g
      have hMd := max_pow_le_exp_posLog (area L) harea deg
      have step1 : P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg ≤
          (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) := by
        have := mul_le_mul hXg hMd (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.exp_pos _).le
        calc P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg = (P * Kx) * (X ^ g * max 1 (area L)⁻¹ ^ deg) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (mul_nonneg hPpos.le hKx.le)
      refine step1.trans ?_
      have eq : (P * Kx) * (Real.exp (g * Real.posLog X) * Real.exp (deg * Real.posLog (area L)⁻¹)) =
          Real.exp (Real.log (P * Kx) + g * Real.posLog X + deg * Real.posLog (area L)⁻¹) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (mul_pos hPpos hKx)]; ring
      rw [eq, Real.exp_le_exp, eA, eT]
      linarith [mul_le_mul_of_nonneg_right hgG hpX, mul_le_mul_of_nonneg_right hdN hpA]
    rw [hfeq u]
    calc _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg * nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ u) := hop'
      _ ≤ P * X ^ g * Kx * max 1 (area L)⁻¹ ^ deg * B := mul_le_mul_of_nonneg_left hu hM0
      _ ≤ _ := mul_le_mul_of_nonneg_right hMexp (le_trans (hpos _) hu)
theorem conj_top_degree_in_kernel_mean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjTopAt ch C b C1 :=
  _root_.GlobalTheory.KerConjMean.conjTopAt_of_rank_le_of_weight_le _root_.GlobalTheory.T.kernel_conjugate_transport _root_.GlobalTheory.ConjGrowth.conj_growth _root_.GlobalTheory.FockJetBound.jetOp_norm_le _root_.GlobalTheory.KerConjMean.TopSizes.sizesK
end GlobalTheory.KerConjMean
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_conjugation_average : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → ∀ C1 : ℝ, 0 < C1 → BigC fun _ ch C b => ConjTopAt ch C b C1 := by
  first | exact @_root_.GlobalTheory.KerConjMean.conj_top_degree_in_kernel_mean | exact _root_.GlobalTheory.KerConjMean.conj_top_degree_in_kernel_mean | (intros; apply _root_.GlobalTheory.KerConjMean.conj_top_degree_in_kernel_mean <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspTransitionRightward
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.RightArrowCusp
theorem cuspStep_rightward : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  intro hLS hP
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
  intro t M hM a ha hr e he φ f hf Q F' hF
  obtain ⟨i, j, rfl⟩ := hr
  obtain ⟨i', j', hi, hj, h'⟩ | ⟨_, _, _, _, _, h'⟩ := ha
  · cases h'
    have hcg : ch.sc.cGap = 1 := by rw [hsc]
    obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
      hP.harishChandraModules hSet.host hSet.size hSet.core hcg ch.W hch.weil
    have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
      ⟨hSet.core.lev, hSet.core.models.inf, hSet.core.models.νY, hSet.core.models.νY', hSet.core.models.νX⟩
    have hSm := (hLS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hSet.size) Γ Pl0 T A Ks R G hRB hG).X t i j hi hj
    have hgm := meas_haar_fund hSet.core G hG t i j hi.le hj
    exact lift_right_of_smooth hcg ch.W hch.weil ch.rm hch.vac M t hM i j hi hj (G.V i j) (G.V (i + 1) j)
      (hMa.1.vert i j hi.le hj).sp (hMa.1.vert (i + 1) j hi hj).sp (vert_par hSet.core G hG i j hi.le hj)
      (vert_par hSet.core G hG (i + 1) j hi hj) (G.meas t i j) hgm.1 hgm.2 (G.X i j).ω (hMa.2.omX i j hi hj) hSm
      e he φ f hf Q F' hF
end GlobalTheory.RightArrowCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_transition_rightward : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  first | exact @_root_.GlobalTheory.RightArrowCusp.cuspStep_rightward | exact _root_.GlobalTheory.RightArrowCusp.cuspStep_rightward | (intros; apply _root_.GlobalTheory.RightArrowCusp.cuspStep_rightward <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsGridOfSquareTower
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor NegIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SqTower.TopGridExists
set_option maxHeartbeats 1000000 in
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Doubling GlobalTheory.SqTower.TopExists in
theorem square_tower_grid_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ X : TriG G i j, TopGrid W i j X ∧ IsStageC W i j (pp D j) (qq D j) X := by
  intro _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G W i j => ?_⟩⟩
  have hi := i.2
  have hj := j.2
  have a := node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩
  have a' := node_isV G hL (X := .grid i j) ⟨by omega, by omega⟩
  have b := node_isV G hL (X := .grid i (j + 1)) ⟨by omega, by omega⟩
  have b' := node_isV G hL (X := .grid (i + 1) j) ⟨by omega, by omega⟩
  have ng : ∀ {X : LSp D} {ν q : ℕ}, X.IsV ν q → NegIdx X.sp q := fun h =>
    GlobalTheory.Grid.Vertex.negIdx_of_sig _ _ h.sigOK fun τ => by rw [h.sig, h.rank]
  have ho : ∀ (x : (G.V (.grid i (j + 1))).V) (y : (G.V (.grid (i + 1) j)).V),
      (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).hD (LinearMap.inl D.host.E _ _ x) (LinearMap.inr D.host.E _ _ y) = 0 :=
    fun x y => by simp [HSpace.hD, orthSum_apply]
  have hsig := sigOK_hsum b.sigOK b'.sigOK
  have hsd := GlobalTheory.Twist.OrthSum.selfDual_hsum b.sd b'.sd
  have hneg := negIdx_of_orth rfl _ _ (isIsomEmb_inl _ _) (isIsomEmb_inr _ _) ho (ng b) (ng b')
  obtain ⟨FA, hFA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩
  obtain ⟨FA', hFA'⟩ := exists_isGridFr W (X := .grid i j) ⟨by omega, by omega⟩
  obtain ⟨FV, hFV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨by omega, by omega⟩
  obtain ⟨FV', hFV'⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨by omega, by omega⟩
  obtain ⟨rA, eA, sA, hA⟩ := exists_rig_of_frame FA _ a.sd
  obtain ⟨rA', eA', sA', hA'⟩ := exists_rig_of_frame FA' _ a'.sd
  obtain ⟨rW, eW, sW, hW⟩ := exists_rig_of_frame (frSum FV FV') _ hsd
  have hrk : (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank = rankV D (i + 1) (j + 1) + rankV D i j := by
    have h0 : (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank =
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank := rfl
    have h1 : (G.V (.grid i (j + 1))).rank = rankV D i (j + 1) := b.rank
    have h2 : (G.V (.grid (i + 1) j)).rank = rankV D (i + 1) j := b'.rank
    rw [h0, h1, h2]; simp only [rankV]; ring
  have htg : ∀ (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ AV → IsGridFr W _ AV₁ →
      rW.s = (frSum AV AV₁).cart := fun AV AV₁ h h₁ => by
    rw [sW]; funext τ
    rw [GlobalTheory.SquareAlg.cart_frSum, GlobalTheory.SquareAlg.cart_frSum, (h τ).2, (h₁ τ).2, (hFV τ).2, (hFV' τ).2]
  have ch := chars G hL W i j
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have rA1 : (G.V (.grid (i + 1) (j + 1))).rank = rankV D (i + 1) (j + 1) := a.rank
  have rA2 : (G.V (.grid i j)).rank = rankV D i j := a'.rank
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true (G.V (.grid (i + 1) (j + 1))) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (ch t).2.1
    (ch t).2.2.2.1 (by rw [rA1]; exact (ch t).2.2.2.2.2.1) (by rw [hrk]; exact (ch t).2.2.2.2.2.2.2)
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false (G.V (.grid i j)) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (ch t).1
    (ch t).2.2.1 (by rw [rA2]; exact (ch t).2.2.2.2.1) (by rw [hrk]; exact (ch t).2.2.2.2.2.2.1)
  have hneg' : IsSelfDualC (neg (G.V (.grid (i + 1) (j + 1)))) rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨vac, hv⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (neg (G.V (.grid (i + 1) (j + 1)))) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (fun τ => -rA.s τ) rW.s
    (sigOK_sgn true a.sigOK) hsig (fun τ => isCartanInv_sgn true _ τ (hA.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rA.Λ rW.Λ hneg' hW.1
  obtain ⟨vac', hv'⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (G.V (.grid i j)) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA'.s rW.s
    a'.sigOK hsig (fun τ => (hA'.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rA'.Λ rW.Λ hA'.1 hW.1
  choose e he using idem_exists G hL W
  choose c hc using fun t w => GlobalTheory.ConstRatio.exists_expAt (nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => _root_.GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D W.ψ W.θ _ (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA rW _ _ _ _ _ hA hW (ch t).2.2.1 (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    _root_.GlobalTheory.CompanionTheory.StdSndTheta.exists_theta D W.ψ W.θ _ (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA' rW _ _ _ _ (G.V (.grid (i + 1) (j + 1))).rank _ hA' hW (ch t).2.2.1 (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas (G.V (.grid (i + 1) (j + 1)))
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas (G.V (.grid i j))
  refine ⟨⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩,
    ⟨eA, eA', eW, sA.trans (funext fun τ => (hFA τ).2), sA'.trans (funext fun τ => (hFA' τ).2), htg⟩,
    le_rfl, le_rfl, by rw [rA1], by rw [rA2], ng a, ng a', hneg,
    ⟨by rw [hrk, rA1, rA2], hA, hA', hW, hω, hω', hv, hv', he, fun t w _ => hc t w, hf, hf', hm, hm'⟩⟩
end GlobalTheory.SqTower.TopGridExists
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grid_of_square_tower : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ X : TriG G i j, TopGrid W i j X ∧ IsStageC W i j (pp D j) (qq D j) X := by
  first | exact @_root_.GlobalTheory.SqTower.TopGridExists.square_tower_grid_exists | exact _root_.GlobalTheory.SqTower.TopGridExists.square_tower_grid_exists | (intros; apply _root_.GlobalTheory.SqTower.TopGridExists.square_tower_grid_exists <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsQuadraticTowerStage
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqTower.StageExists
set_option maxHeartbeats 1000000 in
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.HeckeCharsOfSquare in
theorem exists_quadratic_tower_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ)
    (A A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)), IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    p ≤ pp D j → q ≤ qq D j → A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p →
    A'.rank + 2 * qq D j = rankV D i j + 2 * q → NegIdx A p → NegIdx A' q → NegIdx WW (p + q) → A.rank + A'.rank = WW.rank →
      ∃ X : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j p q X ∧ X.rA.Λ = ΛA ∧ X.rA'.Λ = ΛA' ∧ X.rW.Λ = ΛW := by
  intro _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G W hψ i j p q A A' WW ΛA ΛA' ΛW sA sA' sW hp hq kA kA'
    nA nA' nW hrk => ?_⟩⟩
  obtain ⟨rA, eA, hA⟩ := rig_exists nA _ sA
  obtain ⟨rA', eA', hA'⟩ := rig_exists nA' _ sA'
  obtain ⟨rW, eW, hW⟩ := rig_exists nW _ sW
  have ch := TopExists.chars G hL W i j
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true A WW (ch t).2.1
    (ch t).2.2.2.1 (resEta_of_mod (ch t).2.2.2.2.2.1 (by omega)) (resEta_of_mod (ch t).2.2.2.2.2.2.2 (by omega))
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false A' WW (ch t).1
    (ch t).2.2.1 (resEta_of_mod (ch t).2.2.2.2.1 (by omega)) (resEta_of_mod (ch t).2.2.2.2.2.2.1 (by omega))
  obtain ⟨vac, hv⟩ := (vac_exists hψ hθ nA nW hA hW).1
  obtain ⟨vac', hv'⟩ := (vac_exists hψ hθ nA' nW hA' hW).2
  choose e he using TopExists.idem_exists G hL W
  choose c hc using fun t w => GlobalTheory.ConstRatio.exists_expAt (nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => _root_.GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D W.ψ W.θ _ WW rA rW _ _ _ _ _ hA hW (ch t).2.2.1 (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    _root_.GlobalTheory.CompanionTheory.StdSndTheta.exists_theta D W.ψ W.θ _ WW rA' rW _ _ _ _ A.rank _ hA' hW (ch t).2.2.1 (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas A
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas A'
  exact ⟨⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩,
    ⟨hp, hq, kA, kA', nA, nA', nW,
      ⟨hrk, hA, hA', hW, hω, hω', hv, hv', he, fun t w _ => hc t w, hf, hf', hm, hm'⟩⟩, eA, eA', eW⟩
end GlobalTheory.SqTower.StageExists
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_tower_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ)
    (A A' WW : HSp D) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)), IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    p ≤ pp D j → q ≤ qq D j → A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p →
    A'.rank + 2 * qq D j = rankV D i j + 2 * q → NegIdx A p → NegIdx A' q → NegIdx WW (p + q) → A.rank + A'.rank = WW.rank →
      ∃ X : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j p q X ∧ X.rA.Λ = ΛA ∧ X.rA'.Λ = ΛA' ∧ X.rW.Λ = ΛW := by
  first | exact @_root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage | exact _root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage | (intros; apply _root_.GlobalTheory.SqTower.StageExists.exists_quadratic_tower_stage <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FinitenessInputsRealDataThree
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow
theorem lamLow_closing_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCusp hWS hSWC hDM hUD hBZ hFD D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH
    hOk hSep hChar hEx hPrim hPhs hStd fw hBar hIo hPins hOne hTie hSizes hLow hNum hPar hStdV
  have hAd : AdelC R.toRealDat F.lv2 :=
    _root_.GlobalTheory.T.adelC_of_parameter_choice_stdV hCusp hWS hSWC hDM hUD hBZ hFD R.toRealDat F.lv2 hPar hStdV
  have hCore := (_root_.GlobalTheory.LowRow.baseLinks_of_prims R F s hOk hSep hChar hEx hPrim hPhs).1
  have hPT : PrimeToHost R.toRealDat A3.A.μ0 :=
    _root_.GlobalTheory.LowRow.primeToHost_base R.toRealDat F.lv2 (GlobalTheory.Core5.of_core hCore)
  exact _root_.GlobalTheory.LowRow.lamLow_of_weak _root_.GlobalTheory.ConjRatLiftFive.conjRatLift5 T R F κ v₀ O s b C CH hOk hSep hChar hEx hPrim hPhs hStd fw hBar
    hIo hPins hOne hTie hSizes hLow hNum hAd hPT
end GlobalTheory.LowRow
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteness_inputs_real_data_three_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  first | exact @_root_.GlobalTheory.LowRow.lamLow_closing_alt | exact _root_.GlobalTheory.LowRow.lamLow_closing_alt | (intros; apply _root_.GlobalTheory.LowRow.lamLow_closing_alt <;> assumption)
end
end

