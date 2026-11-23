module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StdWeylLatticesFgAndSpanCoeffSpace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRational
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatCoordA
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lca_span {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    nabStd K lam ≤ Submodule.span (𝓞 K) (MvPolynomial.map (Rat.castHom K) '' (nabStd ℚ lam : Set (Pol ℚ ι n))) := by
  have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K ℚ ι (Rat.castHom K)
    (RingOfIntegers.mapRingHom (Rat.castHom K)) (fun r => rfl) n lam).1
  have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
  rw [h1, ← h2]
  intro x hx
  exact Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩

private theorem lca_coord {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (lam : ι → DomWeight n) (x : Pol K ι n) (hx : x ∈ nabStd K lam) :
    ∃ v : VV ℂ lam, (v : Pol ℂ ι n) = MvPolynomial.map φ x ∧ ∀ i, ∃ o : 𝓞 K, (bVV ℂ lam).repr v i = φ (o : K) := by
  have hx' := lca_span lam hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    have hyV : y ∈ VV ℚ lam := by
      rw [← (GlobalTheory.StdLatSpan.std_fg_span ℚ ι n lam).2.2.1]
      exact Submodule.subset_span hy
    obtain ⟨Q, hQ⟩ := GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hy
    refine ⟨GlobalTheory.CoefModel.mapVV (φ.comp (Rat.castHom K)) lam ⟨y, hyV⟩, ?_, fun i => ?_⟩
    · rw [GlobalTheory.CoefModel.mapVV_coe, MvPolynomial.map_map]
    · obtain ⟨z, hz⟩ := UpperTheory.WildA.bvvInt lam (GlobalTheory.CoefModel.mapVV (φ.comp (Rat.castHom K)) lam ⟨y, hyV⟩) (fun m => by
        refine ⟨Rat.ringOfIntegersEquiv (AddMonoidAlgebra.coeff Q m), ?_⟩
        rw [GlobalTheory.CoefModel.mapVV_coe, MvPolynomial.coeff_map]
        have h2 : AddMonoidAlgebra.coeff y m = ((AddMonoidAlgebra.coeff Q m : 𝓞 ℚ) : ℚ) := by
          rw [← hQ]; exact MvPolynomial.coeff_map _ _ _
        change (φ.comp (Rat.castHom K)) (AddMonoidAlgebra.coeff y m) = _
        have h3 : ((AddMonoidAlgebra.coeff Q m : 𝓞 ℚ) : ℚ) = ((Rat.ringOfIntegersEquiv (AddMonoidAlgebra.coeff Q m) : ℤ) : ℚ) :=
          (Rat.ringOfIntegersEquiv_apply_coe _).symm
        rw [h2, h3, map_intCast]) i
      refine ⟨(z : 𝓞 K), ?_⟩
      rw [hz]
      simp
  | zero => exact ⟨0, by simp, fun i => ⟨0, by simp⟩⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, ha'⟩ := hy
    obtain ⟨b, hb, hb'⟩ := hz
    refine ⟨a + b, by simp [ha, hb], fun i => ?_⟩
    obtain ⟨o, ho⟩ := ha' i
    obtain ⟨p, hp⟩ := hb' i
    exact ⟨o + p, by simp [ho, hp]⟩
  | smul c y _ hy =>
    obtain ⟨a, ha, ha'⟩ := hy
    refine ⟨φ (c : K) • a, ?_, fun i => ?_⟩
    · ext m
      rw [Submodule.coe_smul, ha]
      simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
      change φ (c : K) * φ (y.coeff m) = φ ((c : K) * y.coeff m)
      rw [map_mul]
    · obtain ⟨o, ho⟩ := ha' i
      exact ⟨c * o, by simp [ho]⟩

private theorem lca_dual {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}
    (emb : ι → E →+* K) (τ : ι) :
    dualFr (tauLat emb τ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) =
      colLat (1 : GL (Fin n) K) := by
  classical
  apply le_antisymm
  · intro f hf
    have h1 : ∀ a, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = f a := fun a => by
      have := hf (Pi.single a 1) (Submodule.subset_span ⟨Pi.single a 1, fun j _ => by
        by_cases h : j = a
        · subst h; simpa using Submodule.mem_one.2 ⟨1, map_one _⟩
        · simp [h], by
        funext j
        by_cases h : j = a
        · subst h; simp
        · simp [h]⟩)
      rw [dotProduct_single, mul_one] at this
      exact Submodule.mem_one.1 this
    choose o ho using h1
    have e : f = ∑ j, o j • fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j := by
      funext a
      rw [Finset.sum_apply, Finset.sum_eq_single a]
      · simp [Algebra.smul_def, ho]
      · intro b _ hb
        simp [Matrix.one_apply, Ne.symm hb]
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩ x hx
    have e : (fun a : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a j) ⬝ᵥ x = x j := by
      simp [dotProduct, Matrix.one_apply]
    beta_reduce
    rw [e]
    clear e
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hy j (Set.mem_univ _))
      exact Submodule.mem_one.2 ⟨RingOfIntegers.mapRingHom (emb τ) o, by beta_reduce; rw [← ho]; rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy => exact Submodule.smul_mem _ c hy

theorem UpperTheory.WildA.latCoordA :
    ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal →
      ∀ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ (Formalism.MainNotions.StandardLatticesGL3.stdL D n) → ∀ (a : ℝ) (v : VV ℂ lam),
      InLat lam w a Λ v → ∀ i, LossLe w ((bVV ℂ lam).repr v i) a := by
  intro D n lam w l _ hw Λ hΛ a v hv i
  obtain ⟨N, hN, h1, h2⟩ := hΛ
  obtain ⟨u, s, huv, hs0, hsa, hsu⟩ := hv
  have hNw := GlobalTheory.GO.natCast_notMem_of_coprime hN w hw
  have h1' : ∀ x ∈ Λ, N • x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D n := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h1 x hx
  have h2' : ∀ x ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D n, N • x ∈ Λ := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h2 x hx
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (labLL D) τ Λ)) ((1 : D.what₂.Tau → GL (Fin n) D.what₂.LL) τ) := fun τ => by
    unfold IsBasisAt
    rw [Pi.one_apply, ← lca_dual (labLL D) τ]
    exact le_antisymm (GlobalTheory.GO.localization_dualFr_tauLat_le (labLL D) τ h2' w hNw)
      (GlobalTheory.GO.localization_dualFr_tauLat_le (labLL D) τ h1' w hNw)
  have h3 : ((s • u : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau n) ∈
      transLat lam (nabStd D.what₂.LL lam) (fun τ => dualFr (tauLat (labLL D) τ Λ)) := hsu
  unfold transLat at h3
  simp only [Submodule.mem_iInf] at h3
  have h4 : actP lam (1 : D.what₂.Tau → GL (Fin n) D.what₂.LL)⁻¹ ((s • u : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau n) ∈
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd D.what₂.LL lam) := h3 w 1 hB
  have h5 : ∀ F : Pol D.what₂.LL D.what₂.Tau n, actP lam (1 : D.what₂.Tau → GL (Fin n) D.what₂.LL)⁻¹ F = F := fun F => by
    rw [inv_one]
    simp [actP, detTwK_one, trAct_one]
  rw [h5] at h4
  obtain ⟨c, hc, hcF⟩ := h4
  have hc' : c ∉ w.asIdeal := hc
  have hc0 : (c : D.what₂.LL) ≠ 0 := by
    intro h0
    have : c = 0 := RingOfIntegers.ext h0
    exact hc' (this ▸ w.asIdeal.zero_mem)
  obtain ⟨v', hv', ho⟩ := lca_coord D.what₂.embLL lam _ hcF
  obtain ⟨o, ho⟩ := ho i
  have e : v' = D.what₂.embLL ((c : D.what₂.LL) * s) • v := by
    rw [← huv, ← LinearMap.map_smulₛₗ]
    apply Subtype.ext
    rw [hv', GlobalTheory.CoefModel.mapVV_coe, mul_smul]
    rfl
  have hcs : (c : D.what₂.LL) * s ≠ 0 := mul_ne_zero hc0 hs0
  refine ⟨((c : D.what₂.LL) * s)⁻¹ * o, ?_, ?_⟩
  · rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul] at ho
    rw [map_mul, ← ho, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcs, map_one, one_mul]
  · by_cases h0 : (o : D.what₂.LL) = 0
    · left; rw [h0, mul_zero]
    · right
      have h6 := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w o
      rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (inv_ne_zero hcs) h0, Formalism.DivisionValues.ValuationRepresentative.vw_inv, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hc0 hs0,
        GlobalTheory.LocInt.vw_eq_zero_of_notMem w hc', zero_add]
      have h7 : (0 : ℝ) ≤ (vw w (o : D.what₂.LL) : ℝ) := by exact_mod_cast h6
      push_cast
      linarith
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RealTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MvPolynomial Formalism.L2.Ker in
private theorem jetMap_smul' {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (n : ι → ℕ) (P : Pol ℂ ι a) :
    jetMap (fun m => c * J m) n P = c • jetMap J n P := by
  have h : jetLin (fun m => c * J m) = c • jetLin J := by
    refine (basisMonomials _ ℂ).ext fun m => ?_
    rw [coe_basisMonomials]
    simp only [LinearMap.smul_apply]
    rw [GlobalTheory.KerT.RatLaw.jetLin_monomial, GlobalTheory.KerT.RatLaw.jetLin_monomial, smul_monomial, smul_eq_mul]
  simp only [jetMap, LinearMap.comp_apply, h, LinearMap.smul_apply]

open MvPolynomial Formalism.L2.Ker in
private theorem jetMap_substF {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (ℓ : MvPolynomial (DVar ι a b) ℂ →ₗ[ℂ] ℂ)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (n : ι → ℕ) (P : Pol ℂ ι a) :
    jetMap (fun m => c * ℓ (GlobalTheory.CompactHowe.substF h (fun τ => (g τ)ᵀ) (monomial m 1))) n P =
      (c * ∏ τ, (g τ).det ^ n τ) • GlobalTheory.KJInf.lft h (jetMap (fun m => ℓ (monomial m 1)) n (GlobalTheory.KJInf.lft g P)) := by
  have e1 : GlobalTheory.KerT.RatLaw.tabFn (fun m => ℓ (monomial m 1)) = ℓ := by
    refine (basisMonomials _ ℂ).ext fun m => ?_
    rw [coe_basisMonomials]
    exact GlobalTheory.KerT.RatLaw.tabFn_monomial _ m
  have e2 : GlobalTheory.CompactHowe.substF h (fun τ => (g τ)ᵀ) = aeval (GlobalTheory.KerT.RatLaw.subst g h) := by
    refine algHom_ext fun v => ?_
    simp only [GlobalTheory.CompactHowe.substF_X, aeval_X, Matrix.transpose_apply]
  rw [jetMap_smul', GlobalTheory.KerT.RatLaw.jetMap_subst (J := fun m => ℓ (monomial m 1)) g h (fun m => by rw [e1, e2]), mul_smul]
  rfl

open GlobalTheory.ColKer GlobalTheory.RowHoweAvg in
theorem UpperTheory.WildA.realTop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} (N : Std G U₀) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m →
      ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (GlobalTheory.ChiGrid.Pair.top t j)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (GlobalTheory.ChiGrid.Pair.top t j)) τ (b τ)) →
      ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.top t j) * (G.pS (GlobalTheory.ChiGrid.Pair.top t j)).rank / 2) →
        (∀ τ, (e₂ τ : ℚ) = -(b τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.top t j) * (G.pT (GlobalTheory.ChiGrid.Pair.top t j)).rank / 2)) →
      ∀ (ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.top t j)).rank (G.pS (GlobalTheory.ChiGrid.Pair.top t j)).rank →ₗ[ℂ] ℂ) (k : GA D (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).small)), k ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).small) →
      ∀ k' : GA D (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).big), k' ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.top t j)).big) →
        Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).small) (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).big) (fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.top t j) e₁ e₂ k k' *
                  ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.top t j) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t j))) 1))) (nuEnd G (GlobalTheory.ChiGrid.Pair.top t j)) =
          GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.top t j)).big k'⁻¹ ∘ₗ
            Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).small) (wt G ((GlobalTheory.ChiGrid.Pair.top t j)).big) (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.top t j))) 1)) (nuEnd G (GlobalTheory.ChiGrid.Pair.top t j)) ∘ₗ
            GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.top t j)).small k := by
  intro D T L sc G W U₀ N μ₀ hL t j hj a b ha hb e₁ e₂ he₁ he₂ ℓ k _ k' _
  have hp : DefPair D.R.m (Pair.top t j) := hj
  have hj' : j < D.R.m := hj
  have hJ := (wtOK_of_defPair G _ hp).2
  have hr0 : Even (G.V (.top j)).rank := by rw [rank_top G (j := j) (by omega)]; exact rankX_even D j
  have hr1 : Even (G.V (.top (j + 1))).rank := by rw [rank_top G (j := j + 1) (by omega)]; exact rankX_even D (j + 1)
  have hS : G.chrS (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pS, Nat.not_odd_iff_even.2 hr0, if_false]
  have hT : G.chrT (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
  have h1 : ∀ τ, e₁ τ = (wt G (.top (j + 1)) τ).detShift := fun τ => by
    have ea := GlobalTheory.Mem.HeckeExp.hasInfExp_unique (hS ▸ ha τ) (mu_exp hL t j hj' τ)
    have := (detShift_top G t j hj' τ).1
    have h : (e₁ τ : ℚ) = ((wt G (.top (j + 1)) τ).detShift : ℤ) := by
      rw [he₁, this, ea]; simp only [GlobalTheory.FockReal.sgnP, one_mul]
    exact_mod_cast h
  have h2 : ∀ τ, e₂ τ = (nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift := fun τ => by
    have eb := GlobalTheory.Mem.HeckeExp.hasInfExp_unique (hT ▸ hb τ) (mu_exp hL t j hj' τ)
    have := (detShift_top G t j hj' τ).2
    have h : (e₂ τ : ℚ) = (((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift : ℤ) : ℚ) := by
      rw [he₂, this, eb]; simp only [GlobalTheory.FockReal.sgnP, one_mul]
    exact_mod_cast h
  have hinv : GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (N.frC (.top j)) k⁻¹ =
      fun τ => (GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (N.frC (.top j)) k τ)⁻¹ := by
    funext τ
    rw [← realIn_coe, ← realIn_coe, map_inv, Pi.inv_apply, Matrix.coe_units_inv]
  have hne : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k)).det ≠ 0 := fun τ => by
    rw [← det_inB W.θ N, ← realIn_coe]
    exact (Matrix.isUnits_det_units _).ne_zero
  have hdi : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k⁻¹)).det =
      (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k)).det⁻¹ := fun τ => by
    rw [← det_inB W.θ N, ← det_inB W.θ N, hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hm : ∀ m : Formalism.L2.Ker.DVar D.what₂.Tau (G.V (Pair.top t j).small).rank (G.V (Pair.top t j).big).rank →₀ ℕ,
      Finsupp.mapDomain (fvar G (Pair.top t j)) m = m := fun m => Finsupp.mapDomain_id
  have hs : GlobalTheory.FockReal.realSubst W N.frC (Pair.top t j) k k' =
      GlobalTheory.CompactHowe.substF (GlobalTheory.SeeSaw.inB W.θ (G.V (.top (j + 1))) (N.frC (.top (j + 1))) k')
        (fun τ => (GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (N.frC (.top j)) k⁻¹ τ)ᵀ) := by
    rw [hinv]
    rfl
  refine LinearMap.ext fun v => Subtype.ext ?_
  have e0 := realAct_inv_coe W.θ N (.top j) k⁻¹ v
  rw [inv_inv] at e0
  simp only [hm, hs, LinearMap.comp_apply]
  rw [jetOp_coe hJ, realAct_inv_coe, jetOp_coe hJ]
  refine (jetMap_substF _ ℓ _ _ _ _).trans ?_
  erw [e0]
  rw [map_smul, map_smul, smul_smul]
  congr 1
  simp only [GlobalTheory.FockReal.realChar, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_inB, hdi, h1, h2]
  show (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.top j)) k)).det ^ _ * _ * _ = _
  rw [zpow_sub₀ (hne τ), zpow_natCast, inv_pow, _root_.inv_zpow]
  have := pow_ne_zero (nuEnd G (.top t j) τ) (hne τ)
  field_simp
  try rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.WtBdWtOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
open GlobalTheory.SignedHC

private theorem wtBd_wtOf (n : ℕ) (E : Finset ℚ) (B : ℝ) (hB : 0 ≤ B) (hE : ∀ x ∈ E, |(x : ℝ)| ≤ B)
    (a a' : Fin n) (h : a ≤ a') : (((wtOf n E).w a - (wtOf n E).w a' : ℤ) : ℝ) ≤ 2 * B := by
  by_cases hc : E.card = n ∧ InCoset (((n : ℚ) - 1) / 2) E
  · have e1 := wtOf_cast hc.1 hc.2 a
    have e2 := wtOf_cast hc.1 hc.2 a'
    have b1 := abs_le.1 (hE _ (descEnum_mem E hc.1 a))
    have b2 := abs_le.1 (hE _ (descEnum_mem E hc.1 a'))
    unfold highestWeight at e1 e2
    have e1' := congrArg (fun q : ℚ => (q : ℝ)) e1
    have e2' := congrArg (fun q : ℚ => (q : ℝ)) e2
    have h' : ((a : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at e1' e2' ⊢
    linarith [b1.1, b1.2, b2.1, b2.2]
  · rw [wtOf, dite_eq_right hc]
    simp only [Pi.zero_apply, sub_self, Int.cast_zero]
    linarith

private theorem wtBd_natW {n : ℕ} (lam : DomWeight n) (C : ℝ)
    (h : ∀ a a' : Fin n, a ≤ a' → ((lam.w a - lam.w a' : ℤ) : ℝ) ≤ C) (a : Fin n) :
    ((lam.natW a : ℕ) : ℝ) ≤ C := by
  have hn : 0 < n := a.pos
  have hle : a ≤ (⟨n - 1, by omega⟩ : Fin n) := by
    have := a.2
    show a.1 ≤ n - 1
    omega
  have h1 := h a _ hle
  have h2 := lam.anti hle
  have h3 : ((lam.natW a : ℕ) : ℤ) = lam.w a - lam.w ⟨n - 1, by omega⟩ := by
    unfold DomWeight.natW DomWeight.detShift
    rw [dite_eq_left hn]
    exact Int.toNat_of_nonneg (by linarith)
  rw [← h3] at h1
  exact_mod_cast h1

private theorem wtBd_dual {n : ℕ} (lam : DomWeight n) (C : ℝ)
    (h : ∀ a a' : Fin n, a ≤ a' → ((lam.w a - lam.w a' : ℤ) : ℝ) ≤ C) (a a' : Fin n) (haa : a ≤ a') :
    ((lam.dual.w a - lam.dual.w a' : ℤ) : ℝ) ≤ C := by
  have h1 := h a'.rev a.rev (Fin.rev_le_rev.2 haa)
  have e : lam.dual.w a - lam.dual.w a' = lam.w a'.rev - lam.w a.rev := by
    show -lam.w a.rev - -lam.w a'.rev = _
    ring
  rw [e]; exact h1

end

theorem UpperTheory.WildA.wtBd :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → sc.cGap = 1 → ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p →
      ∀ τ a, (((wt G p.big τ).natW a : ℕ) : ℝ) ≤ 12 * large₂.sc.b := by
  intro D T L sc G large₂ hS hH hc p hp τ
  obtain ⟨-, -, -, -, -, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS
  have key : ∀ X : Node, DefNode D.R.m X → ∀ a, (((wt G X τ).natW a : ℕ) : ℝ) ≤ 12 * large₂.sc.b := by
    intro X hX
    have hb := UpperTheory.WildA.parBd D large₂ hS hH X hX τ
    rw [← hc] at hb
    have hl : ∀ a a', a ≤ a' → (((listedWt G X τ).w a - (listedWt G X τ).w a' : ℤ) : ℝ) ≤ 12 * large₂.sc.b := by
      intro a a' h
      have := wtBd_wtOf (G.V X).rank _ (6 * large₂.sc.b) (by linarith) hb a a' h
      unfold listedWt
      linarith
    cases X with
    | core i => exact hX.elim
    | top j => exact wtBd_natW _ _ hl
    | grid i j => exact wtBd_natW _ _ (wtBd_dual _ _ hl)
  exact key p.big hp.nodes.2
end

