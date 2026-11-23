module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDomInt
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open DiscreteGroups.T1.G
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

private theorem pow_mul_exp_neg_le (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-r) ≤ N.factorial * Real.exp 1 := by
  have h := Real.pow_div_factorial_le_exp (1 + r) (by linarith) N
  rw [div_le_iff₀ (by exact_mod_cast N.factorial_pos)] at h
  have e : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
  calc (1 + r) ^ N * Real.exp (-r) ≤ (Real.exp (1 + r) * N.factorial) * Real.exp (-r) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = N.factorial * Real.exp 1 * (Real.exp r * Real.exp (-r)) := by rw [Real.exp_add]; ring
    _ = N.factorial * Real.exp 1 := by rw [e, mul_one]

private theorem point_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hB : Basic) (hS : Sizes)
    (hn : 1 ≤ n) {π : CuspSub E n} (hθ : ThetaFix π) {ψ : Sm E n} (hψ : ψ ∈ π.V) (M : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R ρ : ℝ, 0 ≤ R → ∀ x : H E n 0, |ldet x| ≤ R → ρ ≤ r0 x →
      ‖ψ.1 x.1‖ ≤ A * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) * wt x ^ (-(2 * M : ℤ)) := by
  obtain ⟨h1, h2, -⟩ := hB E n hn
  obtain ⟨c, hc0, hc⟩ := hS E n hn
  have hA := hθ.1 ψ hψ
  obtain ⟨C₀, hC₀⟩ := Dcy.cp_decay ψ (π.cusp ψ hψ) hA 0 (L + 1)
  set a : ℝ := redSize (1 : GA E 0) with ha
  have ha0 : 0 ≤ a := Dcy.redSize_nonneg _
  set c₁ : ℝ := 2 + a + c with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set C : ℝ := max C₀ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  set K : ℝ := ((2 * M).factorial : ℝ) * Real.exp 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C * c₁ ^ (2 * M) * K, by positivity, fun R ρ hR x hx hρ => ?_⟩
  obtain ⟨hs, -, hr⟩ := hc x
  set r : ℝ := r0 x with hrdef
  set y : H E n 0 := ac E n (-ldet x) * x with hy
  have hy0 : ldet y = 0 := by rw [hy, h2, h1]; ring
  have hψy : ψ.1 y.1 = ψ.1 x.1 := hA _ _
  have hdec : ‖ψ.1 x.1‖ ≤ C * Real.exp (-((L + 1) * r)) := by
    have h := hC₀ y.1 (by
      have : |ldet y| ≤ 0 := by rw [hy0]; simp
      exact this)
    rw [hψy] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hx2 : x.2 = 1 := Units.ext (Subsingleton.elim _ _)
  have hw : wt x = 1 + redSize x.1 + a := by rw [wt, hx2]
  have hrs := Dcy.redSize_nonneg x.1
  have hw1 : 1 ≤ wt x := by rw [hw]; linarith
  have hP : 1 ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
  have hwle : wt x ≤ c₁ * ((1 + r) * (1 + R)) := by
    have h3 : c * (1 + |ldet x|) ≤ c * (1 + R) := mul_le_mul_of_nonneg_left (by linarith) hc0
    have h4 : 1 + R ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
    have h5 : 1 + r ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
    have h6 : c * (1 + R) ≤ c * ((1 + r) * (1 + R)) := mul_le_mul_of_nonneg_left h4 hc0
    have h7 : (1 + a) * 1 ≤ (1 + a) * ((1 + r) * (1 + R)) := mul_le_mul_of_nonneg_left hP (by linarith)
    rw [hw, hc₁]
    nlinarith
  have hexp : Real.exp (-((L + 1) * r)) ≤ Real.exp (-(L * ρ)) * Real.exp (-r) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hρ hL]
  have hpow : wt x ^ (2 * M) ≤ c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * (1 + R) ^ (2 * M)) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hwle _
  have hwpos : 0 < wt x ^ (2 * M) := pow_pos (by linarith) _
  have hz : wt x ^ (-(2 * M : ℤ)) = (wt x ^ (2 * M))⁻¹ := by
    rw [_root_.zpow_neg]
    congr 1
  have hr1 : 0 ≤ 1 + r := by linarith
  have hR1 : 0 ≤ 1 + R := by linarith
  have hmain : ‖ψ.1 x.1‖ * wt x ^ (2 * M) ≤ C * c₁ ^ (2 * M) * K * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by
    have hq := pow_mul_exp_neg_le (2 * M) hr
    calc ‖ψ.1 x.1‖ * wt x ^ (2 * M)
        ≤ (C * (Real.exp (-(L * ρ)) * Real.exp (-r))) *
            (c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * (1 + R) ^ (2 * M))) :=
          mul_le_mul (hdec.trans (mul_le_mul_of_nonneg_left hexp hC0)) hpow hwpos.le (by positivity)
      _ = C * c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * Real.exp (-r)) * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by ring
      _ ≤ C * c₁ ^ (2 * M) * K * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by
          gcongr
  rw [hz, ← div_eq_mul_inv, le_div_iff₀ hwpos]
  exact hmain

theorem domInt_pf : Basic → Sizes → DomInt := by
  intro hB hS E _ _ _ n hn D π hθ ψ hψ Ω hΩ
  refine ⟨2 * (2 * n), fun L hL => ?_⟩
  obtain ⟨A, hA0, hA⟩ := point_bound hB hS hn hθ hψ (2 * n) L hL
  have hI := wtCount E n 0 D Ω hΩ (2 * n) (by omega)
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * ((2 * n : ℕ) : ℤ)))) * cnt (ratH E n 0) Ω x ∂D.ν with hIdef
  refine ⟨A * I.toReal, mul_nonneg hA0 ENNReal.toReal_nonneg, fun R ρ hR => ?_⟩
  set B : ℝ := A * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ)) with hBdef
  have hR1 : 0 ≤ 1 + R := by linarith
  have hB0 : 0 ≤ B := by positivity
  calc ∫⁻ x, {x | |ldet x| ≤ R ∧ ρ ≤ r0 x}.indicator (fun x => ‖ψ.1 x.1‖ₑ * cnt (ratH E n 0) Ω x) x ∂D.ν
      ≤ ∫⁻ x, ENNReal.ofReal B * (ENNReal.ofReal (wt x ^ (-(2 * ((2 * n : ℕ) : ℤ)))) * cnt (ratH E n 0) Ω x) ∂D.ν := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ {x : H E n 0 | |ldet x| ≤ R ∧ ρ ≤ r0 x}
        · rw [Set.indicator_of_mem hx, ← mul_assoc, ← ENNReal.ofReal_mul hB0, ← ofReal_norm]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hA R ρ hR x hx.1 hx.2)) _
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
    _ = ENNReal.ofReal B * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A * I.toReal * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ))) := by
        rw [show A * I.toReal * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ)) = B * I.toReal by rw [hBdef]; ring,
          ENNReal.ofReal_mul hB0, ENNReal.ofReal_toReal hI]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PEvalBasis
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.evalBasis_pf :
    EvalBasis := by
  intro X V _ _ ev hsep W hW
  classical
  haveI := hW
  let r : X → Module.Dual ℂ W := fun x => (ev x).domRestrict W
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ W).surjective f
    have hv : (v : V) = 0 := hsep v fun x => by
      have h := hf (Submodule.subset_span (Set.mem_range_self x))
      simpa [r] using h
    have hv0 : v = 0 := Subtype.ext hv
    exact hf0 (by simp [hv0])
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent ℂ (Set.range r)
  let B0 := Module.Basis.mk hli (by simp [hbspan, hspan])
  haveI : Finite b := Module.Finite.finite_basis B0
  letI := Fintype.ofFinite b
  let B := B0.reindex (Fintype.equivFin b)
  have hx : ∀ i, ∃ x, r x = B i := fun i => by
    have hm : B i ∈ b := by simp [B, B0]
    exact hbs hm
  choose x hx using hx
  refine ⟨Fintype.card b, x, fun i => ((Module.evalEquiv ℂ W).symm (B.coord i) : W),
    fun i => Subtype.coe_prop _, fun v hv => ?_⟩
  have key : (⟨v, hv⟩ : W) = ∑ i, (B i ⟨v, hv⟩) • (Module.evalEquiv ℂ W).symm (B.coord i) := by
    apply (Module.evalEquiv ℂ W).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    exact (B.sum_dual_apply_smul_coord _).symm
  have h2 := congrArg (Subtype.val) key
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hx i]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PFinFac
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private def evAt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CuspSub E n) (x : H E n 0) :
    π.V →ₗ[ℂ] ℂ where
  toFun ψ := ψ.1.1 x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finFac_pf :
    Basic → EvalBasis → FinGen → FinFac := by
  intro hB hE hG E _ _ _ n ι _ s
  obtain ⟨hl, hmul, -⟩ := hB E n s.pos
  obtain ⟨W, hWV, hWf, hW⟩ := hG E n ι s
  have sep : ∀ ψ : s.π.V, (∀ x : {x : H E n 0 // ldet x = 0}, evAt s.π x.1 ψ = 0) → ψ = 0 := by
    intro ψ h
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have hy : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hl]; ring
    have h0 := h ⟨_, hy⟩
    have h1 := s.fix.1 ψ.1 ψ.2 (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) g
    exact h1.symm.trans h0
  haveI : FiniteDimensional ℂ W := hWf
  obtain ⟨d, xs, ws, hw, hrep⟩ := hE {x : H E n 0 // ldet x = 0} s.π.V (fun x => evAt s.π x.1) sep
    (LinearMap.range (Submodule.inclusion hWV)) inferInstance
  refine ⟨{ B := Fin d, w := fun b => (ws b).1, x := fun b => (xs b).1, mem := fun b => (ws b).2,
            zero := fun b => (xs b).2 }, ?_⟩
  have key : ∀ v : Hs (ι := ι) s.D, IsPiVec s.D s.π v → ∀ (x : H E n 0) (i : ι),
      inner ℂ (s.k₁ x i) v =
        ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v := by
    intro v hv x i
    obtain ⟨ψ, hψ, hval⟩ := hW v hv i (ldet x)
    have hb : ∀ b, inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v = ψ.1 (xs b).1.1 := by
      intro b
      rw [hval _ (by rw [hmul, hl, (xs b).2, add_zero])]
      exact s.fix.1 ψ (hWV hψ) _ _
    have hr := congrArg (evAt s.π x) (hrep ⟨ψ, hWV hψ⟩ ⟨⟨ψ, hψ⟩, rfl⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at hr
    rw [hval x rfl]
    refine hr.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [map_smul, hb b, smul_eq_mul, mul_comm]
    rfl
  intro v hv x i
  let L : Hs (ι := ι) s.D →L[ℂ] ℂ := innerSL ℂ (s.k₁ x i) -
    ∑ b, (ws b).1.1 x.1 • innerSL ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i)
  have hL : ∀ f, L f = inner ℂ (s.k₁ x i) f -
      ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) f := by
    intro f
    simp [L, ContinuousLinearMap.sum_apply]
  have hle : Submodule.span ℂ {f | IsPiVec s.D s.π f} ≤ LinearMap.ker (L : Hs (ι := ι) s.D →ₗ[ℂ] ℂ) :=
    Submodule.span_le.2 fun f hf => by
      have := key f hf x i
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [hL, this, sub_self]
  have hv' : v ∈ closure ((Submodule.span ℂ {f | IsPiVec s.D s.π f} : Submodule ℂ (Hs (ι := ι) s.D)) : Set (Hs (ι := ι) s.D)) := hv
  have h0 : L v = 0 :=
    closure_minimal (t := {f | L f = 0}) (fun f hf => LinearMap.mem_ker.1 (hle hf))
      (isClosed_eq L.continuous continuous_const) hv'
  rw [hL] at h0
  exact sub_eq_zero.1 h0

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PFinGen
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ker_integral_shift (X : Ctx) {φ f : X.G → ℂ} (hφ : Tst φ)
    (hinv : ∀ γ : X.Γ, ∀ y, f ((γ : X.G) * y) = f y) (hf : MemLp f 2 X.ν) (x : X.G) :
    ∫ y, ker X.Γ φ x y * f y ∂X.ν = ∫ z, φ z * f (x * z) ∂X.μ := by
  rw [(unfold X kerBasic kernel_rows_columns_square_integrable hφ hinv hf x).2,
    ← integral_mul_left_eq_self (fun y => φ (x⁻¹ * y) * f y) x]
  simp only [inv_mul_cancel_left]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finGen_pf :
    Basic → FinGen := by
  intro hB E _ _ _ n ι _ s
  classical
  obtain ⟨-, hmul, -, -, -, -, -, -, -, hrat, -, -⟩ := hB E n s.pos
  choose W hWle hWfd hW using s.fin
  have hfd : FiniteDimensional ℂ (⨆ p : ι × ι, W p.1 p.2 : Submodule ℂ (Sm E n)) := by
    haveI : ∀ p : ι × ι, FiniteDimensional ℂ (W p.1 p.2) := fun p => hWfd _ _
    exact Submodule.finiteDimensional_iSup _
  refine ⟨⨆ p : ι × ι, W p.1 p.2, iSup_le fun p => hWle _ _, hfd, ?_⟩
  intro v hv i t
  choose ψ hψ u hu hu' hvu using hv
  let X : Ctx := by
    haveI := CuspidalL2GL.t2Space_GA E n
    haveI := CuspidalL2GL.t2Space_GA E 0
    haveI := CuspidalL2GL.locallyCompactSpace_GA E n
    haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
    haveI := CuspidalL2GL.secondCountableTopology_GA E n
    haveI := CuspidalL2GL.secondCountableTopology_GA E 0
    haveI := (ratProper_holds E n).2.1
    haveI := (ratProper_holds E 0).2.1
    exact { G := H E n 0
            ms := borelH E n 0
            bs := ⟨rfl⟩
            μ := s.D.μ
            haar := { toIsFiniteMeasureOnCompacts :=
                        @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ s.D.μ s.D.haar.2.2.2
                      toIsMulLeftInvariant := s.D.haar.1
                      toIsOpenPosMeasure := s.D.haar.2.2.1 }
            Γ := ratH E n 0
            cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
            proper := by
              intro C hC
              have h1 := (ratProper_holds E n).2.2 _ (hC.image continuous_fst)
              have h2 := (ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
              refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
              rintro ⟨_, γ, rfl⟩ hγ
              exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
            F := s.D.F
            fd := s.D.fd }
  have hform : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), (ψ j).1 ((γ : H E n 0) * y).1 = (ψ j).1 y.1 := by
    intro j γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp _ (hψ j)).1.left γ₁ y.1
  set Ft : ι → H E n 0 → ℂ := fun j x => (ψ j).1 x.1 * u j (ldet x) with hFt
  have hinv : ∀ j, ∀ (γ : ratH E n 0) (y : H E n 0), Ft j ((γ : H E n 0) * y) = Ft j y := by
    intro j γ y
    simp only [hFt, hform j γ y, hmul, (hrat γ).1, zero_add]
  have hmem : ∀ j, MemLp (Ft j) 2 s.D.ν := fun j => (Lp.memLp (v j)).ae_eq (hvu j)
  have hex : ∀ j, ∃ ψ' ∈ W i j, ∀ g, ψ'.1 g =
      ∫ y, s.Φ₁ i j y * (fun r => u j (t + r)) (ldet y) * (ψ j).1 (g * y.1) ∂s.D.μ := fun j =>
    hW i j (fun r => u j (t + r)) ((hu j).comp (continuous_const.add continuous_id)) (ψ j) (hψ j)
  choose ψ' hψ' hval using hex
  refine ⟨∑ j, ψ' j, Submodule.sum_mem _ fun j _ =>
    (le_iSup (fun p : ι × ι => W p.1 p.2) (i, j)) (hψ' j), fun x hx => ?_⟩
  rw [s.vecs.rep₁]
  have hsum : (∑ j, ψ' j).1 x.1 = ∑ j, (ψ' j).1 x.1 := by
    simp [Submodule.coe_sum]
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hae : ∫ y, kerH (s.Φ₁ i j) x y * (v j : H E n 0 → ℂ) y ∂s.D.ν =
      ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν :=
    integral_congr_ae ((hvu j).mono fun y hy => by simp only [hy, hFt])
  rw [hae, hval j]
  have hs : ∫ y, kerH (s.Φ₁ i j) x y * Ft j y ∂s.D.ν = ∫ z, s.Φ₁ i j z * Ft j (x * z) ∂s.D.μ :=
    ker_integral_shift X (φ := s.Φ₁ i j) (f := Ft j) (s.t₁ i j) (hinv j) (hmem j) x
  refine hs.trans (integral_congr_ae (Filter.Eventually.of_forall fun z => ?_))
  show s.Φ₁ i j z * ((ψ j).1 (x * z).1 * u j (ldet (x * z))) =
    s.Φ₁ i j z * u j (t + ldet z) * (ψ j).1 (x.1 * z.1)
  rw [hmul, hx, Prod.fst_mul]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PGBound
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem cnt_le_sq {G : Type} [Group G] (Γ : Subgroup G) (Ω : Set G) (x : G) :
    cnt Γ Ω x ≤ cnt Γ Ω x ^ 2 := by
  by_cases h : ∃ γ : Γ, x⁻¹ * (γ : G) * x ∈ Ω
  · obtain ⟨γ, hγ⟩ := h
    have h1 : 1 ≤ cnt Γ Ω x := by
      have h2 := ENNReal.le_tsum (f := fun γ : Γ => Ω.indicator (1 : G → ℝ≥0∞) (x⁻¹ * (γ : G) * x)) γ
      have h3 : Ω.indicator (1 : G → ℝ≥0∞) (x⁻¹ * (γ : G) * x) = 1 := by
        rw [Set.indicator_of_mem hγ]; rfl
      rw [h3] at h2
      exact h2
    rw [sq]
    exact le_mul_of_one_le_left zero_le h1
  · have h0 : cnt Γ Ω x = 0 := by
      unfold cnt
      refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem (fun hm => h ⟨γ, hm⟩) _
    simp [h0]

private theorem cnt_central {G : Type} [Group G] (Γ : Subgroup G) (Ω : Set G) (a x : G)
    (ha : ∀ y, a * y = y * a) : cnt Γ Ω (a * x) = cnt Γ Ω x := by
  unfold cnt
  refine tsum_congr fun γ => ?_
  have e : (a * x)⁻¹ * (γ : G) * (a * x) = x⁻¹ * (γ : G) * x := by
    have h1 : (γ : G) * a = a * (γ : G) := (ha _).symm
    calc (a * x)⁻¹ * (γ : G) * (a * x) = x⁻¹ * a⁻¹ * ((γ : G) * a) * x := by group
      _ = x⁻¹ * (γ : G) * x := by rw [h1]; group
  rw [e]

private theorem norm_part_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (K : Submodule ℂ V) [K.HasOrthogonalProjection] (U Up : V →L[ℂ] V)
    (h1 : ∀ f ∈ K, Up f = U f) (h2 : ∀ f ∈ Kᗮ, Up f = 0) : ‖Up‖ ≤ ‖U‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
  have e : Up f = U (K.starProjection f) := by
    have h3 : f = K.starProjection f + (f - K.starProjection f) := by abel
    calc Up f = Up (K.starProjection f) + Up (f - K.starProjection f) := by
          rw [← map_add (f := _), ← h3]
      _ = U (K.starProjection f) := by
          rw [h2 _ (K.sub_starProjection_mem_orthogonal f), add_zero,
            h1 _ (K.starProjection_apply_mem f)]
  rw [e]
  refine (U.le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left (K.norm_starProjection_apply_le f) (norm_nonneg _)

private theorem le_ofReal_sqrt {e : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (h : e ^ 2 ≤ ENNReal.ofReal r) :
    e ≤ ENNReal.ofReal (Real.sqrt r) := by
  refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hr]
  exact h

private theorem enorm_inner_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a b : V) (T U : V →L[ℂ] V) (hT : ‖T‖ ≤ ‖U‖) (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (c : ℝ≥0∞)
    (ha : ‖a‖ₑ ≤ ENNReal.ofReal P) (hb : ‖b‖ₑ ≤ ENNReal.ofReal Q * c) :
    ‖(inner ℂ a (T b) : ℂ)‖ₑ ≤ ENNReal.ofReal (P * Q * ‖U‖) * c := by
  have h1 : ‖(inner ℂ a (T b) : ℂ)‖ ≤ ‖a‖ * (‖U‖ * ‖b‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((T.le_opNorm b).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))) (norm_nonneg _))
  calc ‖(inner ℂ a (T b) : ℂ)‖ₑ = ENNReal.ofReal ‖(inner ℂ a (T b) : ℂ)‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖a‖ * (‖U‖ * ‖b‖)) := ENNReal.ofReal_le_ofReal h1
    _ = ‖a‖ₑ * (ENNReal.ofReal ‖U‖ * ‖b‖ₑ) := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm]
    _ ≤ ENNReal.ofReal P * (ENNReal.ofReal ‖U‖ * (ENNReal.ofReal Q * c)) := by gcongr
    _ = ENNReal.ofReal (P * Q * ‖U‖) * c := by
        rw [ENNReal.ofReal_mul (mul_nonneg hP hQ), ENNReal.ofReal_mul hP]
        ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.gBound_pf :
    Basic → GBound := by
  intro hB E _ _ _ n ι _ s
  obtain ⟨-, -, hcomm, -⟩ := hB E n s.pos
  obtain ⟨C₀, Ω, hC₀, hΩ, hk⟩ := s.vecs.norm
  refine ⟨Ω, hΩ, fun x₀ => ?_⟩
  have hfin : cnt (ratH E n 0) Ω x₀ ≠ ⊤ := (cntBasic (ctx ratProper_holds s.D)).1 Ω hΩ x₀
  have hA : 0 ≤ C₀.toReal := ENNReal.toReal_nonneg
  have hc : 0 ≤ (cnt (ratH E n 0) Ω x₀).toReal := ENNReal.toReal_nonneg
  have hAe : ENNReal.ofReal C₀.toReal = C₀ := ENNReal.ofReal_toReal hC₀
  have hce : ENNReal.ofReal (cnt (ratH E n 0) Ω x₀).toReal = cnt (ratH E n 0) Ω x₀ :=
    ENNReal.ofReal_toReal hfin
  refine ⟨(Fintype.card ι : ℝ) * (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal),
    by positivity, fun m t y => ?_⟩
  have hU : ‖m.Uπ‖ ≤ ‖m.U‖ := norm_part_le _ m.U m.Uπ m.pp.1 m.pp.2
  have h1 : ∀ i, ‖s.k₁ (ac E n t * x₀) i‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal)) := fun i => by
    refine le_ofReal_sqrt (mul_nonneg hA hc) ?_
    rw [ENNReal.ofReal_mul hA, hAe, hce, ← cnt_central (ratH E n 0) Ω (ac E n t) x₀ (hcomm t)]
    exact (hk _ i).1
  have h2 : ∀ i, ‖s.k₂ y i‖ₑ ≤ ENNReal.ofReal (Real.sqrt C₀.toReal) * cnt (ratH E n 0) Ω y := fun i => by
    refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hA, hAe]
    exact (hk y i).2.trans (mul_le_mul_right (cnt_le_sq _ _ _) _)
  have h3 : ∀ i, ‖(inner ℂ (s.k₁ (ac E n t * x₀) i) (m.Uπ (s.k₂ y i)) : ℂ)‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal * ‖m.U‖) *
        cnt (ratH E n 0) Ω y := fun i =>
    enorm_inner_le _ _ _ _ hU _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) _ (h1 i) (h2 i)
  calc ‖m.G (ac E n t * x₀) y‖ₑ ≤ ∑ i, ‖(inner ℂ (s.k₁ (ac E n t * x₀) i) (m.Uπ (s.k₂ y i)) : ℂ)‖ₑ :=
        enorm_sum_le _ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal * ‖m.U‖) *
        cnt (ratH E n 0) Ω y := Finset.sum_le_sum fun i _ => h3 i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_assoc (Fintype.card ι : ℝ)]
end
end

