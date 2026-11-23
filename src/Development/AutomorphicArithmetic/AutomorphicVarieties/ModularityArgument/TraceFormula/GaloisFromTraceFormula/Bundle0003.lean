module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.Thin
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
public import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DeterminantOneCharacters.DeterminantOneConditionHolds
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.OneSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.CuspFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.PartNorm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem sum_inf_zero {a : ℕ} (ρ : CuspSub E a) (hn : GlobalTheory.DiscSpec.IsNormalised ρ) :
    ∑ τ : E →+* ℂ, ((CG.mk ρ).infChar τ).sum = 0 := by
  have := Submodule.nontrivial_iff_ne_bot.2 ρ.ne_bot
  obtain ⟨x, hx⟩ := exists_ne (0 : ρ.V)
  obtain ⟨g₀, hg₀⟩ : ∃ g, (x : Sm E a).1 g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (Subtype.ext (Subtype.ext (funext hcon)))
  have hlie : lie E a (oneL E a) (x : Sm E a) = (∑ τ : E →+* ℂ, ((CG.mk ρ).infChar τ).sum) • (x : Sm E a) := by
    rw [_root_.GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop E a, LinearMap.sum_apply,
      Finset.sum_congr rfl fun τ _ => _root_.GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq E a ρ τ _ (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) τ) x x.2,
      ← Finset.sum_smul]
  refine GlobalTheory.CompanionTheory.TotalTrace.eq_zero_of_exp_mul_eq_one fun t => ?_
  have h1 := GlobalTheory.T.central_eigen_exponential E a _ _ hlie t g₀
  rw [hn _ x.2 t g₀] at h1
  exact mul_right_cancel₀ hg₀ (by rw [one_mul]; exact h1.symm)

private theorem im_sum_of_const (m : Multiset ℂ) (c : ℝ) (h : ∀ x ∈ m, x.im = c) : m.sum.im = m.card * c := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    rw [Multiset.sum_cons, Complex.add_im, h x (Multiset.mem_cons_self x m),
      ih fun y hy => h y (Multiset.mem_cons_of_mem hy), Multiset.card_cons]
    push_cast
    ring

private theorem log_norm_prod (B : Multiset ℂˣ) :
    Real.log ‖((B.prod : ℂˣ) : ℂ)‖ = (B.map fun α : ℂˣ => Real.log ‖(α : ℂ)‖).sum := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons α B ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 α.ne_zero) (norm_ne_zero_iff.2 (Units.ne_zero _)), ih]

private theorem twist_zero (hA : AbsInf) {a n : ℕ} (ha : 1 ≤ a) (ρ : CuspSub E a) (hn : GlobalTheory.DiscSpec.IsNormalised ρ) (z : ℂ)
    (hR : ∀ τ, ∀ y ∈ ((CG.mk ρ).twist (Model.absC E z)).infChar τ, ∃ k : ℤ, y = (k : ℂ) + ((n : ℂ) - 1) / 2)
    (w : HeightOneSpectrum (𝓞 E)) (b : Multiset ℂˣ) (hb : ((CG.mk ρ).twist (Model.absC E z)).HasSat w b)
    (hbd : ∀ α ∈ b, (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖(α : ℂ)‖ ∧
      ‖(α : ℂ)‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ)) : z = 0 := by
  have hI : ∀ τ, ((CG.mk ρ).twist (Model.absC E z)).infChar τ = ((CG.mk ρ).infChar τ).map (· + z) :=
    fun τ => (hA E a (CG.mk ρ) z τ).1
  have hcard : ∀ τ, ((CG.mk ρ).infChar τ).card = a := fun τ =>
    (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) τ).1

  have him : ∀ τ, ∀ x ∈ (CG.mk ρ).infChar τ, (x + z).im = 0 := fun τ x hx => by
    obtain ⟨k, hk⟩ := hR τ (x + z) (by rw [hI]; exact Multiset.mem_map_of_mem _ hx)
    rw [hk]
    simp
  have hzim : z.im = 0 := by
    have h0 := congrArg Complex.im (sum_inf_zero ρ hn)
    rw [Complex.im_sum, Finset.sum_congr rfl fun τ _ => im_sum_of_const ((CG.mk ρ).infChar τ) (-z.im) fun x hx => by
      have := him τ x hx
      rw [Complex.add_im] at this
      linarith] at h0
    simp only [hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Complex.zero_im] at h0
    have hc : (Fintype.card (E →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have := (mul_eq_zero.1 h0).resolve_left hc
    have := (mul_eq_zero.1 this).resolve_left ha'
    linarith

  obtain ⟨M, hM⟩ : ∃ M : ℤ, 2 * z = (M : ℂ) := by
    obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hcard τ₀]; omega : 0 < ((CG.mk ρ).infChar τ₀).card)
    have hconj := PositivityTheory.Rg.BcB.F.Rig.B.infChar_conj ρ hn τ₀ _ _ (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) τ₀)
      (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) (ComplexEmbedding.conjugate τ₀))
    have hxim : x.im = 0 := by
      have := him τ₀ x hx
      rw [Complex.add_im, hzim] at this
      linarith
    have hxc : (starRingEnd ℂ) x = x := Complex.conj_eq_iff_im.2 hxim
    obtain ⟨k₁, hk₁⟩ := hR τ₀ (x + z) (by rw [hI]; exact Multiset.mem_map_of_mem _ hx)
    obtain ⟨k₂, hk₂⟩ := hR (ComplexEmbedding.conjugate τ₀) (-x + z) (by
      rw [hI, hconj, Multiset.map_map]
      refine Multiset.mem_map.2 ⟨x, hx, ?_⟩
      simp [hxc])
    refine ⟨k₁ + k₂ + n - 1, ?_⟩
    push_cast
    linear_combination hk₁ + hk₂

  have hq1 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast DiscreteGroups.T1.G.one_lt_absNorm w
  have hq0 : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by linarith
  have hlq : 0 < Real.log (Ideal.absNorm w.asIdeal : ℝ) := Real.log_pos hq1
  have hS := PositivityTheory.RgJS.satake_twist_holds E a _ (Model.absC E (-z)) w b (PositivityTheory.Rg.Rs.StrStepB.absC_unrAt (-z) w) hb
  rw [← CG.twist_mul, ← PositivityTheory.Rg.Rs.StrStepB.absC_add, add_neg_cancel, PositivityTheory.Rg.Rs.StrStepB.absC_zero, CG.twist_one] at hS
  have hu : (CG.mk ρ).IsUnitary := (CG.isUnitary_mk ρ).2 (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn)
  have hd := PositivityTheory.RgJS.determinant_one_condition_holds E a (CG.mk ρ) w _ hu hS
  have hbc : b.card = a := hb.card
  set q : ℝ := (Ideal.absNorm w.asIdeal : ℝ) with hq
  set r : ℝ := (M : ℝ) / 2 with hr
  have hzr : z = (r : ℂ) := by
    rw [hr]
    push_cast
    linear_combination hM / 2
  have hprod : (((b.map (· * (Model.absC E (-z)).val w)).prod : ℂˣ) : ℂ) =
      ((b.prod : ℂˣ) : ℂ) * (((Model.absC E (-z)).val w : ℂˣ) : ℂ) ^ a := by
    rw [Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const', Multiset.prod_replicate, hbc]
    simp
  have hv : ‖(((Model.absC E (-z)).val w : ℂˣ) : ℂ)‖ = q ^ r := by
    have := DiscreteGroups.T1.G.norm_absC_val (E := E) (-r) w
    rw [neg_neg] at this
    rw [hzr, ← Complex.ofReal_neg]
    exact this
  rw [hprod, norm_mul, norm_pow, hv] at hd
  have hpos : q ^ r ≠ 0 := (Real.rpow_pos_of_pos hq0 r).ne'
  have hl := congrArg Real.log hd
  rw [Real.log_mul (norm_ne_zero_iff.2 (Units.ne_zero _)) (pow_ne_zero _ hpos), Real.log_pow, Real.log_rpow hq0,
    Real.log_one, log_norm_prod] at hl
  have hb0 : b ≠ 0 := fun h => by
    rw [h, Multiset.card_zero] at hbc
    omega
  have hlo : (b.map fun _ : ℂˣ => -(Real.log q / 2)).sum < (b.map fun α : ℂˣ => Real.log ‖(α : ℂ)‖).sum := by
    refine Multiset.sum_lt_sum_of_nonempty hb0 fun α hα => ?_
    have h1 := Real.log_lt_log (Real.rpow_pos_of_pos hq0 _) (hbd α hα).1
    rw [Real.log_rpow hq0] at h1
    linarith
  have hhi : (b.map fun α : ℂˣ => Real.log ‖(α : ℂ)‖).sum < (b.map fun _ : ℂˣ => Real.log q / 2).sum := by
    refine Multiset.sum_lt_sum_of_nonempty hb0 fun α hα => ?_
    have h1 := Real.log_lt_log (norm_pos_iff.2 α.ne_zero) (hbd α hα).2
    rw [Real.log_rpow hq0] at h1
    linarith
  rw [Multiset.map_const', Multiset.sum_replicate, hbc, nsmul_eq_mul] at hlo hhi
  have hP : 0 < (a : ℝ) * Real.log q := mul_pos (by exact_mod_cast ha) hlq
  have h1 : r < 1 / 2 := by
    refine lt_of_mul_lt_mul_left ?_ hP.le
    nlinarith
  have h2 : -(1 / 2) < r := by
    refine lt_of_mul_lt_mul_left ?_ hP.le
    nlinarith
  have hM0 : M = 0 := by
    have h3 : (M : ℝ) < 1 := by rw [hr] at h1; linarith
    have h4 : (-1 : ℝ) < M := by rw [hr] at h2; linarith
    have h5 : M < 1 := by exact_mod_cast h3
    have h6 : -1 < M := by exact_mod_cast h4
    omega
  rw [hM0] at hM
  simpa using hM

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.partNorm :
    AbsInf → PartNorm := by
  intro hA E _ _ _ n hn π hd D hR hs i
  obtain ⟨w, hsp, B, ⟨b, hb, rfl⟩, hB⟩ : ∃ w : UpperTheory.V.Cj.S.Pl E, IsSplitAt w ∧ ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B := by
    have hinf := (UpperTheory.V.Z.Tf.GOne.thin E).2
    have hfin := Filter.eventually_cofinite.1 hs
    obtain ⟨w, hw, hw'⟩ := (hinf.diff hfin).nonempty
    have h : ¬ ¬ (IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B) := hw'
    exact ⟨w, hw, (not_not.1 h) hw⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CuspSub E (D.N i), CG.mk ρ = D.P i := Quotient.exists_rep (D.P i)
  obtain ⟨s, hs'⟩ := GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised E (D.N i) (D.pos i) ρ fun τ =>
    ⟨_, GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) τ⟩
  have hP : D.P i = (CG.mk (ρ.twist (Model.absC E s))).twist (Model.absC E (-s)) := by
    rw [← hρ, ← CG.twist_mk, ← CG.twist_mul, ← PositivityTheory.Rg.Rs.StrStepB.absC_add, add_neg_cancel,
      PositivityTheory.Rg.Rs.StrStepB.absC_zero, CG.twist_one]
  have hu := UpperTheory.V.Z.Tf.GOne.unitOf E n hn π hd
  have hz : -s = 0 := by
    refine twist_zero (n := n) hA (D.pos i) (ρ.twist (Model.absC E s)) hs' (-s) (fun τ y hy => ?_) w (b i) (hP ▸ hb i)
      fun α hα => PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound E n (CG.mk π) hu w _ hB α
        (Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hα⟩)
    rw [← hP] at hy
    obtain ⟨lam, hlam⟩ := hR τ
    have hy' : y ∈ infOfWeight lam := by
      rw [← hlam]
      exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hy⟩
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hy'
    refine ⟨lam.w k - (k : ℕ), ?_⟩
    push_cast
    ring
  have hs0 : s = 0 := neg_eq_zero.1 hz
  refine ⟨ρ.twist (Model.absC E s), ?_, hs', GlobalTheory.SpehPair.isUnitary_of_isNormalised hs'⟩
  rw [← hρ, hs0, PositivityTheory.Rg.Rs.StrStepB.absC_zero, CuspSub.twist_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.SigmaEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem sigma_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {a n : ℕ} (e : a = n) (Q : CuspSub E a)
    (π : CuspSub E n) (h : e ▸ Q.V = π.V) : (⟨a, CG.mk Q⟩ : Σ k, CG E k) = ⟨n, CG.mk π⟩ := by
  subst e
  have : Q = π := CuspSub.ext h
  rw [this]

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.preOf :
    PartNorm → GOne.CsdSat → Places → PreOf := by
  intro hN hC hPl E _ _ _ n hn π hd D hHas hReg hIn hSp
  have hcc := fun w : Pl E => ((hPl E).2.1 w).1
  have hsp := fun w : Pl E => ((hPl E).2.1 w).2
  choose P hP hnorm hunit using hN E n hn π hd D hReg hSp
  have hl : ∀ i w, ∃ σ, IsLocCompGL (P i).V w σ := fun i w =>
    (GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL E (D.N i) (P i) w).imp fun σ h =>
      ((cuspSub_iff (P i)).2.1 w σ).2 h.1
  choose σ hσ using hl
  have hdisc (i : Fin D.c) : IsDiscrete (P i).V :=
    isDiscrete_of_cuspSub (P i) fun φ hφ => by
      obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_invariant
        ((P i).cusp φ hφ) (hnorm i φ hφ)
      exact GlobalTheory.DiscChar.isSqInt_of_bounded (hnorm i φ hφ) (C := C) fun g => by
        simpa using hC g
  have hinf (i : Fin D.c) (τ : E →+* ℂ) :
      HasInfCharGL (P i).V τ ((CG.mk (P i)).infChar τ) :=
    ((cuspSub_iff (P i)).2.2 τ _).2 (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk (P i)) τ)
  let D' : PositivityTheory.Rg.BcB.F.Pre E n := ⟨D.c, D.N, D.sum, fun i => (P i).V, σ, fun i τ => (CG.mk (P i)).infChar τ,
    D.pos, hdisc, hσ, hinf⟩
  have hsat : ∀ w B, D.Sat w B → D'.Sat w B := by
    rintro w B ⟨b, hb, rfl⟩
    refine ⟨b, fun i => ?_, rfl⟩
    let part : PositivityTheory.Rg.BcB.F.Pre E (D.N i) :=
      ⟨1, fun _ => D.N i, by simp, fun _ => (P i).V, fun _ => σ i,
        fun _ => (CG.mk (P i)).infChar, fun _ => D.pos i, fun _ => hdisc i,
        fun _ => hσ i, fun _ => hinf i⟩
    have hone : GOne.One part (P i) := ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
    have hpart := (GOne.oneSat E (D.N i) (D.pos i) (P i) part hone w (b i)).1
      (by rw [hP i]; exact hb i)
    obtain ⟨b', hb', hsum⟩ := hpart
    have heq : b' 0 = b i := by simpa using hsum
    exact heq ▸ hb' 0
  have hconj {w u : Pl E} (h : PositivityTheory.Rg.BcB.F.ConjPl w u) : cPl u = w := by
    obtain ⟨hunder, hsplit⟩ := h
    by_cases e : u = w
    · subst e
      exact (GlobalTheory.ConjAtPlace.conjSrc_eq_iff u).2 (hsplit.resolve_left fun h => h rfl)
    · rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
        (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u w).1 hunder.symm with h | h
      · exact absurd h.symm e
      · refine (eq_conjSrc ?_).symm
        rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at h ⊢
        intro x y hxy
        refine (h y x ?_).symm
        rw [hxy]
        exact (IsCMField.complexConj_apply_apply E _).symm
  have hcof : Tendsto (cPl : Pl E → Pl E) cofinite cofinite :=
    Function.Injective.tendsto_cofinite fun x y e => by rw [← hcc x, ← hcc y, e]
  refine ⟨D', fun τ => ?_, ?_, hSp.mono fun w hw hs => (hw hs).imp fun B hB => ⟨hsat w B hB.1, hB.2⟩, ?_⟩
  · obtain ⟨lam, hlam⟩ := hReg τ
    refine ⟨lam, ?_⟩
    rw [← hlam]
    exact Finset.sum_congr rfl fun i _ => by simp only [D', hP i]
  · filter_upwards [hIn, hSp, hcof.eventually hSp, hC E n hn π hd] with w h1 h2 h3 h4
    by_cases hw : IsSplitAt w
    · obtain ⟨B, hB, hπ⟩ := h2 hw
      obtain ⟨B', hπ', hu⟩ := h4
      obtain rfl := CG.HasSat.unique hπ hπ'
      refine ⟨B, hsat w B hB, fun u hu' => ?_⟩
      have e : u = cPl w := by rw [← hconj hu', hcc]
      have hs : IsSplitAt u := by
        rw [e]
        refine (hsp _).2 ?_
        rw [hcc]
        exact ((hsp w).1 hw).symm
      obtain ⟨B₂, hB₂, hπ₂⟩ := e ▸ h3 (e ▸ hs)
      obtain rfl := CG.HasSat.unique hπ₂ (hu u hu')
      exact hsat _ _ hB₂
    · obtain ⟨B, hB, hinv⟩ := h1 hw
      refine ⟨B, hsat w B hB, fun u hu' => ?_⟩
      have e : u = w := by
        rw [← hcc u, hconj hu']
        by_contra h
        exact hw ((hsp w).2 h)
      subst e
      have : B.map (·⁻¹) = B := hinv
      rw [this]
      exact hsat _ _ hB
  · rintro ⟨hc, h⟩
    have i : Fin D.c := ⟨0, by have : D.c = 1 := hc; omega⟩
    obtain ⟨e, he⟩ := h i
    refine hHas ⟨i, ?_⟩
    rw [← hP i]
    exact sigma_eq e (P i) π he
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.StableS
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.stableS :
    Enlarge → Places → StableBlockG → StableBlockS := by
  classical
  intro hEn hP hG E _ _ _ hunr n hn π hreg hd
  obtain ⟨l₁, hl⟩ := hG E hunr n hn π hreg hd
  refine ⟨l₁, fun l₂ S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨c, hc, hst⟩ := hl l₂ S hS Z hZ B τ hB hτ
  refine ⟨c, hc, fun φ hφ hr => ?_⟩
  obtain ⟨J, _, D, B₁, hD, hInf, hbd⟩ := hst φ hφ hr

  have hoff : ∀ w : Pl E, ¬ IsSplitAt w → Off Z w := by
    intro w hw
    have hcw : cPl w = w := by
      by_contra h
      exact hw (((hP E).2.1 w).2.2 h)
    have hwZ : w ∉ Z := fun h => hw (hZ w h).2
    exact ⟨hwZ, by rwa [hcw]⟩

  let good : J → Prop := fun j => ∀ w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w
  refine ⟨{j // good j}, inferInstance, fun j => D j.1, fun j => B₁ j.1, fun j => hD j.1, fun j => hInf j.1,
    fun j => j.2, ?_⟩
  intro T hT hTZ e₁ e₂ ρ hρ hlt
  have hbad : ∀ i : {j // ¬ good j}, ∃ w, ¬ IsSplitAt w ∧ inv (B w) = B w ∧ inv (B₁ i.1 w) ≠ B₁ i.1 w := by
    intro i
    have h := i.2
    simp only [good, not_forall] at h
    obtain ⟨w, h1, h2, h3⟩ := h
    exact ⟨w, h1, h2, h3⟩
  choose u hu1 hu2 hu3 using hbad
  have hcard : ∀ j w, ¬ IsSplitAt w → (B₁ j w).card = n := fun j w hw => sat_card ((hD j).2 w (hoff w hw))
  have hBcard : ∀ w, ¬ IsSplitAt w → (B w).card = n := fun w hw => (hB w (hoff w hw)).card
  obtain ⟨T', e₁', e₂', hT'S, hT'Z, hT'e, hzero, hval, hgeom⟩ :=
    hEn E hunr n 0 S hS Z T hZ hT hTZ e₁ e₂ {j // ¬ good j} u (fun i => B₁ i.1) (fun _ => 0)
      (fun i => ⟨hu1 i, hcard _ _ (hu1 i), Multiset.card_zero, fun h => hu3 i h.1⟩)
  have hvj : ∀ j, good j → val T' e₁' e₂' (B₁ j) 0 = val T e₁ e₂ (B₁ j) 0 := fun j hj =>
    hval (B₁ j) 0 fun i => ⟨hcard _ _ (hu1 i), Multiset.card_zero, hj _ (hu1 i) (hu2 i), Multiset.map_zero _⟩
  have hvB : val T' e₁' e₂' B 0 = val T e₁ e₂ B 0 :=
    hval B 0 fun i => ⟨hBcard _ (hu1 i), Multiset.card_zero, hu2 i, Multiset.map_zero _⟩
  have hsm := hbd T' hT'S hT'Z e₁' e₂' ρ hT'e hρ fun j => by
    by_cases hj : good j
    · rw [hvj j hj]
      exact hlt ⟨j, hj⟩
    · have h0 : val T' e₁' e₂' (B₁ j) 0 = 0 := hzero ⟨j, hj⟩
      rw [h0, norm_zero]
      exact hρ
  simpa only [hgeom, hvB] using hsm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.TwDataT
section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem sum_map_eq {ι : Type} [Fintype ι] (f : ι → Multiset ℂ) (g : ℂ → ℂ) :
    ∑ i, (f i).map g = (∑ i, f i).map g :=
  (map_sum (Multiset.mapAddMonoidHom g) f Finset.univ).symm

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.twDataT :
    CDAddG → MuInf → MWAt → DualWt → TwDataT := by
  intro hAdd hMu hMW hDW E _ _ _ n a b hab ha hb μ e hμ l₁ l₂ lam hlam D₁ D₂ h₁ h₂
  subst hab
  obtain ⟨D, hnot, hsat, hinf⟩ := hAdd E a b D₁ D₂ (μ ^ b) (μ ^ a) ha hb
  have hval : ∀ (w : Pl E) (k : ℕ), (μ ^ k).val w = μ.val w ^ k :=
    fun w k => MonoidHom.pow_apply μ.1 k _
  have hunr : ∀ {w : Pl E} (k : ℕ), μ.UnrAt w → (μ ^ k).UnrAt w := by
    intro w k h x hx
    have e1 : (μ ^ k).loc w x = μ.loc w x ^ k := MonoidHom.pow_apply μ.1 k _
    rw [e1, h x hx, one_pow]
  have hT := (hMu E μ e hμ).2
  have hemb : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        (infOfWeight (l v)).map (· + (k : ℂ) * (e v : ℂ) / 2) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        ((C.P i).infChar v.embedding).map (· + (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).1
    simp only [h1]
    rw [sum_map_eq, hC v.embedding, (hMW E m l v).1]
  have hcon : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        (infOfWeight (l v)).map (fun t => -(t + (k : ℂ) * (e v : ℂ) / 2)) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        ((C.P i).infChar (ComplexEmbedding.conjugate v.embedding)).map (· - (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).2
    simp only [h1]
    rw [sum_map_eq, hC (ComplexEmbedding.conjugate v.embedding), (hMW E m l v).2, Multiset.map_map]
    refine Multiset.map_congr rfl fun t _ => ?_
    simp only [Function.comp_apply]
    ring
  refine ⟨D, hnot, ?_, ?_⟩
  · intro τ
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · refine ⟨lam (InfinitePlace.mk τ), ?_⟩
      rw [hinf τ, ← hlam (InfinitePlace.mk τ), ← hemb D₁ l₁ b h₁, ← hemb D₂ l₂ a h₂, h]
    · obtain ⟨lam', hl⟩ := hDW (a + b) (lam (InfinitePlace.mk τ))
      have hτ : τ = ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding := by
        rw [h]
        exact (star_star τ).symm
      refine ⟨lam', ?_⟩
      rw [hinf τ, hl, ← hlam (InfinitePlace.mk τ), Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map]
      have e1 := hcon D₁ l₁ b h₁ (InfinitePlace.mk τ)
      have e2 := hcon D₂ l₂ a h₂ (InfinitePlace.mk τ)
      rw [← hτ] at e1 e2
      rw [e1, e2]
      rfl
  · intro w B₁ B₂ hu s₁ s₂
    have h := hsat w B₁ B₂ (hunr b hu) (hunr a hu) s₁ s₂
    rw [hval, hval] at h
    exact h
end

