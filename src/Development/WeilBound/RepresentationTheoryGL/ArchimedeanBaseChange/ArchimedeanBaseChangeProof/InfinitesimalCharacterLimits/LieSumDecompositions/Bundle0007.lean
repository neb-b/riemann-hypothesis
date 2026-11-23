module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogLie
section
noncomputable section

open NumberField Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def Zr (N r : ℕ) : Lie E N := fun i j => if i = j ∧ (i : ℕ) < r then 1 else 0

def Tr1 (r s : ℕ) (τ : E →+* ℂ) : Module.End ℂ (Sm E (r + s)) :=
  ∑ i : Fin r, Eop τ (Fin.castAdd s i) (Fin.castAdd s i)

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem aInf_add' (N r : ℕ) (s t : ℝ) : aInf E N r (s + t) = aInf E N r s * aInf E N r t := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i w
  simp only [Pi.mul_apply]
  split_ifs <;> simp [← Complex.exp_add]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem aInf_zero' (N r : ℕ) : aInf E N r 0 = 1 :=
  Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)

theorem aT_add' (N r : ℕ) (s t : ℝ) : aT E N r (s + t) = aT E N r s * aT E N r t := by
  rw [aT, aT, aT, aInf_add', map_mul]

theorem lieS_diag_comm {N : ℕ} (i j : Fin N) (x y : Cinf E) : Commute (lieS E N i i x) (lieS E N j j y) := by
  classical
  rw [lieS_apply, lieS_apply]
  have h := lie_comm (E := E) (toL (Matrix.single i i x)) (toL (Matrix.single j j y))
  have e : Matrix.of (toL (Matrix.single i i x)) * Matrix.of (toL (Matrix.single j j y)) =
      Matrix.of (toL (Matrix.single j j y)) * Matrix.of (toL (Matrix.single i i x)) := by
    simp only [toL, Equiv.apply_symm_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_comm]
    · have z : ∀ (p q : Fin N) (u v : Cinf E), p ≠ q → Matrix.single p p u * Matrix.single q q v = 0 := by
        intro p q u v hpq
        refine Matrix.ext fun a b => ?_
        rw [Matrix.mul_apply, Matrix.zero_apply]
        refine Finset.sum_eq_zero fun c _ => ?_
        simp only [Matrix.single_apply]
        by_cases h1 : p = a ∧ p = c
        · rw [if_pos h1, if_neg (fun h2 => hpq (h1.2.trans h2.1.symm)), mul_zero]
        · rw [if_neg h1, zero_mul]
      rw [z i j x y hij, z j i y x (Ne.symm hij)]
  rw [e, sub_self] at h
  exact sub_eq_zero.1 h

theorem Eop_diag_comm {N : ℕ} (τ τ' : E →+* ℂ) (i j : Fin N) : Commute (Eop τ i i) (Eop τ' j j) := by
  have hc := fun x y => lieS_diag_comm (E := E) i j x y
  simp only [Eop]
  refine Commute.smul_right (Commute.smul_left ?_ _) _
  exact Commute.sub_left (Commute.sub_right (hc _ _) ((hc _ _).smul_right _))
    ((Commute.sub_right (hc _ _) ((hc _ _).smul_right _)).smul_left _)

theorem lie_Zr (r s : ℕ) : lie E (r + s) (Zr (r + s) r) =
    ∑ w : InfinitePlace E, (Tr1 r s w.embedding + Tr1 r s (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  simp only [Tr1, ← Finset.sum_add_distrib, Eop_add_Eop_conj]
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_sum]
  have h1 : ∑ w : InfinitePlace E, atEmb w.embedding (1 : ℂ) = (1 : Cinf E) := by
    have e : ∀ w : InfinitePlace E, atEmb w.embedding (1 : ℂ) = Pi.single w ((fun _ => (1 : ℂ)) w) := by
      intro w; simp [atEmb, InfinitePlace.mk_embedding]
    simp only [e]
    exact Finset.univ_sum_single _
  rw [h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lieS_apply, ← map_sum]
  congr 1
  funext a b
  simp only [Zr, toL, Finset.sum_apply, Matrix.of_symm_apply, Matrix.single_apply]
  by_cases hab : a = b ∧ (a : ℕ) < r
  · rw [if_pos hab]
    obtain ⟨rfl, ha⟩ := hab
    rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin r)]
    · rw [if_pos]
      exact ⟨Fin.ext rfl, Fin.ext rfl⟩
    · intro c _ hc
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hc (Fin.ext (by have := congrArg Fin.val h1; simpa using this))
    · simp
  · rw [if_neg hab]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hab ⟨h1.symm.trans h2, by rw [← h1]; simp⟩

theorem Tr1_comm (r s : ℕ) (τ τ' : E →+* ℂ) : Commute (Tr1 (E := E) r s τ) (Tr1 r s τ') := by
  unfold Tr1
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact Eop_diag_comm _ _ _ _

omit [_root_.NumberField.IsTotallyComplex E] in
theorem hasDerivAt_aInf (N r : ℕ) : HasDerivAt (fun t : ℝ => toL (aInf E N r t).val) (Zr N r) 0 := by
  rw [hasDerivAt_pi]; intro i
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro w
  simp only [aInf, toL, Zr, Matrix.of_symm_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : (i : ℕ) < r
    · simp only [if_true, hi, and_self, Pi.one_apply]
      have := (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
      simpa using this
    · simp only [if_true, hi, and_false, if_false, Pi.zero_apply]
      exact hasDerivAt_const _ _
  · simp only [hij, if_false, false_and, Pi.zero_apply]
    exact hasDerivAt_const _ _

theorem hasDerivAt_aT (r s : ℕ) (Φ : Sm E (r + s)) (h : GA E (r + s)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Φ.1 (h * aT E (r + s) r t))
      ((lie E (r + s) (Zr (r + s) r) Φ).1 (h * aT E (r + s) r t)) t := by
  have key := hasDerivAt_curve Φ (h * aT E (r + s) r t) (aInf E (r + s) r) (Zr (r + s) r) (aInf_zero' _ _)
    (hasDerivAt_aInf _ _)
  have e : (fun u => Φ.1 (h * aT E (r + s) r t * infGL E (r + s) (aInf E (r + s) r u))) =
      fun u => Φ.1 (h * aT E (r + s) r (t + u)) := by
    funext u
    rw [aT_add', ← mul_assoc]
    rfl
  rw [e] at key
  have h2 := HasDerivAt.comp_sub_const (f := fun u => Φ.1 (h * aT E (r + s) r (t + u))) t t (by simpa using key)
  simpa [lie_apply] using h2

theorem lev_aT (r s : ℕ) (t : ℝ) : lev (Ad E) r s (aT E r r t, 1) = aT E (r + s) r t := by
  have val_emb₂ {T : Type} [CommRing T] (g : GL (Fin r) T × GL (Fin s) T) :
      (GlobalTheory.SmGL.emb₂ T (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) g : Matrix (Fin (r+s)) (Fin (r+s)) T) =
        Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    obtain ⟨u, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨v, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases u with u | u <;> rcases v with v | v
    all_goals simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb,
      GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two, Matrix.blockDiagonal'_apply_eq,
      Matrix.blockDiagonal'_apply_ne]
  apply Units.ext
  rw [lev, val_emb₂, JFinTr.aT_val, JFinTr.aT_val]
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, Matrix.diagonal_apply]
  have e1 : (fun _ : InfinitePlace E => (1 : ℂ)) = (1 : Cinf E) := rfl
  simp only [Matrix.one_apply, e1, sub_add_cancel]

theorem lev_mul_aT (r s : ℕ) (m : GA E r × GA E s) (t : ℝ) :
    ∃ m', lev (Ad E) r s m * aT E (r + s) r t = lev (Ad E) r s m' := by
  refine ⟨(m.1 * aT E r r t, m.2), ?_⟩
  rw [← lev_aT r s t, ← map_mul]
  congr 1
  ext <;> simp

theorem aT_mul_decomp (r s : ℕ) (F : GA E (r + s) → ℂ) (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F (unip x * g) = F g)
    (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (y : GA E (r + s)) (t : ℝ) :
    F (aT E (r + s) r t * (unip x * lev (Ad E) r s m * y)) = F (lev (Ad E) r s m * aT E (r + s) r t * y) := by
  obtain ⟨x', hx'⟩ := JFinTr.diag_mul_unip (aT E (r + s) r t) _ _ (JFinTr.aT_val (r + s) r t)
    (JFinTr.aT_inv_val (r + s) r t) x
  have e : aT E (r + s) r t * (unip x * lev (Ad E) r s m * y) = unip x' * (aT E (r + s) r t * lev (Ad E) r s m * y) := by
    rw [← mul_assoc, ← mul_assoc, hx']
    simp only [mul_assoc]
  rw [e, hF, JFinTr.aT_comm_lev]

theorem iwasawa2 (r s : ℕ) (g : GA E (r + s)) : ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s)
    (k : Kinf E (r + s)) (g' : GL (Fin (r + s)) (Af E)),
    g = unip x * lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g') := by
  let n : Fin 2 → ℕ := ![r, s]
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  obtain ⟨v, hv, m, k, g', e⟩ := GlobalTheory.SpehInfChar.exists_iwasawa E n h g
  obtain ⟨xv, rfl⟩ := CapFactor.exists_unip_of_mem n h hv
  refine ⟨xv, (m 0, m 1), k, g', ?_⟩
  have hx : lev (Ad E) r s (m 0, m 1) = GlobalTheory.SmGL.leviEmb (Ad E) (GlobalTheory.SmGL.stdBlocks n h) m :=
    (CapFactor.lev_eq_leviEmb (R := Ad E) n h (m 0, m 1)).trans (by rw [PositivityTheory.Rg.Rs.PInfInd2A.levPair_eta])
  rw [hx]
  exact e

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.ReLtRho
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs
open scoped Pointwise ENNReal

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

namespace Grow

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem leftInv {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g) :
    ∀ γ ∈ latticeGL E N, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E N) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E N ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact hφ.left γ) (Subgroup.zpowers_le.2 (hcen 1))
  exact this

theorem exists_kill {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    {r : ℕ} (hr0 : 0 < r) (hrN : r < N) :
    ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧ ∀ z, p.IsRoot z → ∃ c ∈ Exp r φ.1, z = Complex.exp c := by
  obtain ⟨hA, hS, _, hCT⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  have hct := (hCT φ hφ r hr0 hrN).1
  have hfin := finTr_holds E N φ hφ r hr0 hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => by
    rw [hA, hA, hA]; exact JSqIntGlue.aR_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp hnice.cont r ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [hA] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    exact ⟨c, ⟨_, hct, F, hF, hF0, hFe⟩, rfl⟩

theorem bnd_of' {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ An.Kill r φ.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp (κ r)) : An.Bnd φ.1 κ := by
  obtain ⟨_, hS, _, _⟩ := dict_holds E N
  have hcen' : ∀ (t : ℝ) g, φ.1 (An.tor E (fun _ => t) * g) = φ.1 g := fun t g => by
    rw [← hS]; exact hcen t g
  have hnice := niceAut_holds E N φ hφ hcen'
  obtain ⟨M, hM⟩ := initBnd_holds E N φ hφ hcen'
  exact GlobalTheory.CompanionTheory.AnBoot.bootGlue diffstep_holds (ctstepglue_holds GlobalTheory.CompanionTheory.LinRec.recBound) E N φ.1 M κ hnice hM hκ

theorem bnd_of {φ : Sm E N} (hφ : IsAutForm φ) (hcen : ∀ (t : ℝ) g, φ.1 (splitCentre E N t * g) = φ.1 g)
    (κ : ℕ → ℝ) (hκ : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re < κ r) : An.Bnd φ.1 κ := by
  refine bnd_of' hφ hcen κ fun r hr0 hrN => ?_
  obtain ⟨p, hp, hk, hroots⟩ := exists_kill hφ hcen hr0 hrN
  refine ⟨p, hp, hk, fun z hz => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hroots z hz
  rw [Complex.norm_exp]
  exact Real.exp_lt_exp.2 (hκ r hr0 hrN c hc)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_le_rho {r : ℕ} {c : ℂ} (h : pE E N r c ≤ 0) : c.re ≤ An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_le_iff₀ hd).1 h2
  unfold An.rho
  calc c.re ≤ (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem re_lt_rho {r : ℕ} {c : ℂ} (h : pE E N r c < 0) : c.re < An.rho E N r := by
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  unfold pE at h
  have h2 : c.re / (Module.finrank ℚ E : ℝ) < (r : ℝ) * ((N : ℝ) - r) / 2 := by linarith
  have h3 := (div_lt_iff₀ hd).1 h2
  unfold An.rho
  calc c.re < (r : ℝ) * ((N : ℝ) - r) / 2 * (Module.finrank ℚ E : ℝ) := h3
    _ = _ := by ring

end Grow

open Grow in
theorem growPHolds : GrowPHolds := by
  intro E _ _ _ N χ hχ hcen hnp
  refine ⟨ContAut.continuous_of_isOpen_stab E N χ hχ.level, leftInv hχ hcen, fun ε hε => ?_⟩
  exact bnd_of hχ hcen _ fun r hr0 hrN c hc => by
    have := re_le_rho (hnp r hr0 hrN c hc)
    linarith

open Grow in
theorem growQHolds : GrowQHolds := by
  intro E _ _ _ N u hu hsq
  have hcen := hsq.1
  have hk : ∀ r, ∃ κ : ℝ, 0 < r → r < N → κ < An.rho E N r ∧ ∃ p : ℂ[X], p.Monic ∧ An.Kill r u.1 p ∧
      ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ := by
    intro r
    by_cases hr : 0 < r ∧ r < N
    swap
    · exact ⟨0, fun h1 h2 => (hr ⟨h1, h2⟩).elim⟩
    obtain ⟨hr0, hrN⟩ := hr
    obtain ⟨p, hp, hpk, hroots⟩ := exists_kill hu hcen hr0 hrN
    have hroot' : ∀ z ∈ p.roots.toFinset, ‖z‖ < Real.exp (An.rho E N r) := by
      intro z hz
      rw [Multiset.mem_toFinset, mem_roots hp.ne_zero] at hz
      obtain ⟨c, hc, rfl⟩ := hroots z hz
      rw [Complex.norm_exp]
      exact Real.exp_lt_exp.2 (re_lt_rho (expNeg_holds E N u hu hsq r hr0 hrN c hc))
    obtain ⟨κ, hκ, hκz⟩ := JSqIntGlue.exists_lt_of_finset _ _ hroot'
    refine ⟨κ, fun _ _ => ⟨hκ, p, hp, hpk, fun z hz => hκz z ?_⟩⟩
    rw [Multiset.mem_toFinset, mem_roots hp.ne_zero]
    exact hz
  choose κ hκ using hk
  exact ⟨ContAut.continuous_of_isOpen_stab E N u hu.level, leftInv hu hcen, κ, fun r h1 h2 => (hκ r h1 h2).1,
    bnd_of' hu hcen κ fun r h1 h2 => (hκ r h1 h2).2⟩

theorem intBnd : IntBnd := by
  intro E _ _ _ N H hc h0 hl m hm hB
  obtain ⟨_, hS, hL, _⟩ := dict_holds E N
  set φ : GA E N → ℂ := fun g => ((Real.sqrt (H g) : ℝ) : ℂ) with hφ
  have hφc : Continuous φ := Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hc)
  have hφB : An.Bnd φ (fun r => m r / 2) := by
    intro ω hω hωB t₀ Q hQ
    obtain ⟨C, hC⟩ := hB ω hω hωB t₀ Q hQ
    refine ⟨Real.sqrt (max C 0), fun b hb x hx q hq => ?_⟩
    have h1 := hC b hb x hx q hq
    rw [Complex.norm_real, Real.norm_of_nonneg (h0 _)] at h1
    set S := ∑ r ∈ Finset.range N, m r * An.sr x r with hSdef
    have e2 : ∑ r ∈ Finset.range N, m r / 2 * An.sr x r = S / 2 := by
      rw [hSdef, Finset.sum_div]
      exact Finset.sum_congr rfl fun r _ => by ring
    have e : Real.exp (∑ r ∈ Finset.range N, m r / 2 * An.sr x r) = Real.sqrt (Real.exp S) := by
      rw [e2]
      conv_rhs => rw [show S = S / 2 + S / 2 by ring]
      rw [Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
    have h2 : H (b * An.tor E x * q) ≤ max C 0 * Real.exp S :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    calc ‖φ (b * An.tor E x * q)‖ = Real.sqrt (H (b * An.tor E x * q)) := by
          rw [hφ, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (max C 0 * Real.exp S) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (max C 0) * Real.sqrt (Real.exp S) := Real.sqrt_mul (le_max_right _ _) _
      _ = _ := by rw [e]
  have hκ : ∀ r, 0 < r → r < N → m r / 2 < An.rho E N r := fun r h1 h2 => by
    have := hm r h1 h2
    linarith
  have hslab := GlobalTheory.CompanionTheory.SlabGlue.slabGlue boxvol_holds E N Measure.haar φ (fun r => m r / 2) hφc hφB hκ
  have hfd := isFundamentalDomain_stdDom (latticeGL E N) (Measure.haar : Measure (GA E N))
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := GroundTheory.Automorphic.Reduction.exists_siegelSet (K := E) N
  have : MeasurableConstSMul (latticeGL E N) (GA E N) := ⟨fun γ => measurable_const_mul (γ : GA E N)⟩
  have : SMulInvariantMeasure (latticeGL E N) (GA E N) (Measure.haar : Measure (GA E N)) :=
    ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hle := JSqIntGlue.setLIntegral_le_of_cover hfd (S := An.slab ω (max 0 (-Real.log t)))
    (fun g => by
      obtain ⟨γ, hγ, h⟩ := JSqIntGlue.exists_mem_slab hS hL ht hsieg g
      exact ⟨⟨γ, hγ⟩, h⟩) (fun g => ENNReal.ofReal (H g)) (fun γ g => by
      show ENNReal.ofReal (H (γ.1 * g)) = ENNReal.ofReal (H g)
      rw [hl γ.1 γ.2 g])
  have e : ∀ g, ‖φ g‖ₑ ^ 2 = ENNReal.ofReal (H g) := fun g => by
    show ‖((Real.sqrt (H g) : ℝ) : ℂ)‖ₑ ^ 2 = _
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (h0 g)]
  simp only [e] at hslab
  exact hle.trans_lt (hslab ω hω hωB _)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end

