module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevel
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LevGeo

theorem gam_keeps_L' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (A : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hA : A ≠ 0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ X.L', v = a • u}) :
    ∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L' := by
  have hinv : A⁻¹ * A = 1 := inv_mul_cancel₀ hA
  have hA1 : ∀ b ∈ A⁻¹, ∀ x ∈ X.Λ, b • x ∈ X.L' := by
    intro b hb x hx
    rw [hΛ] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hx
      have hm : b * a ∈ A⁻¹ * A := FractionalIdeal.mul_mem_mul hb ha
      rw [hinv, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨z, hz⟩ := hm
      rw [smul_smul, ← hz, algebraMap_smul]
      exact X.L'.smul_mem z hu
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact X.L'.smul_mem c hx
  intro γ hγ v hv
  have key : ∀ y ∈ ((A⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
      (A : Submodule (𝓞 E) E), (γ : Matrix (Fin r) (Fin r) E).mulVec (y • v) ∈ X.L' := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun b hb a ha => ?_) (fun y1 y2 h1 h2 => ?_)
    · have hav : a • v ∈ X.Λ := by
        rw [hΛ]; exact Submodule.subset_span ⟨a, ha, v, hv, rfl⟩
      have h1 := ((X.Γ_stab γ hγ).2 (a • v)).1 hav
      rw [mul_smul, Matrix.mulVec_smul]
      exact hA1 b hb _ h1
    · rw [add_smul, Matrix.mulVec_add]; exact add_mem h1 h2
  have h1 : (1 : E) ∈ ((A⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
      (A : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.coe_mul, hinv]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have := key 1 h1
  rwa [one_smul] at this

theorem level_mul_two_div (m n d : ℝ) (hn : 0 < n) (hd : 0 < d) :
    m * (n * d) * (2 * (1 / (n * Real.sqrt d))) = 2 * m * Real.sqrt d := by
  have key : ∀ s : ℝ, 0 < s → s * s = d → m * (n * d) * (2 * (1 / (n * s))) = 2 * m * s := by
    intro s hs hss
    subst hss
    field_simp
  exact key _ (Real.sqrt_pos.2 hd) (Real.mul_self_sqrt hd.le)

theorem exists_dataX_transv : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ k : (U σ).Comp, ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (U σ).X k ∧ Xx.g = l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ (∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v ∈ Xx.L') ∧ ∃ M : ℝ, 0 < M ∧ M * Xx.k0 = 2 * l.M * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b) := by
  intro D j H Dw l Xo c U dict h σ hσ k
  have hP := _root_.GlobalTheory.LevGeo.hasPrinc_laws D j H Dw l Xo c U dict h σ hσ
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
  have hN' : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
  have hd' : (0 : ℝ) < D.host.d := by exact_mod_cast hd
  have hs := Real.sqrt_pos.2 hd'
  have hx1 : xiR D ≤ 1 := by
    rw [GlobalTheory.TransvModel.xiR_eq]
    have h1 : (1 : ℝ) ≤ Ideal.absNorm D.host.ccK := by exact_mod_cast hN
    have h2 : (1 : ℝ) ≤ Real.sqrt D.host.d := by
      rw [Real.one_le_sqrt]; exact_mod_cast hd
    rw [div_le_one (by positivity)]
    nlinarith
  have habs := h.xiAbs σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (U σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((U σ).X k).ξ0 D.host.φ₀
    (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((U σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((U σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hA : D.host.AA ≠ 0 := by
    intro e
    rw [e] at hone
    simp at hone
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((U σ).X k) D.host.AA D.host.AAbar
    (xiR D) l.M
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hP k)
  let Xy : DataX D.host.E D.R.r := { Xx with
    k0 := 2 * xiR D
    minWeight_pos := by have := GlobalTheory.TransvModel.xiR_eq D; rw [this]; positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((U σ).X k).ξ0 from congrArg _ h1, habs]; ring }
  have hΛ : Xy.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xy.L', v = a • u} := h3
  have hX0 : Xy.toData = (U σ).X k := h1
  have habs' : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xy.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← GlobalTheory.TransvModel.xiR_eq, ← habs τ, ← hX0]
  refine ⟨Xy, h1, h2, h3, gam_keeps_L' Xy _ hA hΛ, ((l.M * (Ideal.absNorm D.host.ccK * D.host.d) : ℕ) : ℝ),
    by positivity, ?_, fun v hv hiso b hb hbi => ?_⟩
  · change _ * (2 * xiR D) = _
    rw [GlobalTheory.TransvModel.xiR_eq]
    push_cast
    exact level_mul_two_div _ _ _ hN' hd'
  · have := GlobalTheory.TransvModel.transv_mem_of_span Xy (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (GlobalTheory.TransvModel.isIntegral_level_mul_kappa Xy.toData hN hd D.host.φ₀ (habs' _)) v hv hiso b hb hbi
    have hg : Xy.g = l.M := h2
    rwa [hg] at this

end GlobalTheory.LevGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitInertFactor
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.CongSplitFactor

variable {D : D7} {N : ℕ}

noncomputable def phi (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D) :=
  e • A + (1 - e) • (1 : Matrix (Fin N) (Fin N) (AE D))

theorem phi_apply (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) (i j : Fin N) :
    phi e A i j = e * A i j + (1 - e) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
  simp [phi, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem phi_sub_one (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A - 1 = e • (A - 1) := by
  rw [phi, sub_smul, one_smul, smul_sub]; abel

theorem phi_one (e : AE D) : phi e (1 : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
  rw [phi, ← add_smul, add_sub_cancel, one_smul]

theorem phi_mul {e : AE D} (he : e * e = e) (A B : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A * phi e B = phi e (A * B) := by
  have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem phi_mul_compl {e : AE D} (he : e * e = e) (A : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A * phi (1 - e) A = A := by
  have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  simp only [phi, sub_sub_cancel, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

noncomputable def phiHom {e : AE D} (he : e * e = e) :
    Matrix (Fin N) (Fin N) (AE D) →* Matrix (Fin N) (Fin N) (AE D) where
  toFun := phi e
  map_one' := phi_one e
  map_mul' A B := (phi_mul he A B).symm

theorem phi_map (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    (phi e A).map (sgA D) = phi (sgA D e) (A.map (sgA D)) := by
  ext i j
  simp only [Matrix.map_apply, phi_apply, map_add (f := _), map_mul, map_sub, map_one]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem phi_transpose (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    (phi e A).transpose = phi e A.transpose := by
  simp [phi, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]

theorem phi_mem_OhE {e : AE D} (he : e ∈ OhE D) {A : Matrix (Fin N) (Fin N) (AE D)}
    (hA : ∀ i j, A i j ∈ OhE D) (i j : Fin N) : phi e A i j ∈ OhE D := by
  rw [phi_apply]
  refine add_mem (mul_mem he (hA i j)) (mul_mem (sub_mem (one_mem _) he) ?_)
  by_cases h : i = j
  · simp [Matrix.one_apply, h, one_mem]
  · simp [Matrix.one_apply, h, zero_mem]

theorem hatId_mul {𝔪 : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D 𝔪) {s : AE D}
    (hs : s ∈ OhE D) : s * x ∈ hatId D 𝔪 := by
  unfold hatId at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

noncomputable def part {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) : GA D N :=
  ⟨Units.map (phiHom he) (k : GL (Fin N) (AE D)), by
    rw [PtsMem.mem_GA]
    have hk := (PtsMem.mem_GA D (k : GL (Fin N) (AE D))).1 k.2
    show ((phi e (↑(k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).map (sgA D)).transpose *
      phi e (↑(k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = 1
    rw [phi_map, hse, phi_transpose, phi_mul he, hk, phi_one]⟩

theorem part_val {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) :
    (((part he hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      phi e ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem part_inv_val {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) :
    ((((part he hse k : GA D N) : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) =
      phi e (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem part_intG {e : AE D} (he : e * e = e) (hse : sgA D e = e) (heO : e ∈ OhE D) {k : GA D N}
    (hk : k ∈ intG D N) : part he hse k ∈ intG D N := by
  rw [mem_intG] at hk ⊢
  intro i j
  refine ⟨?_, ?_⟩
  · rw [part_val]; exact phi_mem_OhE heO (fun a b => (hk a b).1) i j
  · rw [part_inv_val]; exact phi_mem_OhE heO (fun a b => (hk a b).2) i j

theorem part_sub_one_apply {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) (i j : Fin N) :
    (((part he hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j =
      e * ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) i j) := by
  rw [← Matrix.sub_apply, part_val, phi_sub_one, Matrix.smul_apply, smul_eq_mul]

theorem exists_split_inert_factor : ∀ {D : D7} {N : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {k : GA D N},
    k ∈ intG D N → CongOne D 𝔪 k →
    ∃ ks ki : GA D N, k = ks * ki ∧ ks ∈ intG D N ∧ ki ∈ intG D N ∧ CongOne D 𝔪 ks ∧
      SuppSplit D (ks : GL (Fin N) (AE D)) ∧ SuppInert D (ki : GL (Fin N) (AE D)) := by
  intro D N 𝔪 k hk hc
  obtain ⟨ε, hεO, hεε, hεs, hq⟩ := VacMove.exists_half_idem D
  set e := ε + sgA D ε with he_def
  have heO : e ∈ OhE D := add_mem hεO (VacMove.sgA_mem D hεO)
  have hse : sgA D e = e := by rw [he_def, map_add (f := _), VacMove.sgA_sgA, add_comm]
  have hee : e * e = e := by
    have h2 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, hεε]
    have h3 : sgA D ε * ε = 0 := by rw [mul_comm, hεs]
    rw [he_def, add_mul, mul_add, mul_add, hεε, hεs, h3, h2, zero_add, add_zero]
  have hfO : 1 - e ∈ OhE D := sub_mem (one_mem _) heO
  have hsf : sgA D (1 - e) = 1 - e := by rw [map_sub, map_one, hse]
  have hff : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  refine ⟨part hee hse k, part hff hsf k, ?_, part_intG hee hse heO hk, part_intG hff hsf hfO hk,
    ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      phi e ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        phi (1 - e) ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    rw [phi_mul_compl hee]
  · intro i j
    show ((((part hee hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) i j ∈ hatId D 𝔪
    rw [Matrix.sub_apply, part_sub_one_apply]
    exact hatId_mul (hc i j) heO
  · intro q hqp hin i j
    rw [part_sub_one_apply]
    exact VacMove.zeroAt_mul D hqp ((hq q hqp).1 hin) _
  · intro q hqp hin i j
    rw [part_sub_one_apply]
    exact VacMove.zeroAt_mul D hqp ((hq q hqp).2 hin) _

end GlobalTheory.CongSplitFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLatticePointOfIntegralSplitPlaceCoor
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LatFill
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_smul {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (a : AF F) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW τ (a • z) = evFin F v a * piW τ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), mul_add]
  | tmul b x =>
    rw [TensorProduct.smul_tmul']
    change splitProj τ (compFin F E v ((a • b) ⊗ₜ[F] x)) = evFin F v a * splitProj τ (compFin F E v (b ⊗ₜ[F] x))
    simp [compFin, mul_assoc]

theorem piW_inclR {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (F := F) (AF F) x) = τ x := by
  change splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x
  simp [compFin]

variable {n d : ℕ}

def fillSet (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) :
    AddSubgroup (Matrix (Fin n) (Fin d) (Fv F v)) where
  carrier := {M | ∃ γ ∈ latAtV X W v, (∀ i j, piW (t.comp σ) (γ i j) = 0) ∧ ∀ i j, piW t (γ i j) = M i j}
  zero_mem' := ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro _ _ ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
    exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1'], fun i j => by simp [h2, h2']⟩
  neg_mem' := by
    rintro _ ⟨γ, hγ, h1, h2⟩
    exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩

variable {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d} {v : Pl (F := F)} {t : E →ₐ[F] Fv F v}

theorem smul_mem_fillSet {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) {M : Matrix (Fin n) (Fin d) (Fv F v)}
    (hM : M ∈ fillSet σ X W v t) : a • M ∈ fillSet σ X W v t := by
  obtain ⟨γ, hγ, h1, h2⟩ := hM
  refine ⟨GlobalTheory.LatVac.liftV v a • γ, (GlobalTheory.LatVac.latAtV_at_stable X W v).2 a ha γ hγ, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.smul_apply, piW_smul, h1, mul_zero]
  · rw [Matrix.smul_apply, piW_smul, h2, GlobalTheory.LatVac.evFin_liftV, Matrix.smul_apply, smul_eq_mul]

theorem gen_mem_fillSet (h : IsCMExt F E σ) {x : Fin n → E} (hx : x ∈ X.L) {x' : Fin d → E} (hx' : x' ∈ W.L) :
    Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) ∈ fillSet σ X W v t := by
  have key : ∀ e ∈ intLoc F E v, ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j)) := by
    intro e he
    refine intLoc_induction (p := fun e => ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j))) (fun a ha o => ?_) ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩ ?_ ?_ he
    · have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
      refine ⟨GlobalTheory.LatVac.liftV v a • incM F (Matrix.vecMulVec (o • x) x'),
        AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha,
          _, X.L.smul_mem o hx, x', hx', rfl⟩, fun i j => ?_, fun i j => ?_⟩
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        simp only [AlgHom.comp_apply]
        ring
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        ring
    · rintro y z ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
      exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1', add_mul],
        fun i j => by simp [h2, h2', add_mul]⟩
    · rintro y ⟨γ, hγ, h1, h2⟩
      exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩
  obtain ⟨γ, hγ, h1, h2⟩ := key _ (splitIdem_mem h t)
  exact ⟨γ, hγ, fun i j => by simp [h1], fun i j => by simp [h2, Matrix.vecMulVec_apply]⟩

theorem vecMulVec_mem_fillSet (h : IsCMExt F E σ) {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc F X.L v)
    {y' : Fin d → Fv F v ⊗[F] E} (hy' : y' ∈ latLoc F W.L v) :
    Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t := by
  refine latLoc_induction (p := fun y => Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t)
    (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · refine latLoc_induction (p := fun y' => Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t y') ∈
      fillSet σ X W v t) (fun a' ha' x' hx' => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy'
    · have e : Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t fun j => a' ⊗ₜ[F] x' j) =
          (a * a') • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) := by
        ext i j; simp [splitVec, Matrix.vecMulVec_apply]; ring
      rw [e]
      exact smul_mem_fillSet (mul_mem ha ha') (gen_mem_fillSet h hx hx')
    · convert zero_mem (fillSet σ X W v t) using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
    · convert add_mem hy hz using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply, mul_add]
    · convert neg_mem hy using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert zero_mem (fillSet σ X W v t) using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert add_mem hy hz using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply, add_mul]
  · convert neg_mem hy using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]

theorem mul_mul_transpose_eq_sum {K : Type} [Field K] (b : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin d) (Fin d) K)
    (A : Matrix (Fin n) (Fin d) K) :
    b * A * cᵀ = ∑ i, ∑ j, A i j • Matrix.vecMulVec (b *ᵥ Pi.single i 1) (c *ᵥ Pi.single j 1) := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.col_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.LatFill

theorem GlobalTheory.LatFill.exists_latAtV_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∀ A : Matrix (Fin n) (Fin d) (Fv F v), (∀ i j, A i j ∈ v.adicCompletionIntegers F) →
      ∃ γ ∈ latAtV X W v, γ.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ = A := by
  intro F E _ _ _ _ _ σ n d h X W v t b c hb hc A hA
  have single_mem : ∀ {m : ℕ} (i : Fin m) (k : Fin m),
      (Pi.single i (1 : Fv F v) : Fin m → Fv F v) k ∈ v.adicCompletionIntegers F := fun i k => by
    by_cases e : k = i
    · subst e; simp
    · simp [e]
  have hT : b.1 * A * c.1ᵀ ∈ GlobalTheory.LatFill.fillSet σ X W v t := by
    rw [GlobalTheory.LatFill.mul_mul_transpose_eq_sum]
    refine sum_mem fun i _ => sum_mem fun j _ => GlobalTheory.LatFill.smul_mem_fillSet (hA i j) ?_
    obtain ⟨y, hy, ey⟩ := (hb _).1 (single_mem i)
    obtain ⟨y', hy', ey'⟩ := (hc _).1 (single_mem j)
    rw [← ey, ← ey']
    exact GlobalTheory.LatFill.vecMulVec_mem_fillSet h hy hy'
  obtain ⟨γ, hγ, h1, h2⟩ := hT
  refine ⟨γ, hγ, Matrix.ext fun i j => h1 i j, ?_⟩
  have e : γ.map (piW t) = b.1 * A * c.1ᵀ := Matrix.ext fun i j => h2 i j
  rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.mul_one]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandKazhdanDualOfTwoHyps
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

theorem gelfandKazhdanDual_of_jacquetShalika : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.GelfandKazhdanDual :=
  fun hJ hA => gelfandKazhdanDual_of_rapidDecay hJ hA (GlobalTheory.cuspRapidDecaySiegelGL_of_finite hA)

end GlobalTheory.GelfandKazhdanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfSurjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.GeomConnConst

theorem algX_top_strHom (K : Type) [Field K] (C : Scheme.{0}) [Algebra K Γ(C, ⊤)] (c : K) :
    algX (strHom K C) ⊤ c = algebraMap K Γ(C, ⊤) c := by
  rw [algebraMap_eq_strHom K C c]
  simp [algX, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]

end GlobalTheory.GeomConnConst
end

