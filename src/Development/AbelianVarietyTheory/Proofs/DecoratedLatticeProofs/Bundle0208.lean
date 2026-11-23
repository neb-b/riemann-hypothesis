module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSumHolds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PerSumProof

variable {D : D7}

theorem conv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) {f : GA D B.V → ℂ}
    (hf : IsContAut B.V f) {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) :
    (∀ h, IntegrableOn (besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν) ∧
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  haveI := B.vA.haar
  obtain ⟨K, hK, hcov⟩ := B.cpt
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (isIsoSub_e B.d)).1
  obtain ⟨hemb, -, hnorm, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  have hch := GlobalTheory.MixPer.charLaws D ψ hψ.1 B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  have hfin : B.vA.μ B.vA.𝓕 < ⊤ := by
    refine GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hK (fun g => ?_) B.vA.μ B.vA.fund
    obtain ⟨γ, hγ, hk⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, γ * g, hk, by group⟩
  have hc : Continuous fun q : GA D B.A × flagN B.d => besFun ψ 1 B.d B.o B.ζ φ f q.1 q.2 :=
    ((hφ.2.comp continuous_fst).mul (hf.2.comp ((continuous_subtype_val.comp continuous_snd).mul
      (hemb.comp continuous_fst)))).mul ((hch.1 _).comp (continuous_subtype_val.comp continuous_snd)).star
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hc.continuousOn
  refine GlobalTheory.Per.FJConv.iterated_integrableOn hfin.ne (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top) hc (M := M)
    fun g n => ?_
  obtain ⟨γ, hγ, hk⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹, hnorm n.1 n.2 γ⟩
  have e' : embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹ = γ'.1 * k'.1 := congrArg Subtype.val e
  have hδ : embA B.d B.o γ ∈ GQ B.V := by simpa using (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
  have hγ'Q : γ'.1 ∈ GQ B.V := hγ'
  have en : n.1 = (embA B.d B.o γ)⁻¹ * (γ'.1 * k'.1) * embA B.d B.o γ := by
    rw [← e']; group
  have e1 : besFun ψ 1 B.d B.o B.ζ φ f g n = besFun ψ 1 B.d B.o B.ζ φ f (γ * g) k' := by
    simp only [besFun]
    have f1 : f (n.1 * embA B.d B.o g) = f (k'.1 * embA B.d B.o (γ * g)) := by
      rw [← hf.1 ((embA B.d B.o γ)⁻¹ * γ'.1) (mul_mem (inv_mem hδ) hγ'Q) (k'.1 * embA B.d B.o (γ * g)), en, map_mul]
      congr 1; group
    have p1 : psiBes ψ B.d 1 (vecB B.o B.ζ) n.1 = psiBes ψ B.d 1 (vecB B.o B.ζ) k'.1 := by
      have := hch.2.2.1 (γ'.1 * k'.1) γ⁻¹
      rw [map_inv, inv_inv, ← en] at this
      rw [this, psiBes_mul B.d ψ 1 _ γ'.2 k'.2, hch.2.1 _ _ hγ'Q, one_mul]
    rw [f1, p1, hφ.1 γ hγ g]
  rw [e1]
  exact hM (γ * g, k') ⟨hk, hk'⟩

end GlobalTheory.SeeSaw.PerSumProof

namespace GlobalTheory.SeeSaw

theorem perSum_all : ∀ D : D7, PerSum D := by
  intro D ψ hψ ρ B f hf I s a φ hφ
  have hconv := fun i (hi : i ∈ s) => PerSumProof.conv hψ B hf (hφ i hi)
  simp only [BesLev.per, besPer]
  have e1 : ∀ h n, besFun ψ 1 B.d B.o B.ζ (∑ i ∈ s, a i • φ i) f h n =
      ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ (φ i) f h n := by
    intro h n
    simp only [besFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1]
  have e2 : (fun h => ∫ n in B.vN.𝓝, ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ (φ i) f h n ∂B.vN.ν) =
      fun h => ∑ i ∈ s, a i * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ (φ i) f h n ∂B.vN.ν := by
    funext h
    rw [integral_finsetSum s fun i hi => ((hconv i hi).1 h).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [e2, integral_finsetSum s fun i hi => (hconv i hi).2.const_mul (a i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

private theorem pow_exp_I_injective (a b : ℕ)
    (h : Complex.exp Complex.I ^ a = Complex.exp Complex.I ^ b) : a = b := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have him := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
    Complex.natCast_im, Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re] at him
  have hre : ((a : ℝ) - b) = n * (2 * Real.pi) := by linarith
  by_cases h0 : n = 0
  · subst h0
    have : (a : ℝ) = b := by simpa [sub_eq_zero] using hre
    exact_mod_cast this
  · exfalso
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h0
    have hpi : Real.pi = ((((a : ℚ) - b) / (2 * n) : ℚ) : ℝ) := by
      push_cast
      field_simp
      linarith
    exact irrational_pi ⟨_, hpi.symm⟩

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_pow_eq_pow_of_eq_exp_I_or_inv : ∀ (a b : ℕ) (w : ℂ), (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) → w ^ a = w ^ b → a = b := by
  intro a b w hw hab
  rcases hw with rfl | rfl
  · exact pow_exp_I_injective a b hab
  · rw [inv_pow, inv_pow, _root_.inv_inj] at hab
    exact pow_exp_I_injective a b hab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorFockUnitScaledBasisMonomial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.FockScal

open GlobalTheory.FockSubst

theorem foldr_scal {ι X : Type} {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop} (c : ι → ℂ)
    (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (h : ∀ i f, P f → A' i f = c i • A i f)
    {f : X → ℂ} (hf : P f) (l : List ι) :
    P (l.foldr (fun i g => A i g) f) ∧
      l.foldr (fun i g => A' i g) f = (l.map c).prod • l.foldr (fun i g => A i g) f := by
  induction l with
  | nil => simpa using hf
  | cons i l ih =>
    refine ⟨hA _ _ ih.1, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih.2, h _ _ (hsm _ _ ih.1), Asm _ _ _ ih.1, smul_smul]

theorem pure_monomial {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) (α : ι →₀ ℕ) :
    pureTensorL A f (MvPolynomial.monomial α 1) = opPow A α f := by
  unfold pureTensorL
  have := (MvPolynomial.basisMonomials ι ℂ).constr_basis ℂ (fun k : ι →₀ ℕ => opPow A k f) α
  rwa [MvPolynomial.coe_basisMonomials] at this

theorem prod_fiber {ι κ : Type} [Fintype κ] [DecidableEq κ] (g : ι → κ) (μ : κ → ℂ) (α : ι →₀ ℕ) :
    ((Finsupp.toMultiset α).toList.map fun i => μ (g i)).prod = ∏ τ, μ τ ^ (∑ v ∈ α.support with g v = τ, α v) := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add]), Finsupp.prod,
    ← Finset.prod_fiberwise (s := α.support) (g := g)]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.1 hv).2]

theorem pure_scal {ι κ X : Type} [Fintype κ] [DecidableEq κ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (g : ι → κ) (μ : κ → ℂ) (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (h : ∀ i f, P f → A' i f = μ (g i) • A i f)
    {f : X → ℂ} (hf : P f) (α : ι →₀ ℕ) :
    pureTensorL A' f (MvPolynomial.monomial α 1) =
      (∏ τ, μ τ ^ (∑ v ∈ α.support with g v = τ, α v)) • pureTensorL A f (MvPolynomial.monomial α 1) := by
  rw [pure_monomial, pure_monomial]
  unfold opPow
  rw [(foldr_scal (fun i => μ (g i)) hsm hA Asm h hf _).2, prod_fiber]

theorem unitMap_smul {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) {z : ℂ} (hz : z ≠ 0)
    (a : Fin m) (j : Fin n) : unitMap (z • B) B' a j = z⁻¹ • unitMap B B' a j := by
  have e : z • B = B * (z • (1 : Matrix (Fin n) (Fin n) ℂ)) := by simp
  have e' : (z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ = z⁻¹ • 1 :=
    Matrix.inv_eq_left_inv (by simp [smul_smul, hz])
  unfold unitMap
  rw [e, Matrix.mul_inv_rev, e']
  simp

theorem cplxO_pm {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) (a : Fin m) (j : Fin n) (u : Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t u = ((if decide (s = 1 ↔ t = 1) then 1 else -1 : ℂ) * Complex.I) • u := by
  have h1 : (-1 : Matrix (Fin n) (Fin n) ℂ) ≠ 1 := fun h => by
    have := congrFun (congrFun h j) j
    simp at this
    norm_num at this
  have h2 : (-1 : Matrix (Fin m) (Fin m) ℂ) ≠ 1 := fun h => by
    have := congrFun (congrFun h a) a
    simp at this
    norm_num at this
  unfold cplxO
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [h1, h2]

theorem pureTensorO_scal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ ζ : D.what₂.Tau → ℂ, (∀ τ, ‖ζ τ‖ = 1) → ∀ α : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T x.s y.s (fun τ => ζ τ • x.B τ) y.B f (MvPolynomial.monomial α 1) = (∏ τ, (if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (MvPolynomial.monomial α 1) := by
  intro D ψ θ hψ hθ S T x y hx hy f hf ζ hζ α
  have hz : ∀ τ, ζ τ ≠ 0 := fun τ h => by simpa [h] using hζ τ
  let μ : D.what₂.Tau → ℂ := fun τ => if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) (fun τ => ζ τ • x.B τ) y.B i g =
      μ i.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, μ]
    rw [unitMap_smul _ _ (hz ρ), aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (cplxO_pm (hx.pm ρ) (hy.pm ρ) a j _)]
    congr 1
    rw [map_inv₀, ← Complex.inv_eq_conj (hζ ρ), inv_inv]
    simp only [decide_eq_true_eq]
  have hA : ∀ i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i f) :=
    fun _ _ h => aPlus_th hψ hθ _ _ _ h
  have Asm : ∀ i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i f :=
    fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  exact pure_scal (P := IsThetaFunO ψ S T) (fun v : FVar D T.rank S.rank => v.1) μ
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) hA Asm key hf α

end GlobalTheory.FockScal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidValOfCuspRapidDecay
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem rapidVal_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, RapidVal D := by
  intro hP D θ hθ V S M J χ G hG v
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hG)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r w =>
    have h1 := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ (hM.aut w) (hM.cusp w)
    have h2 : G (r • PiTensorProduct.tprod ℂ w) = r • PiTensorProduct.lift.symm G w := by
      simp [PiTensorProduct.lift_symm]
    rw [h2]
    exact GlobalTheory.Grow.RapidDec.smul r h1
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact hx.add hy

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.CenterScalar

theorem scalar_of_comm_unitary {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → U * C = C * U) : ∃ ζ : ℂ, C = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  open scoped Matrix.Norms.L2Operator in
  have hall : ∀ M : Matrix (Fin n) (Fin n) ℂ, M * C = C * M := by
    intro M
    have hM : M ∈ Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      rw [CStarAlgebra.span_unitary]; trivial
    induction hM using Submodule.span_induction with
    | mem U hU => exact h U hU.1
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.add_mul, Matrix.mul_add, ha, hb]
    | smul c a _ ha => rw [Matrix.smul_mul, Matrix.mul_smul, ha]
  obtain ⟨ζ, hζ⟩ := Matrix.mem_range_scalar_of_commute_single (M := C) (fun i j _ => hall _)
  exact ⟨ζ, by rw [← hζ, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem scalar_of_comm {n : ℕ} (G s B A : Matrix (Fin n) (Fin n) ℂ) (p : ℕ) (hs : s = 1 ∨ s = -1)
    (hB : IsONBasis G s B p) (hA : Aᴴ * G * A = G)
    (h : ∀ M : Matrix (Fin n) (Fin n) ℂ, Mᴴ * G * M = G → M * A = A * M) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ A = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨ε, hε, h1, h2⟩ := hB
  have hdet : (Matrix.diagonal (fun a => (ε a : ℂ))).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    rcases hε a with h | h <;> simp [h.1]
  rw [← h1, Matrix.det_mul, Matrix.det_mul] at hdet
  have hBu : IsUnit B.det := (right_ne_zero_of_mul hdet).isUnit
  have hG : G.det ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hdet)
  have i1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ hBu
  have i2 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hBu
  obtain ⟨c, hc⟩ : ∃ c : ℂ, Bᴴ * G * B = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have e : B⁻¹ * (s * B) = Matrix.diagonal (fun a => (ε a : ℂ)) := by
      rw [h2, ← Matrix.mul_assoc, i1, Matrix.one_mul]
    rcases hs with rfl | rfl
    · exact ⟨1, by rw [h1, ← e, Matrix.one_mul, i1, one_smul]⟩
    · exact ⟨-1, by rw [h1, ← e, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, i1, neg_smul, one_smul]⟩
  have hG' : (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ = G := by
    calc _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [i2]; simp
  obtain ⟨ζ, hζ⟩ := scalar_of_comm_unitary (B⁻¹ * A * B) fun U hU => by
    have k := h (B * U * B⁻¹) (by
      calc _ = (B⁻¹)ᴴ * (Uᴴ * (Bᴴ * G * B) * U) * B⁻¹ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by
            rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
        _ = G := hG')
    calc U * (B⁻¹ * A * B) = (B⁻¹ * B) * U * (B⁻¹ * A * B) := by rw [i1, Matrix.one_mul]
      _ = B⁻¹ * (B * U * B⁻¹ * A) * B := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * A * B * U * (B⁻¹ * B) := by rw [k]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [i1, Matrix.mul_one]
  have hAζ : A = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    calc A = (B * B⁻¹) * A * (B * B⁻¹) := by rw [i2, Matrix.one_mul, Matrix.mul_one]
      _ = B * (B⁻¹ * A * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hζ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, i2]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, norm_one, Subsingleton.elim _ _⟩
  · refine ⟨ζ, ?_, hAζ⟩
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hG0 : G ≠ 0 := fun e => hG (by rw [e, Matrix.det_zero])
    rw [hAζ, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul] at hA
    have e : ζ * star ζ = 1 := by
      by_contra hne
      apply hG0
      have : (ζ * star ζ - 1) • G = 0 := by rw [sub_smul, hA, one_smul, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    have e2 : ‖ζ‖ * ‖ζ‖ = 1 := by simpa using congrArg norm e
    nlinarith [norm_nonneg ζ]

theorem center_scalar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (x : DefSp S), x.Is → ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ∀ τ : D.what₂.Tau, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  intro D θ hθ S x hx z _ hz τ
  obtain ⟨p, hp⟩ := hx.onb τ
  refine scalar_of_comm (gramAt D S τ) (x.s τ) (x.B τ) _ p (hx.pm τ) hp
    (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S z τ) fun M hM => ?_
  have ha := GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ (g := M) hM
  have hc := congrArg (infMat D.sp.cm.sig S.gram (θ τ)) (Subgroup.mem_center_iff.1 hz (atTau θ S τ M))
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, ha.2.1] at hc
  exact hc

end GlobalTheory.CenterScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealFormsRangeMultiplicityOfScalarHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw

theorem rangeX_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → RangeX R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG t
  have hm := hG.core.models
  exact GlobalTheory.DefiniteMult.range_top R hm.inf hm.cX hm.prX hm.HX t

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
section
namespace I195MixedCoordinates_8f574703cd7515a934a5d64e

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_8f574703cd7515a934a5d64e

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem sch_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f f', IsThetaFunO ψ (dblSp A) B f → IsThetaFunO ψ (dblSp A) B f' → ∀ c : ℂ, IsThetaFunO ψ (dblSp A) B (f + f') ∧ IsThetaFunO ψ (dblSp A) B (c • f) ∧ sch ψ A B ν 𝓨 (f + f') = sch ψ A B ν 𝓨 f + sch ψ A B ν 𝓨 f' ∧ sch ψ A B ν 𝓨 (c • f) = c • sch ψ A B ν 𝓨 f := by
  intro D ψ hψ A B ν 𝓨 hν f f' hf hf' c
  refine ⟨GlobalTheory.OrientedHeis.theta_add hf hf', GlobalTheory.OrientedHeis.theta_smul c hf, ?_, ?_⟩
  · funext x
    have h1 := (dblDec A).integrableOn_mixS hψ.1.1 hν hf x 0
    have h2 := (dblDec A).integrableOn_mixS hψ.1.1 hν hf' x 0
    simp only [sch, HypDec.mixS, _root_.I195MixedCoordinates_8f574703cd7515a934a5d64e.source, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
    exact integral_add h1 h2
  · funext x
    simp only [sch, HypDec.mixS, _root_.I195MixedCoordinates_8f574703cd7515a934a5d64e.source, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      integral_const_mul]

end GlobalTheory.StdUnn
end

