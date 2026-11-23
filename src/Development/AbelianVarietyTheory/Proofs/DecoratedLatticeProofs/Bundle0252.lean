module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoefficient_realPlace_two_vacua : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ (τ : D.what₂.Tau) (f F F' : WO V W → ℂ), (∀ x ∈ [f, F, F'], IsThetaFunO ψ V W x ∧ IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x) → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ P Q : LPol W.rank V.rank, let pt := GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ); GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt F P)) (pt F' Q) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt f P)) (pt f Q) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X F F' := by
  first | exact @GlobalTheory.VacCoefAtPlace.coef_at_place | exact GlobalTheory.VacCoefAtPlace.coef_at_place | (intros; apply GlobalTheory.VacCoefAtPlace.coef_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaIntegrandIsUnfoldingTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.ThLaws

variable {D : D7}

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := by
  have h := congrFun (congrFun (adj_adj (Matrix.of fun _ _ => z : Mx D 1 1)) 0) 0
  simpa [adj] using h

theorem form_mulVec (S : HSp D) {ρ : ℕ} (J : Mx D S.rank ρ) (B : Fin ρ → AE D) (y : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA S) :
    GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S y (J *ᵥ B) = (fun k => cA D (B k)) ⬝ᵥ ((adj J ⬝ gA S) *ᵥ y) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form, ← Matrix.mulVec_mulVec]
  generalize gA S *ᵥ y = g
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [adj, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

abbrev tvN {ρ : ℕ} (A B : Fin ρ → AE D) : Mx D ρ ρ := vecMulVec A fun k => cA D (B k)

theorem tvN_apply {ρ : ℕ} (A B : Fin ρ → AE D) (i k : Fin ρ) : tvN A B i k = A i * cA D (B k) := rfl

theorem tvN_sq {ρ : ℕ} {A B : Fin ρ → AE D} (h : (fun k => cA D (B k)) ⬝ᵥ A = 0) : tvN A B * tvN A B = 0 := by
  ext i k
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply]
  have e : ∑ l, A i * cA D (B l) * (A l * cA D (B k)) = A i * ((fun k => cA D (B k)) ⬝ᵥ A) * cA D (B k) := by
    simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e, h]; ring

theorem tvN_mulVec {ρ : ℕ} (A B z : Fin ρ → AE D) : tvN A B *ᵥ z = ((fun k => cA D (B k)) ⬝ᵥ z) • A := by
  ext i
  simp only [Matrix.mulVec, vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem adj_tvN {ρ : ℕ} (A B : Fin ρ → AE D) : adj (tvN A B) = tvN B A := by
  ext i k
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply, vecMulVec_apply, map_mul, cA_cA']
  ring

def tvGL {ρ : ℕ} (A B : Fin ρ → AE D) (h : (fun k => cA D (B k)) ⬝ᵥ A = 0) : GL (Fin ρ) (AE D) :=
  ⟨1 + tvN A B, 1 - tvN A B,
    by rw [show (1 + tvN A B) * (1 - tvN A B) = 1 - tvN A B * tvN A B by noncomm_ring, tvN_sq h, sub_zero],
    by rw [show (1 - tvN A B) * (1 + tvN A B) = 1 - tvN A B * tvN A B by noncomm_ring, tvN_sq h, sub_zero]⟩

theorem tvGL_val {ρ : ℕ} (A B : Fin ρ → AE D) (h : (fun k => cA D (B k)) ⬝ᵥ A = 0) :
    (tvGL A B h).1 = 1 + tvN A B := rfl

theorem tvGL_inv_val {ρ : ℕ} (A B : Fin ρ → AE D) (h : (fun k => cA D (B k)) ⬝ᵥ A = 0) :
    (tvGL A B h)⁻¹.1 = 1 - tvN A B := rfl

theorem mt_levi_tv {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (A B : Fin ρ → AE D)
    (h : (fun k => cA D (B k)) ⬝ᵥ A = 0) :
    mt S (d.levi (tvGL A B h)) = 1 + d.jX ⬝ tvN A B ⬝ d.pX - d.jY ⬝ tvN B A ⬝ d.pY := by
  rw [d.mt_levi, tvGL_val, tvGL_inv_val, adj_sub, adj_one, adj_tvN]
  conv_rhs => rw [← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

theorem transv_null {S : HSp D} {y v w : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA S} (hvv : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S v v = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.transv S w v y = y + GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S y v • w - GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S y w • v := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.transv
  rw [hvv, mul_zero, zero_mul, zero_smul, sub_zero]

set_option maxHeartbeats 1000000 in
theorem levi_isTransv {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (A B : Fin ρ → AE D)
    (h : (fun k => cA D (B k)) ⬝ᵥ A = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv S (d.jX *ᵥ A) (d.jY *ᵥ B) (d.levi (tvGL A B h)) := by
  intro y
  have hv : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S z (d.jY *ᵥ B) = (fun k => cA D (B k)) ⬝ᵥ (d.pX *ᵥ z) := fun z => by
    rw [form_mulVec, ← d.pX_eq]
  have hvv : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S (d.jY *ᵥ B) (d.jY *ᵥ B) = 0 := by
    rw [hv, Matrix.mulVec_mulVec, d.pX_jY, Matrix.zero_mulVec, dotProduct_zero]
  have e1 : (d.jX ⬝ tvN A B ⬝ d.pX) *ᵥ y = GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S y (d.jY *ᵥ B) • (d.jX *ᵥ A) := by
    rw [hv y, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tvN_mulVec, Matrix.mulVec_smul]
  have e2 : (d.jY ⬝ tvN B A ⬝ d.pY) *ᵥ y = GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S y (d.jX *ᵥ A) • (d.jY *ᵥ B) := by
    rw [form_mulVec, ← d.pY_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tvN_mulVec, Matrix.mulVec_smul]
  rw [transv_null hvv]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.act
  rw [mt_levi_tv, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, e1, e2]

end GlobalTheory.ThLaws

namespace GlobalTheory.ThLaws

variable {D : D7}

theorem trace_half_smul (x : AF D.host.F) :
    Algebra.trace (AF D.host.F) (AE D) (x • incA D (algebraMap D.host.F D.host.E (1 / 2))) = x := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have t1 : Algebra.trace (AF D.host.F) (AE D) (incA D (algebraMap D.host.F D.host.E (1 / 2))) = 1 := by
    have := GlobalTheory.SymplecticOrthogonalSesquilinear.trace_one_tmul (F := D.host.F) (E := D.host.E) (AF D.host.F)
      (algebraMap D.host.F D.host.E (1 / 2))
    rw [Algebra.trace_algebraMap, D.sp.cm.deg2] at this
    refine this.trans ?_
    norm_num
  rw [map_smul, t1, smul_eq_mul, mul_one]

theorem exists_psiE_ne_one {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) : ∃ t : AE D, psiE ψ t ≠ 1 := by
  obtain ⟨x, hx⟩ := hψ.1.2.2.2
  exact ⟨x • incA D (algebraMap D.host.F D.host.E (1 / 2)), by rw [psiE, trace_half_smul]; exact hx⟩

end GlobalTheory.ThLaws

open GlobalTheory.ThLaws in
theorem GlobalTheory.th_isTh : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1))
    (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ), Quasi ψ J.W₀ B.L y →
    ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = x0 B →
      IsTh ψ J.d B.V x₀ (th J ψ B y) := by
  intro D ψ hψ σ J B y hy x₀ hx₀
  obtain ⟨hcont, -, hleft, hcen, -, -⟩ := _root_.GlobalTheory.Unf.FB.ThLaws.th_laws D ψ hψ σ J B y hy
  obtain ⟨x₁, hx₁, -, -, hlast, hq⟩ := _root_.GlobalTheory.Unf.FB.basePoint_spec D σ B
  have e : x₁ = x₀ := rat_injective (hx₁.trans hx₀.symm)
  refine ⟨hcont.comp continuous_subtype_val, fun γ hγQ hγN n hn => hleft γ hγN hγQ n hn, fun c n hn => ?_, ?_⟩
  · rw [hcen c n hn, hx₀, hq]
  intro j a ha1 ha0 hg
  have hl : a (Fin.last σ) = 0 := hlast a (by rw [e]; exact hg)
  have hj : j.1 < σ := by
    by_contra hc
    have : j = Fin.last σ := Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)
    rw [this, hl] at ha1
    exact zero_ne_one ha1
  let j' : Fin (σ + 1) := ⟨j.1 + 1, by omega⟩
  have hjj : j < j' := by rw [Fin.lt_def]; simp [j']
  obtain ⟨t, ht⟩ := exists_psiE_ne_one hψ
  let A : Fin (σ + 1) → AE D := GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a
  let Bv : Fin (σ + 1) → AE D := fun k => if k = j' then cA D t else 0
  have hB0 : ∀ k, k ≠ j' → Bv k = 0 := fun k hk => if_neg hk
  have hA0 : ∀ i, j < i → A i = 0 := fun i hi => by
    show incA D (a i) = 0
    rw [ha0 i hi, map_zero]
  have hN : ∀ i k, ¬(i ≤ j ∧ k = j') → A i * cA D (Bv k) = 0 := by
    intro i k hik
    by_cases hk : k = j'
    · rw [hA0 i (not_le.1 fun hi => hik ⟨hi, hk⟩), zero_mul]
    · rw [hB0 k hk, map_zero, mul_zero]
  have hAB : (fun k => cA D (Bv k)) ⬝ᵥ A = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm]
    exact hN k k fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj)
  have hupper : tvGL A Bv hAB ∈ upperUni (σ + 1) (AE D) := fun i k => by
    refine ⟨fun hki => ?_, ?_⟩
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hki), tvN_apply,
        hN i k fun h => absurd (h.2 ▸ hki) (not_lt.2 (le_of_lt (lt_of_le_of_lt h.1 hjj))), zero_add]
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_eq, tvN_apply,
        hN i i fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj), add_zero]
  have hUX : tvGL A Bv hAB ∈ UX D (σ + 1) := mem_UX.2 hupper
  have hu : J.d.levi (tvGL A Bv hAB) ∈ flagN J.d := J.d.levi_mem_NFlag hupper
  have hup : upSum (tvN A Bv) = t := by
    unfold upSum
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j']
    · rw [if_pos (by simp [j']), tvN_apply, show Bv j' = cA D t from if_pos rfl, cA_cA']
      show incA D (a j) * t = t
      rw [ha1, map_one, one_mul]
    · intro k _ hk
      rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = j'
      · rw [if_neg]
        intro h
        apply hi
        rw [hk] at h
        exact Fin.ext (by simp [j'] at h; omega)
      · rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨J.d.jY *ᵥ Bv, J.d.levi (tvGL A Bv hAB), star (psiE ψ t), ?_, levi_isTransv J.d A Bv hAB,
    Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_iInf.2 fun i => ?_⟩, ?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form J.W (J.d.jX *ᵥ A) (J.d.jY *ᵥ Bv) = 0
    rw [form_mulVec, ← J.d.pX_eq, Matrix.mulVec_mulVec, J.d.pX_jX, Matrix.one_mulVec, hAB]
  · rw [mem_fixer]
    have hcol : ∀ m, (tvGL A Bv hAB).1 m i.1 = (1 : Mx D (σ + 1) (σ + 1)) m i.1 := fun m => by
      rw [tvGL_val, Matrix.add_apply, tvN_apply,
        hN m i.1 fun h => absurd (h.2 ▸ i.2) (not_le.2 hjj), add_zero]
    ext k l
    have h1 := congrFun (congrFun (J.d.levi_jX (tvGL A Bv hAB)) k) i.1
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id] at h1 ⊢
    rw [h1]
    simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro h1
    apply ht
    rw [← star_star (psiE ψ t), h1, star_one]
  · intro n hn n' hn'
    have hx : ∀ u ∈ UX D (σ + 1), zl B ⬝ u.1 = zl B := fun u hu => zEll_mul B.L B.ζ hu
    have hJu : jacS ψ J.d B.L (zl B) (J.d.levi (tvGL A Bv hAB)) = id := by
      have := jacS_levi_mul ψ J.d B.L (zl B) (hx _ hUX) 1
      rwa [mul_one, jacS_one] at this
    have hpu : psiFlag ψ J.d (J.d.levi (tvGL A Bv hAB)) = psiE ψ t := by
      rw [psiFlag, blockX_levi, tvGL_val, upSum_add, upSum_one, zero_add, hup]
    simp only [th]
    rw [GlobalTheory.JacHom.jacS_mul J.d hx ψ (mul_mem hn hu) hn', GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hu, hJu,
      GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hn', psiFlag_mul J.d ψ (mul_mem hn hu) hn', psiFlag_mul J.d ψ hn hu,
      psiFlag_mul J.d ψ hn hn', hpu]
    simp only [id, star_mul']
    ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealGeneratedByOneAlmostEverywhere
section
open Formalism.BasicNotions IsDedekindDomain NumberField

namespace GlobalTheory.IdeleGen

theorem exists_nat_mem_mul_integral {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 E, (N : E) * b = (o : E) := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hbot : (I : Submodule (𝓞 E) E) ≠ ⊥ := by
    intro h
    apply hI
    exact FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).1 hbot
  obtain ⟨j, hj⟩ := hint x hxI
  have hj' : (j : E) = (a : E) * x := by
    simpa [Algebra.smul_def] using hj
  have haE : (a : E) ≠ 0 := by exact_mod_cast ha0
  have hj0 : j ≠ 0 := by
    intro h; rw [h] at hj'; simp at hj'
    rcases hj' with h1 | h1
    · first | exact ha0 h1 | exact ha0 h1.symm | exact haE h1 | exact haE h1.symm
    · first | exact hx0 h1 | exact hx0 h1.symm
  set Nd := Ideal.absNorm (Ideal.span {a}) with hNd
  set Nj := Ideal.absNorm (Ideal.span {j}) with hNj
  have hNd0 : Nd ≠ 0 := by
    rw [hNd, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ha0
  have hNj0 : Nj ≠ 0 := by
    rw [hNj, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hj0
  obtain ⟨o₁, ho₁⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  obtain ⟨o₂, ho₂⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {j}))
  have ho₁E : ((Nd : 𝓞 E) : E) = (o₁ : E) * (a : E) := by rw [← ho₁]; push_cast; ring
  have ho₂E : ((Nj : 𝓞 E) : E) = (o₂ : E) * (j : E) := by rw [← ho₂]; push_cast; ring
  refine ⟨Nd * Nj, mul_ne_zero hNd0 hNj0, ?_, ?_⟩
  · have : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) * o₂ * a : 𝓞 E) • x := by
      rw [Algebra.smul_def]
      have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
      rw [e1, ho₂E]
      have hal : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E) := fun _ => rfl
      rw [hal]
      push_cast
      linear_combination ((Nd : E) * (o₂ : E)) * hj'
    rw [this]
    exact Submodule.smul_mem _ _ hxI
  · intro b hb
    obtain ⟨y, hy⟩ := hint b hb
    have hy' : (y : E) = (a : E) * b := by simpa [Algebra.smul_def] using hy
    refine ⟨(Nj : 𝓞 E) * o₁ * y, ?_⟩
    have e1 : ((Nd * Nj : ℕ) : E) = ((Nd : 𝓞 E) : E) * ((Nj : 𝓞 E) : E) := by push_cast; ring
    rw [e1, ho₁E]
    push_cast
    linear_combination (-((Nj : E) * (o₁ : E))) * hy'

theorem aeGen : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 →
    ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ S, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧
      ((c : D.host.F) : D.host.E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = (o : D.host.E) := by
  intro D I hI
  obtain ⟨N, hN0, hNI, hNb⟩ := exists_nat_mem_mul_integral I hI
  have hc0 : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  have hfin := Ideal.finite_factors hc0
  refine ⟨hfin.toFinset, fun v hv => ⟨(N : 𝓞 D.host.F), ?_, ?_, ?_⟩⟩
  · intro hmem
    apply hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNI
  · have : (((N : 𝓞 D.host.F) : D.host.F) : D.host.E) = (N : D.host.E) := by push_cast; rfl
    rw [this]; exact hNb

end GlobalTheory.IdeleGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocalGeneratorAtBasePrime
section
open Formalism.BasicNotions IsDedekindDomain NumberField

namespace GlobalTheory.LocGen

theorem exists_gen_mul_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (J : Ideal S) (hJ : J ≠ ⊥) :
    ∃ y ∈ J, y ≠ 0 ∧ ∃ c : R, c ∉ p ∧ ∀ j ∈ J, ∃ o : S, algebraMap R S c * j = y * o := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hr'0 : algebraMap R S r ≠ 0 := fun h => hr0 (hinj (by rw [h, map_zero]))
  have hJ0 : J ≠ 0 := hJ
  have hIv0 : J * Ideal.span {algebraMap R S r} ≠ 0 :=
    mul_ne_zero hJ0 (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr'0)
  obtain ⟨y, hy⟩ := exists_sup_span_eq (Ideal.mul_le_left : J * Ideal.span {algebraMap R S r} ≤ J) hIv0
  have hyJ : y ∈ J := hy ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {y} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hyJ)
  have key : ¬ Ideal.comap (algebraMap R S) K ≤ p := by
    intro h
    obtain ⟨Q, hKQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p K h
    have hrQ : algebraMap R S r ∈ Q := by
      change r ∈ Ideal.under R Q
      rw [hQp]; exact hr
    have h1 : J * Ideal.span {algebraMap R S r} ≤ J * Q :=
      Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).mpr hrQ)
    have h2 : Ideal.span {y} ≤ J * Q := hK ▸ Ideal.mul_mono_right hKQ
    have h3 : J ≤ J * Q := calc J = _ := hy.symm
      _ ≤ J * Q := sup_le h1 h2
    have h4 : J * Q = J * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h3
    exact hQ.ne_top (mul_left_cancel₀ hJ0 h4)
  rw [SetLike.not_le_iff_exists] at key
  obtain ⟨c, hcK, hcp⟩ := key
  rw [Ideal.mem_comap] at hcK
  refine ⟨y, hyJ, ?_, c, hcp, ?_⟩
  · rintro rfl
    have hJK : J * K = 0 := by rw [← hK, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have hK0 : K = 0 := (mul_eq_zero.mp hJK).resolve_left hJ0
    rw [hK0, Ideal.zero_eq_bot, Ideal.mem_bot] at hcK
    exact hcp (by rw [hinj (hcK.trans (map_zero _).symm)]; exact p.zero_mem)
  · intro j hj
    have hm : j * algebraMap R S c ∈ Ideal.span {y} := hK ▸ Ideal.mul_mem_mul hj hcK
    obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨o, by rw [mul_comm, ← ho, mul_comm]⟩

end GlobalTheory.LocGen

namespace GlobalTheory


open GlobalTheory.LocGen in
theorem fracIdeal_locGen : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 →
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ a : D.host.E, a ≠ 0 ∧ ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧
      ((c : D.host.F) : D.host.E) * a ∈ I ∧
      ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a * (o : D.host.E) := by
  intro D I hI v
  letI : Algebra (𝓞 D.host.F) (𝓞 D.host.E) := (RingOfIntegers.mapRingHom D.host.F.subtype).toAlgebra
  have hφ : ∀ c : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.F) : D.host.E) := fun c => rfl
  haveI : Algebra.IsIntegral (𝓞 D.host.F) (𝓞 D.host.E) := Algebra.IsIntegral.tower_top (R := ℤ)
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    intro x y h
    have h' := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) h
    simp only [hφ] at h'
    exact RingOfIntegers.ext (Subtype.ext h')
  obtain ⟨d, J, hd, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ ⊥ := by
    rintro rfl
    exact hI (by rw [FractionalIdeal.coeIdeal_bot, mul_zero])
  obtain ⟨y, hyJ, hy0, c, hcv, hc⟩ := exists_gen_mul_of_isIntegral hinj v.asIdeal v.ne_bot J hJ
  have hd' : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hy' : ((y : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  refine ⟨(y : D.host.E) * (d : D.host.E)⁻¹, mul_ne_zero hy' (inv_ne_zero hd'), c, hcv, ?_, ?_⟩
  · rw [FractionalIdeal.mem_singleton_mul]
    refine ⟨algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c * y), ?_, ?_⟩
    · exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, J.mul_mem_left _ hyJ, rfl⟩
    · rw [map_mul]
      show _ = _ * (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) * (y : D.host.E))
      rw [hφ]
      ring
  · intro b hb
    rw [FractionalIdeal.mem_singleton_mul] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨j, hj, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hb'
    obtain ⟨o, ho⟩ := hc j hj
    refine ⟨o, ?_⟩
    have h2 : ((c : D.host.F) : D.host.E) * (j : D.host.E) = (y : D.host.E) * (o : D.host.E) := by
      have h3 := congrArg (algebraMap (𝓞 D.host.E) D.host.E) ho
      rw [map_mul, map_mul] at h3
      exact h3
    calc ((c : D.host.F) : D.host.E) * (((d : 𝓞 D.host.E) : D.host.E)⁻¹ * (j : D.host.E))
        = (d : D.host.E)⁻¹ * (((c : D.host.F) : D.host.E) * (j : D.host.E)) := by ring
      _ = (d : D.host.E)⁻¹ * ((y : D.host.E) * (o : D.host.E)) := by rw [h2]
      _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenericTermsPointsAgreeGroupSumsCorankOne
section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem genericTerms_points_agree_groupSums_corankOne : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ), (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) ∧ (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ) ∧ (∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν = grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν) ∧ ((∀ t ∈ (Y.tO u u).genSet, J2of Y u u νL (ptPN t) = 0 → (Y.tO u u).vec t = 0) → PN.AmpInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)) := by
  intro D X Y u νL νB ng
  have hs : (genT (scT (Y.tO u u))).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hs' : (genT (Y.tO u u)).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hA : ∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨cls1 Y u t, nmlOf Y u u t, t, hs ▸ ht, hv, rfl, hp, rfl⟩
  have hB : ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs'] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨clsG Y u t, nmlOf Y u u t, t, hs' ▸ ht, hv, rfl, hp, rfl⟩
  have hG : ∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν =
      grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν := by
    intro c γ ν
    unfold PN.grp grpF
    rw [hs]
    rfl
  refine ⟨fun γ => (hA γ).trans (hB γ).symm, hA, hG, ?_⟩
  intro h
  have hJ : ∀ γ, 0 ≤ J2of Y u u νL γ := fun γ => J2of_nonneg Y u u νL γ
  have hV : ∀ c γ ν, J2of Y u u νL γ = 0 → grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν = 0 := by
    intro c γ ν h0
    unfold grpF
    have hz : ∀ t, ((Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}).indicator
        (Y.tO u u).vec t = 0 := by
      intro t
      by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}
      · rw [Set.indicator_apply, if_pos ht]
        exact h t ht.1 (by rw [ht.2.2.1]; exact h0)
      · rw [Set.indicator_apply, if_neg ht]
    simp only [hz, tsum_zero]
  refine ⟨fun c γ ν => ?_, hJ, fun c γ ν => ?_⟩
  · show 0 ≤ a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν
    unfold a2F
    exact div_nonneg (by positivity) (hJ γ)
  · rw [hG]
    show ‖grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν‖ ^ 2 ≤
      a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν * J2of Y u u νL γ
    unfold a2F
    by_cases h0 : J2of Y u u νL γ = 0
    · rw [hV c γ ν h0]; simp
    · rw [div_mul_cancel₀ _ h0]

end GlobalTheory.Core.One
end

