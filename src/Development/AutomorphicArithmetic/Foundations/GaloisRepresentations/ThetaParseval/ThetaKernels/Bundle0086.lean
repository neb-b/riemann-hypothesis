module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0077
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0084
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinNormSumInvariantRight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExtensionByZeroAtBaseIndex
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0049
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0064
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0078
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0085
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutTraceA
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0073

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousTransportFApplyK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
namespace GlobalTheory.WeilContF
open Formalism.IndefR.DatumF
theorem continuous_transportF_apply_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ z : κ → AF F, Continuous fun p => om p Φ z := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr
    Φ hΦ z
  have hstd := hω.std
  have hψ := hstd.1
  have hth : ∀ w, Continuous fun p => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) w := by
    intro w
    choose g h hh hg using fun p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) =>
      _root_.GlobalTheory.T.doubled_lagrangian_intertwiner F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB p.1 p.2
    have hθ : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
      ⟨_root_.GlobalTheory.T.doubled_lagrangian_continuous F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        _root_.GlobalTheory.T.doubled_lagrangian_unitary F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        _root_.GlobalTheory.T.doubled_lagrangian_equivariant F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        _root_.GlobalTheory.T.doubled_lagrangian_invariant_functional F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ⟩
    have hhU : ∀ p, matHomF σ JT (h p) = p.1.1 := fun p => Units.ext (hh p)
    have hgU : ∀ p, (matHomF σ JS (g p))⁻¹.1 = p.2.1.1ᵀ := by
      intro p
      apply Units.inv_eq_of_mul_eq_one_right
      change mtF σ JS (g p) * _ = 1
      rw [hg p, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one]
    have hcH' : Continuous fun p => matHomF σ JT (h p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JT (h p)) = fun p => p.1.1.1 := funext fun p => hh p
        rw [e]
        exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
      · have e : (fun p => (matHomF σ JT (h p))⁻¹.1) = fun p => (p.1.1)⁻¹.1 := funext fun p => by rw [hhU p]
        rw [e]
        exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)
    have hcG' : Continuous fun p => matHomF σ JS (g p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JS (g p)) = fun p => ((p.2.1)⁻¹).1ᵀ := funext fun p => hg p
        rw [e]
        exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
      · have e : (fun p => (matHomF σ JS (g p))⁻¹.1) = fun p => p.2.1.1ᵀ := funext hgU
        rw [e]
        exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
    have hcH : Continuous h := continuous_induced_rng.2 hcH'
    have hcG : Continuous g := continuous_induced_rng.2 hcG'
    have heq : ∀ p, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) w =
        ω (g p, h p) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) w := fun p =>
      congrFun (htr p.1 p.2 (g p) (h p) (hh p) (hg p) Φ hΦ).2 w
    exact ((hω.om_cont _ hθ w).comp (hcG.prodMk hcH)).congr fun p => (heq p).symm
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  obtain ⟨N, hN, m, g, y, hg, hy, hf⟩ :=
    _root_.GlobalTheory.T.weil_pair_commuting_actions F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr Φ hΦ p0
  let f : _ → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    fun p => if h : p ∈ N then Classical.choose (hf p h) else 0
  have hfe : ∀ p ∈ N, om p Φ = ∑ i, pureA F (f p i) (g i) := fun p hp => by
    simp only [f, dif_pos hp]
    exact Classical.choose_spec (hf p hp)
  have hslice : ∀ p ∈ N, ∀ i v, f p i v = om p Φ (GlobalTheory.WeilCont.adeleJoin F v (y i)) := by
    intro p hp i v
    rw [hfe p hp, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_pos rfl, mul_one]
    · intro j _ hji
      rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_neg hji, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C := by
    intro k
    choose C hC using fun i =>
      _root_.GlobalTheory.T.weil_pair_rational_invariance F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
        Φ hΦ (y i) p0 k 0
    refine ⟨∑ i, |C i|, ?_⟩
    filter_upwards [Filter.eventually_all.2 hC, hN] with p hp hpN i v
    have h1 := hp i v
    rw [norm_iteratedFDeriv_zero] at h1
    rw [hslice p hpN i v]
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨M, hM, hMb⟩ := GlobalTheory.SchwartzMajorant.exists_summable_majorant F κ (fun p => om p Φ) p0 m g f hg
    (Filter.eventually_of_mem hN fun p hp => hfe p hp) hbd z
  let e : (κ → F) → AddChar (κ → AF F) ℂ := fun a =>
    B.ψ.compAddMonoidHom (AddMonoidHom.mk' (fun y => (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y)
      (fun y y' => dotProduct_add _ y y'))
  have he : ∀ a y, e a y = B.ψ ((fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y) := fun a y => rfl
  have hform : ∀ p y', GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
      B.ψ (⅟(2 : AF F) * (z ⬝ᵥ y')) * ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
    intro p y'
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr,
      LinearEquiv.apply_symm_apply, he]
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    simp only [AddChar.map_add_eq_mul, Pi.add_def]
    ring
  have h0 : ∀ y, e 0 y = 1 := fun y => by
    rw [he]
    simp
  have hne : ∀ a : κ → F, a ≠ 0 → ∃ y, e a y ≠ 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    obtain ⟨x0, hx0⟩ := hψ.2.2.2
    refine ⟨Pi.single i (algebraMap F (AF F) (a i)⁻¹ * x0), ?_⟩
    rw [he, dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    exact hx0
  have hψinv : ∀ t : AF F, B.ψ (-t) * B.ψ t = 1 := fun t => by
    simpa using (AddChar.map_add_eq_mul B.ψ (-t) t).symm
  have hc : ∀ y', ContinuousAt (fun p => ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j)) p0 := by
    intro y'
    have h2 : ∀ p, B.ψ (-(⅟(2 : AF F) * (z ⬝ᵥ y'))) *
          GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
        ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
      intro p
      simp only [hform, ← mul_assoc, hψinv, one_mul]
    exact ((continuous_const.mul (hth _)).continuousAt).congr (Filter.Eventually.of_forall h2)
  have hL := GlobalTheory.continuousAt_charSeries_coef_zero e (fun a y => hψ.2.1 _) h0 hne _ p0 M hM hMb hc
  simpa using hL
end GlobalTheory.WeilContF
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
theorem uA_zero_k : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L 0 = 1 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k]
theorem uA_col_k (u : Fin L.n → AE F E) (j : Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u j L.i₀ = if j = L.i₀ then 1 else 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k),
    fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k).symm]
theorem uA_mul_aB_k (u : Fin L.n → AE F E) (δ : E) (a : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, add_mul, one_mul, Finset.sum_mul]
  rw [Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j) _, add_zero]
theorem aB_mul_D_k (u : Fin L.n → AE F E) (δ : E) (a : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u)ᵀ.map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.mul_apply, Matrix.single_apply, Matrix.map_apply, Matrix.transpose_apply]
  by_cases hi : L.i₀ = i
  · subst hi
    by_cases hj : j = L.i₀
    · subst hj; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_col_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_col_k, hj, Ne.symm hj]
  · simp [hi]
theorem aB_add_k (δ : E) (a a' : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ (a + a') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, add_smul, Matrix.single_add]
theorem sB_add_k (b b' : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L (b + b') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Pi.add_apply, map_add (f := _), mul_add, neg_add, Matrix.single_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => by abel
theorem index_cases_sum (r : Fin d.n ⊕ Fin d.n) : r = Sum.inl L.i₀ ∨ r = Sum.inr L.i₀ ∨ ∃ a, r = Sum.map L.em L.em a := by
  rcases r with i | i <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨k, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨Sum.inl k, rfl⟩)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨Sum.inr k, rfl⟩)
def padB_k (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  ∑ k, ∑ l, Matrix.single (L.em k) (L.em l) (β k l)
theorem pad_block_row_zero (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (j : Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k L β L.i₀ j = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k, Matrix.sum_apply, Matrix.single_apply, fun k => _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k]
theorem pad_block_column_zero (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i : Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k L β i L.i₀ = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k, Matrix.sum_apply, Matrix.single_apply, fun k => _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k]
theorem padB_em_k (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (k l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k L β (L.em k) (L.em l) = β k l := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k, Matrix.sum_apply, Matrix.single_apply, L.inj.eq_iff, ite_and, Finset.sum_ite_eq']
theorem mem_ratV_k {b : Fin L.n → AE F E} (hb : b ∈ L.ratV) : ∃ x : Fin L.n → E, b = GlobalTheory.ThK.incV F x := by
  let φ : (Fin L.n → E) →+ (Fin L.n → AE F E) :=
    AddMonoidHom.compLeft (inclR (F := F) (E := E) (AF F)).toAddMonoidHom (Fin L.n)
  have hle : L.ratV ≤ φ.range := (AddSubgroup.closure_le _).2 (by rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)
  obtain ⟨x, hx⟩ := hle hb
  exact ⟨x, hx.symm⟩
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem inFrame_uM'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ)) := by
  obtain ⟨a', ha⟩ := h.uM u
  rw [ha, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lr_of_k ha (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L u)]
theorem inFrame_jn_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (β : nA σ L.Y L.b) :
    inFrame d.b (L.j (nb' β)) = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_k L β.1) 0 1 := by
  have hin : ∀ a b, inFrame d.b (L.j (nb' β)) (Sum.map L.em L.em a) (Sum.map L.em L.em b) = inFrame L.b (nb' β) a b :=
    fun a b => congrFun (congrFun (L.j_in (nb' β)) a) b
  ext r c
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.index_cases_sum L r with rfl | rfl | ⟨a, rfl⟩
  · rw [(L.j_out _ _ (by simp) c).1]
    rcases c with c | c <;> simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pad_block_row_zero]
  · rw [(L.j_out _ _ (by simp) c).1]
    rcases c with c | c <;> simp [Matrix.one_apply]
  · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.index_cases_sum L c with rfl | rfl | ⟨b, rfl⟩
    · rw [(L.j_out _ _ (by simp) _).2]
      rcases a with a | a <;> simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k]
    · rw [(L.j_out _ _ (by simp) _).2]
      rcases a with a | a <;> simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pad_block_column_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k]
    · rw [hin, h.nb' β]
      rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_em_k, L.inj.eq_iff]
theorem frame_centre_block_form (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (a : AF F) :
    inFrame d.b (cM (0, a)) = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a) 0 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_zero_k, Matrix.transpose_one]
theorem sM_add_k (b b' : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (b + b') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b' := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_add_k]
  exact (kfour.nM_mul _ _).symm
theorem cM_split_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (a : AF F) : cM (u, a) = uM u * cM (0, a) := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_uM'_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, Matrix.fromBlocks_multiply]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_aB_k]
theorem cM_comm_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (a : AF F) : uM u * cM (0, a) = cM (0, a) * uM u := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_uM'_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_aB_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_mul_D_k]
theorem centre_additive (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (a a' : AF F) : cM (0, a + a') = cM (0, a) * cM (0, a') := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, Matrix.fromBlocks_multiply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_add_k]
  simp [add_comm]
theorem unipotent_commutes_centre (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (b : Fin L.n → AE F E) (a : AF F) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (0, a) = cM (0, a) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp [add_comm]
theorem nb_split_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (β : nA σ d.Y d.b) :
    nb β = L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β) * cM (0, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β)) := by
  have hc : β.1ᵀ = -((((R.ε : ℤ) : AE F E)) • β.1.map (cA σ)) := (kfour.mem_nA_iff (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d) R.hε β.1).1 β.2
  have hcij : ∀ i j, β.1 j i = -(((R.ε : ℤ) : AE F E) * cA σ (β.1 i j)) := fun i j => by
    have := congrFun (congrFun hc i) j
    simpa using this
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mul_k R
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_jn_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.frame_centre_block_form h, h.nb β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨k, rfl⟩ <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L j with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0i0_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_entry_embedded_row, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_emem_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pad_block_row_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pad_block_column_zero, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.padB_em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k,
      Matrix.single_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_eq_k, fun k => _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k,
      fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k).symm, and_self, and_false, false_and, if_true, if_false, add_zero, zero_add]
  · have hy : cA σ (β.1 L.i₀ L.i₀) = -(((R.ε : ℤ) : AE F E)) * β.1 L.i₀ L.i₀ := by
      have e := hcij L.i₀ L.i₀
      calc cA σ (β.1 L.i₀ L.i₀) = -(((R.ε : ℤ) : AE F E)) * -(((R.ε : ℤ) : AE F E) * cA σ (β.1 L.i₀ L.i₀)) := by
            rw [neg_mul_neg, ← mul_assoc, e2, one_mul]
        _ = _ := by rw [← e]
    exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eig_k h _ hy).symm
  · exact hcij _ _
theorem j_move_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) :
    ∃ (B : Fin L.n → AE F E) (A : AF F), ∀ b a, L.j (nb' β'') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (b + B) * cM (u, a + A) * L.j (nb' β'') :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_move'_k h u β''
theorem j_conj_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (γ' : G2 σ L.Y) :
    ∃ (Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E)))
      (Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F), Continuous Q ∧
      (∀ b u a, L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ') ∧
      (γ' ∈ rat2 σ L.Y → ∀ w, w ∈ (L.ratV.prod L.ratV : AddSubgroup _) ↔ Λ w ∈ (L.ratV.prod L.ratV : AddSubgroup _)) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_conj'_k h γ'
theorem heis_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F, Continuous (Function.uncurry Z) ∧
      (∀ u₀ b, u₀ ∈ L.ratV → b ∈ L.ratV → Z u₀ b ∈ (algebraMap F (AF F)).range) ∧
      ∀ u₀ a₀ b u a, cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u₀ + u, a₀ + a + Z u₀ b) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.heis'_k h
theorem section_unipotent_invariant (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    (b : Fin L.n → AE F E) (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * g)) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * g) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_unipotent_invariant_weyl h hf z b g
theorem sM_rat_k {b : Fin L.n → AE F E} (hb : b ∈ L.ratV) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b ∈ rat2 σ d.Y := by
  have hc (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] e) = (1 : AF F) ⊗ₜ[F] σ e
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  obtain ⟨x, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.mem_ratV_k L hb
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 1 (∑ j, (Matrix.single L.i₀ (L.em j) (x j) +
    Matrix.single (L.em j) L.i₀ (-(((R.ε : ℤ) : E) * σ (x j))))) 0 1) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k]
  ext r c
  rcases r with i | i <;> rcases c with j | j <;>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, incM, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), GlobalTheory.ThK.incV, hc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k, map_neg, map_mul,
      map_intCast]
theorem cM_rat_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {c : (Fin L.n → AE F E) × AF F} (hu : c.1 ∈ L.ratV)
    (ha : c.2 ∈ (algebraMap F (AF F)).range) : cM c ∈ rat2 σ d.Y := by
  have hc (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] e) = (1 : AF F) ⊗ₜ[F] σ e
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  obtain ⟨c1, c2⟩ := c
  obtain ⟨x, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.mem_ratV_k L hu
  obtain ⟨t, rfl⟩ := ha
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (x j))
    (Matrix.single L.i₀ L.i₀ (t • δ)) 0 ((1 + ∑ j, Matrix.single L.i₀ (L.em j) (-(x j)))ᵀ.map σ)) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h]
  ext r c
  rcases r with i | i <;> rcases c with j | j <;>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, incM, Matrix.map_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply,
      Matrix.transpose_apply, map_sum, apply_ite (inclR (F := F) (E := E) (AF F)), apply_ite (cA σ), apply_ite (⇑σ), GlobalTheory.ThK.incV,
      hc, map_neg, inclR_smul]
theorem eisenstein_term_left_invariant {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (r * g) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) g :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_term_right_invariant hf z hr hx g
theorem eisenstein_norm_sum_invariant {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {r : d.G} (hr : r ∈ rat2 σ d.Y)
    (hx : ∀ k, inFrame d.b r k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (g : d.G) : ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (r * g))‖ₑ =
      ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)‖ₑ :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisenstein_norm_sum_invariant_right hf z hr hx g
theorem fix_sM_k (b : Fin L.n → AE F E) (k) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k]
  rcases k with k | k <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.one_apply]
theorem fix_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) (k) :
    inFrame d.b (cM c) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h]
  rcases k with k | k <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_col_k, Matrix.one_apply]
theorem fix_nb_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (β : nA σ d.Y d.b) (k) :
    inFrame d.b (nb β) k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [h.nb β]
  rcases k with k | k <;> simp [Matrix.one_apply]
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.NormalizeK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem normalize_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w₁⁻¹ * (p * γ)) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.normalize_k h hγ hn
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutTrace
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem gauss_mul_integral_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hbij : Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x))
    (hF : Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume) (κ : ℂ)
    (hκ : ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, Fixes (opFF hc w) (latF F E nS nT Λ) f → IsVacF σ JS JT ξ₀ B.ψ ι s f → ∀ x,
      (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = κ * ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x)
    (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (ht : ∀ k, b * t k * a - t k ∈ Λ)
    (hu : ∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) :
    ∃ r : ℝ, 0 < r ∧ (∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k)) *
      ∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v = r * κ :=
  _root_.PositivityTheory.ThKW.Trc.gauss_mul_integral_A_k C hG hR hO hs ha hb hbij hF κ hκ n t ht hu
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelMultOfK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.RgEis.Hd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem siegelMult_of_k : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    _root_.SiegelEisensteinSeries.BRoad.SiegelMult_k := _root_.GlobalTheory.T.siegel_multiplicity_of_laws
theorem eisBL_k : _root_.GlobalTheory.ThK.Dbl.EisBL_k :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  _root_.SiegelEisensteinSeries.BRoad.eisBL_of_k _root_.GlobalTheory.T.eisenstein_half_plane_holds
    (_root_.PositivityTheory.RgEis.Hd.siegelMult_of_k secLaw hW dict dictInf hG grpTop bdetLaw extLaw hP
      (sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
        (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
        (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
          (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
          (convGrOf_of bdetLaw extLaw) (convU_of hP))))
    GlobalTheory.CompanionTheory.Entire.local_factorisation
end PositivityTheory.RgEis.Hd
end
end
end

